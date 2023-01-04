From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.
From iris_time Require Import ThunksCode.

(* This file contains a simple formalization of thunks, as presented in the
   ESOP 2019 paper. A more elaborate formalization, which is based on the same
   HeapLang code but offers a richer logical API, can be found in Thunks.v. *)

(* -------------------------------------------------------------------------- *)

Section Proofs.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.

(* The parameters of the public predicate [Thunk p t n R φ] are:

    - p: a non-atomic-invariant pool name

    - N: a non-atomic-invariant namespace

    - t: the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - R: a resource that is required, but not consumed,
         when the thunk is forced

    - φ: the postcondition of this thunk is □φ

 *)

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp Σ.
Implicit Type φ : val → iProp Σ.

(* The following variables are used internally:

    - γpaid: a ghost cell, whose content inhabits the monoid Auth (Nat, max)

    - γdecided: a ghost cell, whose content is either Left () or Right v,
      indicating whether the thunk has been forced already;
      the left side is exclusive and represents a unique permission to force;
      the right side is persistent and represents agreement on the value v

    - nc: the necessary credits, that is, the credits that appear
          in the precondition of the function f

    - ac: the available credits, that is, the credits that have
          been paid so far and currently stored in the thunk

    - f: the function that is invoked when the thunk is forced

    - v: the result of calling f(), and of forcing the thunk

*)

Implicit Type γ : gname.
Implicit Type nc ac : nat.
Implicit Type f v : val.

(* The internal predicate [ThunkInv ...] is the thunk's invariant. *)

(* It states that
   + the ghost cell γpaid contains the authoritative value ac;
     that is, ac is the authoritative number of "available credits";
   + and
     - either the thunk is currently unevaluated,
       in which case we have a unique permission to call f,
       and this call requires nc time credits,
       and we currently have ac time credits at hand;
     - or the thunk is evaluated already,
       and its value v satisfies the postcondition □φ. *)

(* The postcondition □φ is persistent by construction. Indeed, a copy
   of the value [v] is returned to the caller and a copy of [v] is
   memoized for later use. Both copies must satisfy the postcondition,
   so the postcondition must be duplicable. *)

Definition ownUndecided γdecided :=
  own γdecided (Cinl $ Excl ()).

Definition ownDecided γdecided v :=
  own γdecided (Cinr $ to_agree v).

Definition ThunkInv t γpaid γdecided nc R φ : iProp Σ := (

  ∃ ac,
      own γpaid (● MaxNat ac)
    ∗ (
        (∃ (f : val),
            ownUndecided γdecided
          ∗ t ↦ UNEVALUATEDV « f »
          ∗ (R -∗ TC nc -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }})
          ∗ TC ac
        )
      ∨ (∃ (v : val),
            ownDecided γdecided v
          ∗ t ↦ EVALUATEDV « v »
          ∗ □ φ v
        )
      )
)%I.

(* The predicate [Thunk p N t n R φ] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* Its definition states that:

   + γpaid and γdecided are the ghost locations associated with this thunk;

   + the thunk's invariant holds; it is placed in a non-atomic invariant
     indexed by the pool p;

   + we have a fragmentary view of the ghost cell γpaid containing the value
     [nc - n].

   Because γpaid inhabits the monoid Auth (Nat, max), this fragmentary view
   is duplicable. Intuitively, this means that we know [nc - n ≤ ac], hence
   [nc ≤ ac + n]. That is, the credits that have been paid already, plus the
   credits that remain to be paid, are sufficient to cover the actual cost
   of invoking f. *)

Definition Thunk p N t n R φ : iProp Σ := (

  ∃ γpaid γdecided nc,
      meta t nroot (γpaid, γdecided)
    ∗ na_inv p N (ThunkInv t γpaid γdecided nc R φ)
    ∗ own γpaid (◯ MaxNat (nc - n))

)%I.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about ghost state transitions. *)

Local Lemma decide γdecided v :
  ownUndecided γdecided ==∗ ownDecided γdecided v.
Proof.
  unfold ownUndecided, ownDecided.
  iIntros "Hγdecided".
  iApply (own_update _ _ _ with "Hγdecided").
  by apply cmra_update_exclusive.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the assertion [Thunk p N t n R φ] is persistent. This means
   that a thunk can be shared. In combination with [thunk_weakening] and
   [thunk_pay], this implies that several different views of a thunk, with
   distinct numbers of debits, can co-exist. *)

Global Instance thunk_persistent p N t n R φ :
  Persistent (Thunk p N t n R φ).
Proof using.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the number of debits [n] that appears in the assertion
   [Thunk p N t n R φ] is in general an over-approximation of the true
   remaining debt. Therefore, losing information, by replacing [n₁] with a
   larger number [n₂], is permitted. *)

Lemma thunk_weakening p N t n₁ n₂ R φ :
  (n₁ ≤ n₂)%nat →
  Thunk p N t n₁ R φ -∗
  Thunk p N t n₂ R φ.
Proof.
  iIntros (?) "Hthunk".
  iDestruct "Hthunk" as (γpaid γdecided nc) "(Hmeta & Hinv & Hγpaid◯)".
  iExists γpaid, γdecided, nc. iFrame "Hmeta Hinv".
  iDestruct (own_auth_max_nat_weaken _ (nc-n₁) (nc-n₂) with "Hγpaid◯") as "$".
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [create]. *)

(* In short, [create] requires
   + 3 time credits;
   + a permission to call f(), at most once,
     with precondition nc$ and postcondition φ.

   [create] returns a thunk [t] whose number of debits is [nc]
                            and whose postcondition is [φ].

   The pool [p] is arbitrarily chosen by the user. *)

Lemma thunk_create_spec p N nc R φ f :
  TC_invariant -∗
  {{{
      TC 3 ∗
      ( R -∗ TC nc -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }} )
  }}}
  «create f»
  {{{ (t : loc), RET #t ; Thunk p N t nc R φ }}}.
Proof.
  iIntros "#Htickinv" (Φ) "!# [? Hf] Post".
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● Hγpaid◯]".
  iMod (own_alloc (Cinl $ Excl ())) as (γdecided) "?"; first done.
  iApply wp_fupd.
  wp_tick_lam. wp_tick_inj. wp_tick.
  wp_alloc_with_meta t as "Ht" "Hmeta".
  iMod (meta_set _ t _ nroot with "[$]") as "#Hmeta". { set_solver. }
  iApply "Post".
  iExists γpaid, γdecided, nc ; rewrite (_ : nc - nc = 0)%nat ; last lia.
  iFrame "Hmeta Hγpaid◯".
  iApply na_inv_alloc.
  iNext.
  (* The number of available credits is initially 0. *)
  iExists 0%nat.
  auto with iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [force]. *)

(* Forcing a thunk [t] requires a token of the form [na_own p F], where [F]
   contains the namespace [thunkN t]. Because this token is unique and is not
   passed on to the function call f(), reentrancy is statically forbidden. *)

(* Forcing a thunk is permitted only if its apparent debt is zero, that is,
   only if the cost of forcing this thunk has already been paid for (perhaps
   in several increments) using [thunk_pay]. *)

(* Forcing a thunk has (amortized) constant time complexity. It requires 11$. *)

(* Forcing a thunk requires and preserves the resource [R]. *)

Lemma thunk_force_spec p N F t R φ :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t 0 R φ ∗ na_own p F ∗ R }}}
  «force #t»
  {{{ v, RET «v» ; □ φ v ∗ na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & Hp & HR) Post".
  iDestruct "Hthunk" as (γpaid γdecided nc) "#(Hmeta & Hthunkinv & Hγpaid◯)".
  rewrite (_ : nc - 0 = nc)%nat ; last lia.
  iApply wp_fupd.
  wp_tick_lam.

  (* Open the invariant before reading and possibly writing the reference. *)
  iDestruct (na_inv_acc with "Hthunkinv Hp")
    as ">(Hthunk & Hp & Hclose)";
    [done|done|]. (* side conditions about masks *)

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & [ Hunevaluated | Hevaluated ])".
  (* Case: the thunk is UNEVALUATED. *)
  {
    iDestruct "Hunevaluated" as (f) "(>Hundecided & >Ht & Hf & >Htc)".
    wp_tick_load. wp_tick_match.
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    iDestruct (own_auth_max_nat_le with "Hγpaid● Hγpaid◯") as %I.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ I with "Htc") as "Htc".
    (* We can invoke f(), *)
    wp_apply ("Hf" with "HR Htc") ; iIntros (v) "HR #Hv".
    (* and update the reference. *)
    wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
    (* Update the ghost state to remember that the value has been computed. *)
    iMod (decide with "Hundecided") as "#Hdecided".
    (* We must now close the invariant. *)
    iApply "Post".
    iFrame "Hv HR".
    iApply "Hclose". iFrame "Hp". iNext.
    (* [ac] remains unchanged. We cannot make it zero, and we do not need to. *)
    iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v.
    iFrame "Hdecided Ht Hv".
  }
  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v) "(>#Hdecided & >Ht & #Hv)".
    wp_tick_load. wp_tick_match.
    (* Close the invariant. *)
    iApply "Post".
    iFrame "Hv HR".
    iApply "Hclose". iFrame "Hp". iNext.
    iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v.
    iFrame "Hdecided Ht Hv".
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of the ghost operation [pay]. *)

(* Paying is a ghost operation: there is no HeapLang code for it. It is a
   ghost update. Its effect is to change the number of debits from [n] to
   [n-k], while consuming [k] time credits. *)

(* Like [force], paying requires a token of the form [na_own p F], where [F]
   contains the namespace [thunkN t]. *)

Lemma thunk_pay p N F (n k : nat) t R φ :
  ↑N ⊆ F →
  na_own p F -∗ Thunk p N t n R φ -∗
  TC k ={⊤}=∗
  na_own p F  ∗ Thunk p N t (n-k) R φ.
Proof.
  iIntros (?) "Hp #Hthunk Htc_k".
  iDestruct "Hthunk" as (γpaid γdecided nc) "#(Hmeta & Hthunkinv & Hγpaid◯)".

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hthunkinv Hp")
    as ">(Hthunk & Hp & Hclose)";
    [done|done|]. (* side conditions about masks *)

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & [ Hunevaluated | Hevaluated ])".

  (* Case: the thunk is UNEVALUATED. *)
  {
    iDestruct "Hunevaluated" as (f) "(>Hundecided & >Ht & Hf & >Htc)".
    (* We have [ac + k] time credits. *)
    iAssert (TC (ac + k)) with "[Htc Htc_k]" as "Htc" ;
      first by iSplitL "Htc".
    (* Increment the number of available credits from [ac] to [ac + k]. *)
    iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγpaid● Hγpaid◯")
      as ">[Hγpaid●' #Hγpaid◯']";
      iClear "Hγpaid◯".
    (* The invariant can be closed. *)
    iMod ("Hclose" with "[-Hγpaid◯']") as "$".
    { iFrame "Hp". iNext. iExists (ac+k)%nat. auto with iFrame. }
    iModIntro.
    iExists γpaid, γdecided, nc. iFrame "Hmeta Hthunkinv".
    (* And our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [Thunk] assertion. *)
    iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγpaid◯'")
      as "$".
    lia.
  }
  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v) "(>#Hdecided & >Ht & Hv)".
    (* The ghost cell is incremented from [ac] to [ac + k] also in this case.
       However, in this case, no time credits are actually involved. *)
    iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγpaid● Hγpaid◯")
      as ">[Hγpaid●' #Hγpaid◯']";
      iClear "Hγpaid◯".
    iMod ("Hclose" with "[-Hγpaid◯']") as "$".
    { iFrame "Hp". iNext. iExists (ac+k)%nat. auto with iFrame. }
    iModIntro.
    iExists γpaid, γdecided, nc. iFrame "Hmeta Hthunkinv".
    iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγpaid◯'")
      as "$".
    lia.
  }
Qed.

End Proofs.
