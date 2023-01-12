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

Implicit Type γpaid γdecided : gname.
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

Definition ThunkInv t γpaid γdecided nc R φ : iProp Σ :=

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
          ∗ ⌜ nc ≤ ac ⌝
        )
      )
.

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

Definition Thunk p N t n R φ : iProp Σ :=

  ∃ γpaid γdecided nc,
      meta t nroot (γpaid, γdecided)
    ∗ na_inv p N (ThunkInv t γpaid γdecided nc R φ)
    ∗ own γpaid (◯ MaxNat (nc - n))

.

(* The predicate [ThunkVal t v] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* This predicate is persistent. It means that the thunk t has been forced
   and that its value is v. *)

Definition ThunkVal t v : iProp Σ :=

  ∃ γpaid γdecided,
      meta t nroot (γpaid, γdecided)
    ∗ ownDecided γdecided v

.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about our ghost state. *)

Local Lemma decide γdecided v :
  ownUndecided γdecided ==∗ ownDecided γdecided v.
Proof.
  unfold ownUndecided, ownDecided.
  iIntros "Hγdecided".
  iApply (own_update _ _ _ with "Hγdecided").
  by apply cmra_update_exclusive.
Qed.

Local Lemma ownDecided_agree γdecided v1 v2 :
  ownDecided γdecided v1 -∗ ownDecided γdecided v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hag.
  iPureIntro.
  eapply to_agree_op_valid_L, (proj1 (Cinr_valid (A:=unitR) _)).
  by rewrite Cinr_op.
Qed.

Local Lemma decided_xor_undecided γdecided v :
  ownUndecided γdecided -∗ ownDecided γdecided v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hag.
  iPureIntro.
  auto.
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

(* The assertion [ThunkVal t v] is persistent and timeless. *)

Global Instance ThunkVal_persistent t v :
  Persistent (ThunkVal t v).
Proof. exact _. Qed.

Global Instance ThunkVal_timeless t v :
  Timeless (ThunkVal t v).
Proof. exact _. Qed.

(* A public lemma: once the value of a thunk has been decided, there is
   agreement on this value. This can be used to prove that if a thunk is
   forced twice, then both operations must return the same value. *)

Lemma ThunkVal_agree t v1 v2 :
  ThunkVal t v1 -∗ ThunkVal t v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as (γpaid1 γdecided1) "(Hmeta1 & Hown1)".
  iDestruct "H2" as (γpaid2 γdecided2) "(Hmeta2 & Hown2)".
  iDestruct (meta_agree with "[$][$]") as "%Heq".
  assert (γdecided1 = γdecided2) by congruence. subst. clear Heq.
  iApply (ownDecided_agree with "Hown1 Hown2").
Qed.

(* A public lemma: the conjunction of [Thunk p N t n R φ] and [ThunkVal t v]
   implies that the thunk [t] has zero debits, that is, [Thunk p N t 0 R φ]
   holds. This guarantees that this thunk can be forced for a constant cost. *)

Lemma Thunk_ThunkVal p N t n R φ v F E :
  ↑N ⊆ E →
  ↑N ⊆ F →
  Thunk p N t n R φ -∗ ThunkVal t v -∗ na_own p F
  ={E}=∗
  Thunk p N t 0 R φ ∗                  na_own p F.
Proof.
  iIntros (? ?) "#Hthunk #Hval Hp".
  iDestruct "Hthunk" as (γpaid1 γdecided1 nc) "(Hmeta1 & Hinv & Hγpaid◯)".
  iDestruct "Hval" as (γpaid2 γdecided2) "(Hmeta2 & Hdecided)".
  (* Exploit the agreement of the meta tokens. *)
  iDestruct (meta_agree with "Hmeta1 Hmeta2") as "%Heq".
  assert (γpaid1 = γpaid2) by congruence.
  assert (γdecided1 = γdecided2) by congruence.
  subst. clear Heq.
  iClear "Hmeta2". iRename "Hmeta1" into "Hmeta".
  rename γpaid2 into γpaid.
  rename γdecided2 into γdecided.

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hinv Hp")
    as ">(Hthunk & Hp & Hclose)";
    [done|done|]. (* side conditions about masks *)

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & [ Hunevaluated | Hevaluated ])".

  (* Case: the thunk is UNEVALUATED. This is impossible. *)
  {
    iDestruct "Hunevaluated" as (f) "(>Hundecided & _ & _ & _)".
    (* The ghost cell cannot be both decided and undecided. *)
    iDestruct (decided_xor_undecided with "Hundecided Hdecided")
      as "%contradiction".
    tauto.
  }

  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v') "(>#Hdecided' & >Ht & #Hv & >%Hncac)".
    (* The following two lines argue that v and v' are the same value.
       This is not necessary in this proof, but we do it for clarity. *)
    iDestruct (ownDecided_agree with "Hdecided Hdecided'") as "%Heq".
    subst v'. iClear "Hdecided'".
    (* We know that this thunk has been paid for: we have nc ≤ ac.
       We can create a ghost witness of this fact. This will allow
       us to argue that this thunk has zero debits. *)
    iClear "Hγpaid◯".
    iMod (auth_max_nat_update_read_auth with "Hγpaid●")
      as "(Hγpaid● & Hγpaid◯)".
    iPoseProof (own_auth_max_nat_weaken _ ac (nc - 0) with "Hγpaid◯")
      as "Hγpaid◯"; [ lia |].
    (* Close the invariant. *)
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists ac. iFrame "Hγpaid●". iRight.
      iExists v. iFrame "Hdecided Ht Hv". iPureIntro. assumption. }
    iModIntro.
    iExists γpaid, γdecided, nc.
    iFrame "Hmeta Hinv Hγpaid◯".
  }
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
  iDestruct (own_auth_max_nat_weaken with "Hγpaid◯") as "$".
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
   contains the namespace [↑N]. Because this token is unique and is not
   passed on to the function call f(), reentrancy is statically forbidden. *)

(* Forcing a thunk is permitted only if its apparent debt is zero, that is,
   only if the cost of forcing this thunk has already been paid for (perhaps
   in several increments) using [thunk_pay]. *)

(* Forcing a thunk has (amortized) constant time complexity. It requires 11$. *)

(* Forcing a thunk requires and preserves the resource [R]. *)

(* Forcing a thunk produces a witness that the value of the thunk has been
   decided and is [v]. *)

Lemma thunk_force_spec p N F t R φ :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t 0 R φ ∗ na_own p F ∗ R }}}
  «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}.
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
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { iModIntro. unfold ThunkVal. auto. }
    (* Subgoal: close the invariant. *)
    iApply "Hclose". iFrame "Hp". iNext.
    (* [ac] remains unchanged. We cannot make it zero, and we do not need to. *)
    iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v.
    iFrame "Hdecided Ht Hv".
    iPureIntro. assumption.
  }
  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v) "(>#Hdecided & >Ht & #Hv & >%Hncac)".
    wp_tick_load. wp_tick_match.
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { iModIntro. unfold ThunkVal. auto. }
    (* Subgoal: close the invariant. *)
    iApply "Hclose". iFrame "Hp". iNext.
    iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v.
    iFrame "Hdecided Ht Hv".
    iPureIntro. assumption.
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of the ghost operation [pay]. *)

(* Paying is a ghost operation: there is no HeapLang code for it. It is a
   ghost update. Its effect is to change the number of debits from [n] to
   [n-k], while consuming [k] time credits. *)

(* Like [force], paying requires a token of the form [na_own p F], where [F]
   contains the namespace [↑N]. *)

Lemma thunk_pay p N F E (n k : nat) t R φ :
  ↑N ⊆ F →
  ↑N ⊆ E →
  na_own p F -∗ Thunk p N t n R φ -∗
  TC k ={E}=∗
  na_own p F  ∗ Thunk p N t (n-k) R φ.
Proof.
  iIntros (? ?) "Hp #Hthunk Htc_k".
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
    iDestruct "Hevaluated" as (v) "(>#Hdecided & >Ht & #Hv & >%Hncac)".
    (* The ghost cell is incremented from [ac] to [ac + k] also in this case.
       However, in this case, no time credits are actually involved. The extra
       payment is wasted. *)
    iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγpaid● Hγpaid◯")
      as ">[Hγpaid●' #Hγpaid◯']";
      iClear "Hγpaid◯".
    iMod ("Hclose" with "[-Hγpaid◯']") as "$".
    { iFrame "Hp". iNext. iExists (ac+k)%nat.
      iFrame "Hγpaid●'".
      iRight. iExists v. iFrame "Hdecided Ht Hv".
      iPureIntro. lia. }
    iModIntro.
    iExists γpaid, γdecided, nc. iFrame "Hmeta Hthunkinv".
    iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγpaid◯'")
      as "$".
    lia.
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the combination of [pay] and [force]. *)

Lemma thunk_pay_force p N F t n R φ :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC (n + 11) ∗ Thunk p N t n R φ ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}.
Proof using.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & Hp & HR) Post".
  (* Split our credits. *)
  iDestruct "Hcredits" as "(Hn & Hcredits)".
  (* First, pay. *)
  iMod (thunk_pay with "Hp Hthunk Hn") as "(Hp & #Hpaid)"; [ done | done |].
  iClear "Hthunk". iRename "Hpaid" into "Hthunk".
  rewrite Nat.sub_diag. (* n - n = 0 *)
  (* Then, force the thunk. *)
  iApply (thunk_force_spec with "Htickinv [$Hcredits $Hthunk $Hp $HR]").
  { eauto. }
  (* Done. *)
  iApply "Post".
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the special case of [force] where the thunk has been
   forced already. *)

(* TODO In this case, the resource R is not needed. A proof would require
   duplicating the proof of [force], or (better) generalizing the spec of
   [force] to cover both cases? *)

Lemma thunk_force_forced p N F t n R φ v :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t n R φ ∗ ThunkVal t v ∗ na_own p F ∗ R }}}
  «force #t»
  {{{ RET «v» ; □ φ v ∗ na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & #Hval & Hp & HR) Post".
  (* Argue that this thunk has zero debits. *)
  iMod (Thunk_ThunkVal with "Hthunk Hval Hp") as "(Hthunk' & Hp)";
    [ done | done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  (* Force the thunk. *)
  iApply (thunk_force_spec with "Htickinv [$Hcredits $Hthunk $Hp $HR]");
    [ done |].
  iNext.
  iIntros (v') "(#Hv' & #Hval' & Hp & HR)".
  (* Argue that the two values must be the same. *)
  iPoseProof (ThunkVal_agree with "Hval Hval'") as "%". subst v'.
  (* Done. *)
  iApply "Post". auto with iFrame.
Qed.

End Proofs.
