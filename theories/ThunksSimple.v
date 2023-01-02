From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(* This file contains a simple formalization of thunks, as presented in the
   ESOP 2019 paper. A more elaborate formalization, which is based on the same
   HeapLang code but offers a richer logical API, can be found in Thunks.v. *)

(* -------------------------------------------------------------------------- *)

(* Notations that make the HeapLang code more readable. *)

Notation UNEVALUATED f := (InjL f%V) (only parsing).
Notation EVALUATED v := (InjR v%V) (only parsing).
Notation UNEVALUATEDV f := (InjLV f%V) (only parsing).
Notation EVALUATEDV v := (InjRV v%V) (only parsing).
Notation "'match:' e0 'with' 'UNEVALUATED' x1 => e1 | 'EVALUATED' x2 => e2 'end'" :=
  (Match e0 x1%bind e1 x2%bind e2)
  (e0, e1, x2, e2 at level 200, only parsing) : expr_scope.

(* -------------------------------------------------------------------------- *)

(* The HeapLang code. *)

(* There are only two operations on thunks: [create] and [force]. *)

(* A thunk is either white (unevaluated) or black (evaluated). There is no
   grey color (which would mean that a thunk is currently being evaluated) and
   there is no runtime check against reentrancy. Yet, reentrancy is dangerous:
   we wish to guarantee that the function [f] is invoked at most once, but a
   reentrant call to [force] could violate this property. Thus, reentrancy
   must be statically ruled out by the specification of thunks. *)

Definition create : val :=
  λ: "f",
    ref (UNEVALUATED "f").

Definition force : val :=
  λ: "t",
    match: ! "t" with
      UNEVALUATED "f" =>
        let: "v" := "f" #() in
        "t" <- (EVALUATED "v") ;;
        "v"
    | EVALUATED "v" =>
        "v"
    end.

(* -------------------------------------------------------------------------- *)

Section Proofs.

Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.
Context `{na_invG Σ}.

(* The parameters of the public predicate [Thunk p t n φ] are:

    - p: a non-atomic-invariant pool name

    - t: the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - φ: the postcondition of this thunk;
         must be duplicable *)

Implicit Type p : na_inv_pool_name.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type φ : val → iProp Σ.

(* The following variables are used internally:

    - γ: the ghost location associated with this thunk

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

(* With each thunk [t], we associate a namespace [thunkN t]. This namespace
   appears in the public specification of [force]. It is abstract: its
   definition is not meant to be exposed to the user. *)

Definition thunkN t : namespace :=
  nroot .@ "thunk" .@ string_of_pos t.

(* The internal predicate [ThunkInv t γ nc φ] is the thunk's invariant. *)

(* It states that
   + the ghost cell γ, which inhabits the monoid Auth (Nat, max),
     contains the value ac -- that is, ac is the authoritative
     number of "available credits";
   + and
     - either the thunk is currently unevaluated,
       in which case we have a unique permission to call f,
       and this call requires nc time credits,
       and we currently have ac time credits at hand;
     - or the thunk is evaluated already,
       and its value v satisfies the postcondition φ. *)

Definition ThunkInv t γ nc φ : iProp Σ := (

  ∃ (ac : nat),
      own γ (● MaxNat ac)
    ∗ (
        (∃ (f : val),
            t ↦ UNEVALUATEDV « f »
          ∗ {{{ TC nc }}} « f #() » {{{ v, RET « v » ; φ v }}}
          ∗ TC ac
        )
      ∨ (∃ (v : val),
            t ↦ EVALUATEDV « v »
          ∗ φ v
        )
      )
)%I.

(* The predicate [Thunk p t n φ] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* Its definition states that:

   + the thunk's invariant holds;
     it is placed in a non-atomic invariant indexed by the pool p;

   + we have a fragmentary view of the ghost cell γ containing the value [nc - n].

   Because γ inhabits the monoid Auth (Nat, max), this fragmentary view is
   duplicable. Intuitively, this means that we know [nc - n ≤ ac], hence
   [nc ≤ ac + n]. That is, the credits that have been paid already, plus
   the credits that remain to be paid, are sufficient to cover the actual
   cost of invoking f. *)

Definition Thunk p t n φ : iProp Σ := (

  ∃ (γ : gname) (nc : nat),
      na_inv p (thunkN t) (ThunkInv t γ nc φ)
    ∗ own γ (◯ MaxNat (nc - n))

)%I.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the assertion [Thunk p t n φ] is persistent. This means
   that a thunk can be shared. In combination with [thunk_weakening] and
   [thunk_pay], this implies that several different views of a thunk, with
   distinct numbers of debits, can co-exist. *)

Global Instance thunk_persistent p t n φ :
  Persistent (Thunk p t n φ).
Proof using.
  exact _.
Qe.d

(* -------------------------------------------------------------------------- *)

(* The number of debits can be over-estimated. *)
Lemma thunk_weakening p t n₁ n₂ φ :
  (n₁ ≤ n₂)%nat →
  Thunk p t n₁ φ -∗
  Thunk p t n₂ φ.
Proof.
  iIntros (I) "H". iDestruct "H" as (γ nc) "[Hinv Hγ◯]".
  iExists γ, nc. iFrame "Hinv".
  iDestruct (own_auth_max_nat_weaken _ (nc-n₁) (nc-n₂) with "Hγ◯") as "$". lia.
Qed.

Lemma thunk_create_spec p nc φ f :
  TC_invariant -∗
  {{{ TC 3 ∗ ( {{{ TC nc }}} «f #()» {{{ v, RET « v » ; φ v }}} ) }}}
  «create f»
  {{{ (t : loc), RET #t ; Thunk p t nc φ }}}.
Proof.
  iIntros "#Htickinv" (Φ) "!# [? Hf] Post".
  iMod (auth_max_nat_alloc 0) as (γ) "[Hγ● Hγ◯]".
  iApply wp_fupd.
  wp_tick_lam. wp_tick_inj. wp_tick_alloc t.
  iApply "Post".
  iExists γ, nc ; rewrite (_ : nc - nc = 0)%nat ; last lia.
  iFrame "Hγ◯".
  iApply na_inv_alloc.
  iNext. iExists 0%nat. auto with iFrame.
Qed.

Lemma thunk_force_spec p F t φ :
  ↑(thunkN t) ⊆ F →
  (∀ (v : val), φ v -∗ φ v ∗ φ v) →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p t 0 φ ∗ na_own p F }}}
  «force #t»
  {{{ v, RET «v» ; φ v ∗ na_own p F }}}.
Proof.
  iIntros (? Hφdup).
  iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & Hp) Post".
  iDestruct "Hthunk" as (γ nc) "#[Hthunkinv Hγ◯]".
  rewrite (_ : nc - 0 = nc)%nat ; last lia.
  iApply wp_fupd.
  wp_tick_lam.
  (* reading the thunk… *)
  iDestruct (na_inv_acc p ⊤ F (thunkN t) with "Hthunkinv Hp")
    as ">(Hthunk & Hp & Hclose)" ; [done|done|] ;
    iDestruct "Hthunk" as (ac) "(>Hγ● & [ Hunevaluated | Hevaluated ])" ;
    [ iDestruct "Hunevaluated" as (f) "(>Ht & Hf & >Htc)"
    | iDestruct "Hevaluated" as (v) "(>Ht & Hv)" ].
  (* (1) if it is UNEVALUATED, we evaluate it: *)
  {
    wp_tick_load. wp_tick_match.
    iDestruct (own_auth_max_nat_le with "Hγ● Hγ◯") as %I.
    iDestruct (TC_weaken _ _ I with "Htc") as "Htc".
    wp_apply ("Hf" with "Htc") ; iIntros (v) "Hv".
    wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
    iApply "Post".
    iDestruct (Hφdup with "Hv") as "[Hv $]".
    iApply "Hclose". iFrame "Hp".
    iNext. iExists ac. auto with iFrame.
  }
  (* (2) if it is EVALUATED, we get the result which is already memoized: *)
  {
    wp_tick_load. wp_tick_match.
    iApply "Post".
    iDestruct (Hφdup with "Hv") as "[Hv $]".
    iApply "Hclose". iFrame "Hp".
    iNext. iExists ac. auto with iFrame.
  }
Qed.

Lemma thunk_pay p F (n k : nat) t φ :
  ↑(thunkN t) ⊆ F →
  na_own p F -∗ Thunk p t n φ -∗ TC k ={⊤}=∗ Thunk p t (n-k) φ ∗ na_own p F.
Proof.
  iIntros (?) "Hp #Hthunk Htc_k".
  iDestruct "Hthunk" as (γ nc) "#[Hthunkinv Hγ◯]".
  (* reading the thunk… *)
  iDestruct (na_inv_acc p ⊤ F (thunkN t) with "Hthunkinv Hp")
    as ">(Hthunk & Hp & Hclose)" ; [done|done|] ;
    iDestruct "Hthunk" as (ac) "(>Hγ● & [ Hunevaluated | Hevaluated ])" ;
    [ iDestruct "Hunevaluated" as (f) "(>Ht & Hf & >Htc)"
    | iDestruct "Hevaluated" as (v) "(>Ht & Hv)" ].
  (* (1) if it is UNEVALUATED, then we add the time credits to the deposit: *)
  {
    iAssert (TC (ac + k)) with "[Htc Htc_k]" as "Htc" ;
      first by iSplitL "Htc".
    iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγ● Hγ◯") as ">[Hγ●' #Hγ◯']" ;
      iClear "Hγ◯".
    iMod ("Hclose" with "[-Hγ◯']") as "$". {
      iFrame "Hp".
      iNext. iExists (ac+k)%nat. auto with iFrame.
    }
    iModIntro.
    iExists γ, nc. iFrame "Hthunkinv".
    iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγ◯'") as "$" ; lia.
  }
  (* (2) if it is EVALUATED, then we do nothing: *)
  {
    iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγ● Hγ◯") as ">[Hγ●' #Hγ◯']" ;
      iClear "Hγ◯".
    iMod ("Hclose" with "[-Hγ◯']") as "$". {
      iFrame "Hp".
      iNext. iExists (ac+k)%nat. auto with iFrame.
    }
    iModIntro.
    iExists γ, nc. iFrame "Hthunkinv".
    iDestruct (own_auth_max_nat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγ◯'") as "$" ; lia.
  }
Qed.

End Proofs.
