From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode.

Section API.

Context `{timeCreditHeapG Σ}.
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

(* TODO abstract away p *)
(* TODO abstract away the namespace token *)

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
Implicit Type R : iProp.
Implicit Type φ : val → iProp.

(* We write v for a value. *)

Implicit Type v : val.

Class BasicThunkAPI

  (* The Thunk predicate takes the form [Thunk p N t n R φ]. *)

  (
  Thunk :
    na_inv_pool_name →
    namespace →
    loc →
    nat →
    iProp →
    (val → iProp) →
    iProp
  )

  (* The ThunkVal predicate takes the form [ThunkVal t v]. *)

  (
  ThunkVal :
    loc →
    val →
    iProp
  )

  (* Thunk must be persistent. *)

  `{
    ∀ p N t n R φ,
    Persistent (Thunk p N t n R φ)
  }

  (* ThunkVal must be persistent and timeless. *)

  `{
    ∀ t v,
    Persistent (ThunkVal t v)
  }

  `{
    ∀ t v,
    Timeless (ThunkVal t v)
  }

:= {

  (* In [ThunkVal t v], [t] determines [v]. That is, a thunk has at most
     one value. Once its value has been decided, it becomes fixed forever. *)

  confront_thunkval_thunkval t v1 v2 :
    ThunkVal t v1 -∗ ThunkVal t v2 -∗ ⌜v1 = v2⌝
  ;

  (* The conjunction of [Thunk p N t n R φ] and [ThunkVal t v] implies that
     the thunk [t] has zero debits, that is, [Thunk p N t 0 R φ] holds. This
     guarantees that this thunk can be forced for a constant cost. *)

  confront_thunk_thunkval p N t n R φ v E F :
    ↑N ⊆ E →
    ↑N ⊆ F →
    Thunk p N t n R φ -∗ ThunkVal t v -∗ na_own p F
      ={E}=∗
    Thunk p N t 0 R φ ∗                  na_own p F
  ;

  (* The predicate [Thunk p N t n R φ] must be covariant in the parameter [n],
     which represents the debt (that is, the number of debits) associated with
     this thunk. Therefore, the parameter [n] represents an over-approximation
     of the true remaining debt. *)

  thunk_increase_debt p N t n₁ n₂ R φ :
    n₁ ≤ n₂ →
    Thunk p N t n₁ R φ -∗
    Thunk p N t n₂ R φ
  ;

  (* The creation of a thunk is *not* part of this basic API. *)

  (* The specification of [force] is as follows. *)

  (* Forcing a thunk is permitted only if its apparent debt is zero, that is,
     only if the cost of forcing this thunk has already been paid for (perhaps
     in several increments) using [thunk_pay]. *)

  (* Forcing a thunk [t] requires a token of the form [na_own p F]
     where [F] contains [↑N]. *)

  (* Forcing a thunk has (amortized) constant time complexity. It requires 11
     time credits. *)

  (* Forcing a thunk requires and preserves the resource [R]. *)

  (* Forcing a thunk produces a witness that the value of the thunk has been
     decided and is [v]. *)

  thunk_force p N t R φ F :
    ↑N ⊆ F →
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p N t 0 R φ ∗ na_own p F ∗ R }}}
      «force #t»
    {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}
  ;

  (* The ghost operation [pay] allows paying for (part of) the cost of a
     thunk. A thunk must be fully paid for before it can be forced. *)

  (* Paying is a ghost operation. Its effect is to change the number of debits
     from [n] to [n - k], while consuming [k] time credits. *)

  (* Like [force], paying requires the token [na_own p F]. *)

  thunk_pay p N n k t R φ E F :
    ↑N ⊆ E →
    ↑N ⊆ F →
    na_own p F -∗ Thunk p N t n R φ -∗ TC k
      ={E}=∗
    na_own p F  ∗ Thunk p N t (n-k) R φ
  ;

}.

End API.

(* -------------------------------------------------------------------------- *)

(* We now establish some laws that are consequences of the above laws. *)

Section Consequences.

Context `{BasicThunkAPI}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)

(* The combination of [pay] and [force]. *)

Lemma thunk_pay_force p N t n R φ F :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC (n + 11) ∗ Thunk p N t n R φ ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}.
Proof.
  intros hop.
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & Hp & HR) Post".
  (* Split our credits. *)
  iDestruct "Hcredits" as "(Hn & Hcredits)".
  (* First, pay. *)
  iMod (thunk_pay with "Hp Hthunk Hn") as "(Hp & #Hpaid)"; [ done | done |].
  iClear "Hthunk". iRename "Hpaid" into "Hthunk".
  rewrite Nat.sub_diag. (* n - n = 0 *)
  (* Then, force the thunk. *)
  iApply (thunk_force with "Htickinv [$Hcredits $Hthunk $Hp $HR]"); [ done |].
  (* Done. *)
  iApply "Post".
Qed.

(* -------------------------------------------------------------------------- *)

(* The special case of [force] where the thunk has been forced already. *)

(* In this case, the resource [R] is not needed, so a stronger specification
   could be given. Its proof would require duplicating the proof of [force],
   or (better) generalizing the spec of [force] to cover both cases. We do
   not do so because we have no use for this stronger specification. Indeed,
   the construction that we have in mind (ThunksStep.v) does not need it and
   does not preserve it. Forcing a ghost proxy thunk can require [R], even
   if the underlying physical thunk has been forced already, because we
   allow the ghost update to use [R]. *)

Lemma thunk_force_forced p N t n R φ v F :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t n R φ ∗ ThunkVal t v ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ RET «v» ; □ φ v ∗ na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & #Hval & Hp & HR) Post".
  (* Argue that this thunk has zero debits. *)
  iMod (confront_thunk_thunkval with "Hthunk Hval Hp") as "(Hthunk' & Hp)";
    [ done | done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  (* Force the thunk. *)
  iApply (thunk_force with "Htickinv [$Hcredits $Hthunk $Hp $HR]"); [ done |].
  iNext.
  iIntros (v') "(#Hv' & #Hval' & Hp & HR)".
  (* Argue that the two values must be the same. *)
  iPoseProof (confront_thunkval_thunkval with "Hval Hval'") as "%". subst v'.
  (* Done. *)
  iApply "Post". auto with iFrame.
Qed.

End Consequences.
