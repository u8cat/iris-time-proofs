From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode.

(* We write [ThunkToken p F] as a synonym for [na_own p F]. *)

Notation ThunkToken := na_own.

Section API.

Context `{timeCreditHeapG Σ}.
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

(* The parameters of the public predicate [Thunk p F t n R φ] are:

    - p: a non-atomic-invariant pool

    - F: a mask

    - t: the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - R: a resource that is required, but not consumed,
         when the thunk is forced

    - φ: the postcondition of this thunk is □φ

 *)

Implicit Type p : na_inv_pool_name.
Implicit Type F : coPset.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.

(* We write v for a value. *)

Implicit Type v : val.

(* The basic thunk API. *)

Class BasicThunkAPI

  (* The Thunk predicate takes the form [Thunk p F t n R φ]. *)

  (
  Thunk :
    na_inv_pool_name →
    coPset →
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

  (* [Thunk] must be persistent. This means that a thunk can be shared. In
    combination with [thunk_increase_debt] and [thunk_pay], this implies that
    several different views of a thunk, with distinct numbers of debits, can
    co-exist. *)

  `{
    ∀ p F t n R φ,
    Persistent (Thunk p F t n R φ)
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

  (* The predicate [Thunk F t n R φ] must be covariant in the parameter [n],
     which represents the debt (that is, the number of debits) associated with
     this thunk. Therefore, the parameter [n] represents an over-approximation
     of the true remaining debt. *)

  thunk_increase_debt p F t n1 n2 R φ :
    n1 ≤ n2 →
    Thunk p F t n1 R φ -∗
    Thunk p F t n2 R φ
  ;

  (* The creation of a thunk is *not* part of this basic API. *)

  (* The specification of [force] is as follows. *)

  (* Forcing a thunk is permitted only if its apparent debt is zero, that is,
     only if the cost of forcing this thunk has already been paid for (perhaps
     in several increments) using [thunk_pay]. *)

  (* Forcing a thunk [t] requires a token of the form [ThunkToken p F']
     where [F'] contains [F]. *)

  (* Forcing a thunk has (amortized) constant time complexity. It requires 11
     time credits. *)

  (* Forcing a thunk requires and preserves the resource [R]. *)

  (* Forcing a thunk produces a witness that the value of the thunk has been
     decided and is [v]. *)

  thunk_force p F t R φ F' :
    F ⊆ F' →
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p F t 0 R φ ∗ ThunkToken p F' ∗ R }}}
      «force #t»
    {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}
  ;

  (* Forcing a thunk that has already been forced requires 11 time credits,
     regardless of the apparent debt associated with this thunk. *)

  (* The value that is returned must be the value [v] predicted by the
     assertion [ThunkVal t v]. *)

  (* This specification is weak: it does not guarantee [□ φ v]. *)

  (* One could remark that, in this case, forcing does not require [R].
     However, we do not need this stronger result, and establishing it
     would require some duplication of proofs, so we do not offer this
     guarantee. *)

  thunk_force_forced_weak p F t n R φ v F' :
    F ⊆ F' →
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p F t n R φ ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}
      «force #t»
    {{{ RET «v» ; ThunkToken p F' ∗ R }}}
  ;

  (* The ghost operation [pay] allows paying for (part of) the cost of a
     thunk. A thunk must be fully paid for before it can be forced. *)

  (* Paying is a ghost operation. Its effect is to change the number of debits
     from [n] to [n - k], while consuming [k] time credits. *)

  (* Like [force], paying requires the token [ThunkToken p F']. *)

  thunk_pay p F n k t R φ E F' :
    F ⊆ E →
    F ⊆ F' →
    ThunkToken p F' -∗ Thunk p F t n R φ -∗ TC k
      ={E}=∗
    ThunkToken p F'  ∗ Thunk p F t (n-k) R φ
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

Lemma thunk_pay_force p F t n R φ F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC (n + 11) ∗ Thunk p F t n R φ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
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

End Consequences.
