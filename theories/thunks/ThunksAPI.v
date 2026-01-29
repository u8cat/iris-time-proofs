From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase.

(* The construction of the predicate [Thunk] is in three layers: base thunks,
   proxy thunks, and thunks. These layers are described in the files
   ThunksBase.v, ThunksStep.v, and ThunksFull.v. *)

(* This file defines an API (that is, a set of reasoning rules) that are
   common to all three layers. This API is used in the construction as
   follows:

   + in the beginning, we prove that the predicate [BaseThunk] satisfies this
     API; in addition, it has a creation rule;

   + then, we prove that if we are given a predicate [Thunk] that satisfies
     this API, then on top of it, we are able to define a predicate
     [ProxyThunk] that also satisfies this API; in addition, it has a form of
     the consequence rule, which constructs a [ProxyThunk] out of a [Thunk];

   + finally, by iterating this construction an arbitrary number of times, we
     build the predicate [Thunk], which satisfies this API and has both the
     creation rule and the consequence rule. *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section API.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* needed by ThunkVal *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Notation iPropO := (iPropO Σ).
Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)

(* The parameters of the public predicate [Thunk p F t n R φ] are:

    - p, F: a non-atomic-invariant pool and a mask; the token
            [ThunkToken p F] is required to force this thunk

    - t: a memory location; the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - R: a resource that is required, but not consumed,
         when the thunk is forced

    - φ: a postcondition; the value v produced by forcing this thunk
         satisfies [□ φ v].

 *)

Implicit Type p : na_inv_pool_name.
Implicit Type F : coPset.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.

(* We write v for a value. *)

Implicit Type v : val.

(* -------------------------------------------------------------------------- *)

(* The common thunk API. *)

Class CommonThunkAPI

  (* The Thunk predicate takes the form [Thunk p F t n R φ]. *)

  (
  Thunk :
    na_inv_pool_name →
    coPset →
    loc →
    nat →
    iProp →
    (val → iPropO) →
    iProp
  )

:= {

  #[global] thunk_persistent p F t n R φ :: Persistent (Thunk p F t n R φ);

  #[global] thunk_proper p F t n ::
    Proper ((≡) ==> pointwise_relation _ (≡) ==> (≡)) (Thunk p F t n);
  #[global] thunk_ne m p F t n ::
    Proper ((dist m) ==> pointwise_relation _ (dist m) ==> (dist m)) (Thunk p F t n);
  #[global] thunk_contractive m p F t n ::
    Proper ((dist_later m) ==> pointwise_relation _ (dist_later m) ==> (dist m)) (Thunk p F t n);

 (* The predicate [Thunk F t n R φ] must be covariant in the parameter [F],
    which is the mask used for forcing. *)
  thunk_mask_subseteq p F1 F2 t n R φ :
    F1 ⊆ F2 → Thunk p F1 t n R φ -∗ Thunk p F2 t n R φ;

  (* The predicate [Thunk F t n R φ] must be covariant in the parameter [n],
     which represents the debt (that is, the number of debits) associated with
     this thunk. Therefore, the parameter [n] represents an over-approximation
     of the true remaining debt. *)

  thunk_increase_debt p F t n1 n2 R φ :
    n1 ≤ n2 →
    Thunk p F t n1 R φ -∗
    Thunk p F t n2 R φ
  ;

  (* The creation of a thunk is *not* part of this API. *)

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
    {{{ TC Tf ∗ Thunk p F t 0 R φ ∗ ThunkToken p F' ∗ R }}}
      «force #t»
    {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}
  ;

  (* The ghost operation [pay] allows paying for (part of) the cost of a
     thunk. A thunk must be fully paid for before it can be forced. *)

  (* Paying is a ghost operation. Its effect is to change the number of debits
     from [n] to [n - k], while consuming [k] time credits. *)

  (* Like [force], paying requires the token [ThunkToken p F']. *)

  thunk_pay p F n k t R φ E :
    ↑ThunkPayment ⊆ E →
    Thunk p F t n R φ -∗ TC k
      ={E}=∗
    Thunk p F t (n-k) R φ
  ;

}.

End API.

(* -------------------------------------------------------------------------- *)

(* The predicate [BaseThunk] satisfies the common thunk API. *)

Section BaseInstance.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).

Global Instance base_thunk_api :
  CommonThunkAPI BaseThunk.
Proof.
  constructor.
  { tc_solve. }
  { eauto using base_thunk_proper. }
  { eauto using base_thunk_ne. }
  { eauto using base_thunk_contractive. }
  { eauto using base_thunk_mask_subseteq. }
  { eauto using base_thunk_increase_debt. }
  { eauto using base_thunk_force. }
  { eauto using base_thunk_pay. }
Qed.

End BaseInstance.

(* -------------------------------------------------------------------------- *)

(* We now establish some laws that are consequences of the above laws. *)

Section Consequences.

Context `{CommonThunkAPI Σ Thunk}.
Notation iProp := (iProp Σ).

(* -------------------------------------------------------------------------- *)

(* The combination of [pay] and [force]. *)

Lemma thunk_pay_force p F t n R φ F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC (n + Tf) ∗ Thunk p F t n R φ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & Hp & HR) Post".
  (* Split our credits. *)
  iDestruct "Hcredits" as "(Hn & Hcredits)".
  (* First, pay. *)
  iMod (thunk_pay with "Hthunk Hn") as "#Hthunk'"; eauto 2.
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  rewrite Nat.sub_diag. (* n - n = 0 *)
  (* Then, force the thunk. *)
  by iApply (thunk_force _ F _ R with "Htickinv [$Hcredits $Hp $HR Hthunk]").
Qed.

End Consequences.
