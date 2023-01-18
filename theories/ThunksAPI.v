From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase.

Section API.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* needed by ThunkVal *)
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

  (* [Thunk] must be persistent. This means that a thunk can be shared. In
    combination with [thunk_increase_debt] and [thunk_pay], this implies that
    several different views of a thunk, with distinct numbers of debits, can
    co-exist. *)

  `{
    ∀ p F t n R φ,
    Persistent (Thunk p F t n R φ)
  }

:= {

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

  (* This specification is weak: it does not guarantee [□ φ v]. One cannot
     hope to obtain this property when [n] is nonzero. Establishing this
     property conditionally, only in the special case where [n = 0] holds,
     may be possible, but leads to difficulties in the proof. *)

  thunk_force_forced p F t n R φ v F' :
    F ⊆ F' →
    TC_invariant -∗
    {{{ TC 11 ∗ Thunk p F t n R φ ∗ ThunkVal t v ∗ ThunkToken p F' }}}
      «force #t»
    {{{ RET «v» ; ThunkToken p F' }}}
  ;

  (* The ghost operation [pay] allows paying for (part of) the cost of a
     thunk. A thunk must be fully paid for before it can be forced. *)

  (* Paying is a ghost operation. Its effect is to change the number of debits
     from [n] to [n - k], while consuming [k] time credits. *)

  (* Like [force], paying requires the token [ThunkToken p F']. *)

  thunk_pay p F n k t R φ E :
    ↑ThunkPayment t ⊆ E →
    Thunk p F t n R φ -∗ TC k
      ={E}=∗
    Thunk p F t (n-k) R φ
  ;

}.

End API.

(* -------------------------------------------------------------------------- *)

(* The predicate [BaseThunk] satisfies the basic thunk API. *)

Section BaseInstance.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).

Global Instance base_thunk_api :
  BasicThunkAPI BaseThunk.
Proof.
  constructor.
  { eauto using base_thunk_increase_debt. }
  { eauto using base_thunk_force. }
  { (* The goal here is almost identical to [base_thunk_force_forced].
       It differs in that we are not asked to prove [□ φ v], yet we
       are actually able to prove it. *)
    intros.
    iIntros "#Htickinv" (Φ) "!# (Htc & #Hthunk & #Hval & Htoken) Post".
    wp_apply (base_thunk_force_forced
               with "Htickinv [$Htc $Hthunk $Hval $Htoken]"); [ done |].
    iIntros "(#Hv & Htoken)".
    iClear "Hv". (* Drop φ v *)
    iApply "Post".
    iFrame "Htoken". }
  { eauto using base_thunk_pay. }
Qed.

End BaseInstance.

(* -------------------------------------------------------------------------- *)

(* We now establish some laws that are consequences of the above laws. *)

Section Consequences.

Context `{BasicThunkAPI Σ Thunk}.
Notation iProp := (iProp Σ).

(* -------------------------------------------------------------------------- *)

(* The combination of [pay] and [force]. *)

Lemma thunk_pay_force p F t n R φ F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC (n + 11) ∗ Thunk p F t n R φ ∗ ThunkToken p F' ∗ R }}}
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
  iApply (thunk_force with "Htickinv [$Hcredits $Hthunk $Hp $HR]"); [ done |].
  (* Done. *)
  iApply "Post".
Qed.

End Consequences.
