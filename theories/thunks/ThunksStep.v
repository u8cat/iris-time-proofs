From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits PiggyBank.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI.

(* In this file, we prove that if we are given a predicate [Thunk] that
   satisfies the API in ThunksAPI.v, then we are able to define a predicate
   [ProxyThunk] that also satisfies this API. in addition, it has a form of
   the consequence rule, which constructs a [ProxyThunk] out of a [Thunk]. *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section Step.

Context `{CommonThunkAPI Σ Thunk}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type E F : coPset.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.

Implicit Type γpaid : gname.
Implicit Type nc ac : nat.
Implicit Type v : val.

(* -------------------------------------------------------------------------- *)

(* We write [isUpdate n R φ ψ] to indicate that we have a one-shot ghost
   update that transforms [□ φ v] into [□ ψ v], for an arbitrary value [v], at
   a cost of [n] time credits. The resource [R] is required, but not consumed,
   by this update. *)

Definition isUpdate n R φ ψ : iProp :=
  ∀ v, R -∗ TC n -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v.

(* The predicate [ProxyThunk] involves a piggy bank whose branches are defined
   as follows:

   - in the left branch, the proxy thunk has not been forced yet: the ghost
     update still exists; the cost [nc1] of forcing the underlying thunk
     plus the cost [nc2] of the ghost update add up to the necessary cost [nc];

   - in the right branch, the proxy thunk has been forced, so the ghost update
     does not exist any more; the underlying thunk has been forced, so its
     value [v] has been decided, and (because the update has been exploited
     already) the postcondition [□ ψ v] holds. *)

Local Definition LeftBranch R φ ψ nc1 nc2 nc : iProp :=
    ⌜ (nc = nc1 + nc2)%nat ⌝
  ∗ isUpdate nc2 R φ ψ.

Local Definition RightBranch t ψ : iProp :=
  ∃ v,
      ThunkVal t v
    ∗ □ ψ v.

(* The definition of [ProxyThunk] is essentially a conjunction of:

   - the underlying thunk, with a debit of [nc1];

   - the piggy bank, whose branches are defined as described above.

   The debit [n] of the piggy bank is also the debit [n] of the proxy thunk.
   Once this debit is zero, the piggy bank can be forced, and this delivers
   enough credit to force the underlying thunk *and* apply the ghost update.

   Things are set up so that the masks required to force the underlying thunk
   and to force the piggy bank are disjoint. The underlying thunk needs [F1],
   while the piggy bank needs [↑N], and we require these masks to be disjoint.
   This is required in the verification of [force]: the piggy bank must be
   broken at the beginning (so as to liberate the time credits stored in it)
   and cannot be closed until the underlying thunk has been forced. In other
   words, the underlying thunk must be forced at a point in time where the
   the piggy bank is opened. This implies that the token for the piggy bank
   and the token for the underlying thunk must be disjoint: the latter must
   be available at a point in time where the former has been consumed. *)

Definition ProxyThunk p F t n R ψ : iProp :=

  ∃ nc1 nc2 φ F1 N,
      ⌜ F1 ∪ ↑N ⊆ F ⌝
    ∗ ⌜ F1 ## ↑N ⌝
    ∗ Thunk p F1 t nc1 R φ
    ∗ PiggyBank
        (LeftBranch R φ ψ nc1 nc2)
        (RightBranch t ψ)
        (ThunkPayment t)
        p N n

.

(* A payment into the proxy thunk is implemented simply as a payment into the
   piggy bank; it is not propagated down as a payment into the underlying
   thunk. Thus, we do *not* have the property that if the piggy bank has zero
   debit then the underlying thunk has zero debit. We *do* have the property
   that if the piggy bank has zero debit then forcing the piggy bank produces
   enough credit to force the underlying thunk. *)

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_thunk :=
  iDestruct "Hthunk"
    as (nc1 nc2 φ F1 N) "(%HuF & %HnF & Hthunk & #Hpiggy)".

Local Ltac destruct_left_branch :=
  unfold LeftBranch;
  iDestruct "Hbranch" as "(>%Heq & Hupdate)".

Local Ltac destruct_right_branch :=
  iDestruct "Hbranch" as (v) "(>#Hval & Hv)".

Local Ltac construct_right_branch :=
  try iNext; iExists _; eauto with iFrame.

Local Ltac construct_thunk :=
  iExists _, _, _, _, _; eauto with iFrame.

(* -------------------------------------------------------------------------- *)

Global Instance thunkstep_persistent p F t n R ψ :
  Persistent (ProxyThunk p F t n R ψ).
Proof.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

Local Lemma thunkstep_increase_debt p F t n1 n2 R ψ :
  n1 ≤ n2 →
  ProxyThunk p F t n1 R ψ -∗
  ProxyThunk p F t n2 R ψ.
Proof.
  iIntros (?) "Hthunk".
  destruct_thunk.
  iPoseProof (piggybank_increase_debt with "Hpiggy") as "#Hpiggy'"; [eauto|].
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_consequence N F E p F1 t n1 n2 R φ ψ :
  F1 ∪ ↑N ⊆ F →
  F1 ## ↑N →
  Thunk p F1 t n1 R φ -∗
  isUpdate n2 R φ ψ ={E}=∗
  ProxyThunk p F t (n1 + n2) R ψ.
Proof.
  intros.
  iIntros "#Hthunk Hupdate".
  (* Create a piggy bank whose initial debt is [n1 + n2].
     This requires checking that the left branch holds. *)
  iMod (piggybank_create
                (LeftBranch R φ ψ n1 n2)
                (RightBranch t ψ)
                (ThunkPayment t)
                p N (n1 + n2)
              with "[Hupdate]") as "#Hpiggy".
  { unfold LeftBranch. eauto. }
  (* Done. *)
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [force]. *)

Local Lemma thunkstep_force_spec p F F' t R ψ :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ProxyThunk p F t 0 R ψ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ ψ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
Proof.
  intros.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Htoken & HR) Post".
  destruct_thunk.

  (* Break the bank! *)
  iMod (piggybank_break with "Hpiggy Htoken")
    as (nc) "(Hbank & Htoken & Hclose)";
    [ set_solver | set_solver | set_solver |].

  (* This places us in one of two situations: either the bank has never
     been broken yet, or it has been broken before. *)
  iDestruct "Hbank" as "[(Hbranch & Hnc) | Hbranch]".

  (* Case: the bank has never been broken. *)
  {
    (* The piggy bank gives us [nc1 + nc2] time credits as well as the
       ability to close the bank's invariant, provided we are able to
       establish the right branch of our invariant. *)
    destruct_left_branch.
    subst nc.
    iDestruct "Hnc" as "(Hnc1 & Hnc2)".
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force the underlying thunk. *)
    iCombine "Hnc1" "Hcredits" as "Hnc1".
    iApply (thunk_pay_force with "Htickinv [$Hnc1 $Hthunk $Htoken $HR]").
    { set_solver. }
    (* This has consumed at least one time step. (This is fortunate.) *)
    iNext.
    iIntros (v) "(#Hv & #Hval & Htoken & HR)".
    (* We can now apply our ghost update, consuming nc2 time credits.
       We must apply this update before closing the invariant, because
       this update produces [□ ψ v], which is needed in order to close
       the invariant. *)
    iMod ("Hupdate" with "HR Hnc2 Hv") as "[HR #Hv']".
    iClear "Hv". iRename "Hv'" into "Hv".
    (* Close the invariant, whose right-hand side now holds. *)
    iMod ("Hclose" with "[] Htoken") as "Hqwd".
    { construct_right_branch. }
    (* Done. *)
    iModIntro. iApply "Post". eauto with iFrame.
  }

  (* Case: the bank has been broken already. *)
  {
    (* The piggy bank requires us to preserve the right branch of our
       invariant. *)
    destruct_right_branch.
    (* We have [□ ψ v], so we are happy. *)
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force this thunk, which we know has been forced already.
       The result must be [v]. *)
    iApply (thunk_force_forced with "Htickinv [$Hcredits $Hthunk $Hval $Htoken]").
    { set_solver. }
    iNext.
    iDestruct "Hv" as "#Hv".
    (* We do not need [□ φ v], which is fortunate, as we do not have it. *)
    iIntros "Htoken".
    (* Close the invariant, whose right-hand side now holds. *)
    iMod ("Hclose" with "[] Htoken") as "Hqwd".
    { construct_right_branch. }
    (* Done. *)
    iModIntro. iApply "Post". eauto with iFrame.
  }

Qed.

Local Lemma thunkstep_force_forced p F t n R ψ v F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ProxyThunk p F t n R ψ ∗ ThunkVal t v ∗ ThunkToken p F' }}}
    «force #t»
  {{{ RET «v» ; ThunkToken p F' }}}.
Proof.
  intros.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & #Hval & Htoken) Post".
  destruct_thunk. iClear "Hpiggy".

  (* Remarkably, we do not even need the piggy bank. *)

  (* We force the underlying thunk using the same law,
     and do not execute the ghost update, as we are not
     required to produce [□ ψ v]. *)

  (* Force the underlying thunk using the same law. *)
  iApply (thunk_force_forced
    with "Htickinv [$Hcredits $Hthunk $Hval $Htoken]");
    [ set_solver |].

  eauto.
Qed.

Local Lemma thunkstep_pay p F E n k t R ψ :
  ↑ThunkPayment t ⊆ E →
  ProxyThunk p F t n R ψ -∗
  TC k ={E}=∗
  ProxyThunk p F t (n-k) R ψ.
Proof.
  intros.
  iIntros "#Hthunk Hk".
  destruct_thunk.

  (* Put the [k] credits into the piggy bank. *)
  iMod (piggybank_pay with "Hpiggy Hk") as "#Hpiggy'";
    [ set_solver |].

  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now check that the API is satisfied. *)

Global Instance step_thunk_api :
  CommonThunkAPI ProxyThunk.
Proof.
  constructor.
  { eauto using thunkstep_increase_debt. }
  { eauto using thunkstep_force_spec. }
  { eauto using thunkstep_force_forced. }
  { eauto using thunkstep_pay. }
Qed.

End Step.
