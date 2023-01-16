From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat PiggyBank.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI.

(* -------------------------------------------------------------------------- *)

Section Step.

Context `{BasicThunkAPI Σ Thunk}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
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

(* TODO comments needed *)

Definition isUpdate n R φ ψ : iProp :=
  ∀ v, R -∗ TC n -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v.

Local Definition LeftBranch R φ ψ nc1 nc2 nc : iProp :=
    ⌜ (nc = nc1 + nc2)%nat ⌝
  ∗ isUpdate nc2 R φ ψ.

Local Definition RightBranch t ψ nc : iProp :=
  ∃ v,
      ThunkVal t v
    ∗ □ ψ v.

Definition ThunkStep p F t n R ψ : iProp :=

  ∃ nc1 nc2 φ F1 N,
      ⌜ F1 ∪ ↑N ⊆ F ⌝
    ∗ ⌜ F1 ## ↑N ⌝
    ∗ Thunk p F1 t nc1 R φ
    ∗ PiggyBank
        (LeftBranch R φ ψ nc1 nc2)
        (RightBranch t ψ)
        p N n

.

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
  Persistent (ThunkStep p F t n R ψ).
Proof.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

Local Lemma thunkstep_increase_debt p F t n1 n2 R ψ :
  n1 ≤ n2 →
  ThunkStep p F t n1 R ψ -∗
  ThunkStep p F t n2 R ψ.
Proof.
  iIntros (?) "Hthunk".
  destruct_thunk.
  iPoseProof (piggy_bank_increase_debt with "Hpiggy") as "#Hpiggy'"; [eauto|].
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_consequence N F E p F1 t n1 n2 R φ ψ :
  F1 ∪ ↑N ⊆ F →
  F1 ## ↑N →
  TC 0 -∗ (* TODO get rid of this? *)
  Thunk p F1 t n1 R φ -∗
  isUpdate n2 R φ ψ ={E}=∗
  ThunkStep p F t (n1 + n2) R ψ.
Proof.
  intros.
  iIntros "Htc #Hthunk Hupdate".
  (* Create a piggy bank whose initial debt is [n1 + n2].
     This requires checking that the left branch holds. *)
  iMod (piggybank_create
                (LeftBranch R φ ψ n1 n2)
                (RightBranch t ψ)
                p N (n1 + n2)
              with "Htc [Hupdate]") as "#Hpiggy".
  { unfold LeftBranch. eauto. }
  (* Done. *)
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [force]. *)

Local Lemma thunkstep_force_spec p F F' t R ψ :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ThunkStep p F t 0 R ψ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ ψ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
Proof.
  intros.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Htoken & HR) Post".
  destruct_thunk.

  (* Break the bank! *)
  iMod (piggybank_break with "Hpiggy Htoken") as "Hbank";
    [ set_solver | set_solver |].

  (* This places us in one of two situations: either the bank has never
     been broken yet, or it has been broken before. *)
  iDestruct "Hbank" as "[Hbank | Hbank]".

  (* Case: the bank has never been broken. *)
  {
    (* The piggy bank gives us [nc1 + nc2] time credits as well as the
       ability to close the bank's invariant, provided we are able to
       establish the right branch of our invariant. *)
    iDestruct "Hbank" as (nc) "(Hbranch & Hnc & Htoken & Hclose)".
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
    iDestruct "Hbank" as (nc) "(Hbranch & Htoken & Hclose)".
    destruct_right_branch.
    (* We have [□ ψ v], so we are happy. *)
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force this thunk, which we know has been forced already.
       The result must be [v]. We do not obtain [□ φ v], but
       we do not need it. *)
    iApply (thunk_force_forced_weak with "Htickinv [$Hcredits $Hthunk $Hval $Htoken $HR]").
    { set_solver. }
    iNext.
    iDestruct "Hv" as "#Hv".
    iIntros "(Htoken & HR)".
    (* Close the invariant, whose right-hand side now holds. *)
    iMod ("Hclose" with "[] Htoken") as "Hqwd".
    { construct_right_branch. }
    (* Done. *)
    iModIntro. iApply "Post". eauto with iFrame.
  }

Qed.

Local Lemma thunkstep_force_forced_weak p F t n R ψ v F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ThunkStep p F t n R ψ ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ RET «v» ; ThunkToken p F' ∗ R }}}.
Proof.
  intros.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & #Hval & Htoken & HR) Post".
  destruct_thunk. iClear "Hpiggy".

  (* Remarkably, we do not even need the piggy bank. *)

  (* We force the underlying thunk using the same law,
     and do not execute the ghost update, as we are not
     required to produce [□ ψ v]. *)

  iApply (thunk_force_forced_weak
    with "Htickinv [$Hcredits $Hthunk $Hval $Htoken $HR]");
    [ set_solver |].

  (* Done. *)
  eauto.

Qed.

Local Lemma thunkstep_pay p F F' E n k t R ψ :
  F ⊆ F' →
  F ⊆ E →
  ThunkToken p F' -∗ ThunkStep p F t n R ψ -∗
  TC k ={E}=∗
  ThunkToken p F'  ∗ ThunkStep p F t (n-k) R ψ.
Proof.
  intros.
  iIntros "Htoken #Hthunk Hk".
  destruct_thunk.

  (* Put the [k] credits into the piggy bank. *)
  iMod (piggybank_pay _ _ k with "Htoken Hpiggy Hk") as "($ & #Hpiggy')";
    [ set_solver | set_solver |].

  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now check that the API is satisfied. *)

Global Instance step_thunk_api :
  BasicThunkAPI ThunkStep.
Proof.
  constructor.
  { eauto using thunkstep_increase_debt. }
  { eauto using thunkstep_force_spec. }
  { eauto using thunkstep_force_forced_weak. }
  { eauto using thunkstep_pay. }
Qed.

End Step.
