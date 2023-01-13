From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.
From iris_time Require Import ThunksCode ThunksAPI.

(* -------------------------------------------------------------------------- *)

Section Step.

Context `{BasicThunkAPI}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)

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

Definition ThunkStepInv t γpaid nc R φ ψ : iProp :=

  ∃ ac,
      own γpaid (● MaxNat ac)
    ∗ (
        (
            (∀ v, R -∗ TC nc -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v)
                  (* TODO is this the correct update symbol? *)
          ∗ TC ac
        )
      ∨ (∃ (v : val),
            ThunkVal t v
          ∗ □ ψ v
        )
      )
.

Definition ThunkStep p F t n R ψ : iProp :=

  ∃ γpaid nc1 nc2 φ F1 N,
      ⌜ F1 ∪ ↑N ⊆ F ⌝
    ∗ ⌜ F1 ∩ ↑N = ∅ ⌝
    ∗ Thunk p F1 t nc1 R φ
    ∗ na_inv p N (ThunkStepInv t γpaid nc2 R φ ψ)
    ∗ own γpaid (◯ MaxNat (nc1 + nc2 - n))

.

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_thunk :=
  iDestruct "Hthunk"
    as (γpaid nc1 nc2 φ F1 N) "(%HuF & %HnF & Hthunk & Hinv & Hγpaid◯)".

Local Ltac open_invariant :=
  iDestruct (na_inv_acc with "Hinv Hp") as ">(Hstepinv & Hp & Hclose)";
    [ set_solver | set_solver |].

Local Ltac pure_conjunct :=
  iSplitR; [ iPureIntro; eauto |].

(* -------------------------------------------------------------------------- *)

Global Instance thunkstep_persistent p F t n R ψ :
  Persistent (ThunkStep p F t n R ψ).
Proof.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_weakening p F t n1 n2 R ψ :
  n1 ≤ n2 →
  ThunkStep p F t n1 R ψ -∗
  ThunkStep p F t n2 R ψ.
Proof.
  iIntros (?) "Hthunk".
  destruct_thunk.
  iExists γpaid, nc1, nc2, φ, F1, N.
  repeat pure_conjunct.
  iFrame.
  iDestruct (own_auth_max_nat_weaken with "Hγpaid◯") as "$".
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_consequence E p F1 N F t n1 n2 n R φ ψ :
  F1 ∪ ↑N ⊆ F →
  F1 ∩ ↑N = ∅ →
  TC 0 -∗ (* TODO get rid of this? *)
  Thunk p F1 t n1 R φ -∗
  (∀ v, R -∗ TC n2 -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v) ={E}=∗
  ThunkStep p F t (n1 + n2) R ψ.
Proof.
  iIntros (? ?) "Hcredits #Hthunk Hupdate".
  (* Allocate the ghost cell γpaid. *)
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● Hγpaid◯]".
  iExists γpaid, n1, n2, φ, F1, N.
  rewrite Nat.sub_diag.
  repeat pure_conjunct.
  iFrame "Hthunk Hγpaid◯".
  (* Allocate the invariant. *)
  iApply na_inv_alloc.
  iNext.
  (* The number of available credits is initially zero. *)
  iExists 0. eauto with iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [force]. *)

Lemma thunkstep_force_spec p F F' t R ψ :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ThunkStep p F t 0 R ψ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ ψ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Hp & HR) Post".
  destruct_thunk.
  rewrite Nat.sub_0_r. (* nc - 0 = nc *)

  (* Open the invariant. *)
  open_invariant.

  (* Perform a case analysis. *)
  iDestruct "Hstepinv" as (ac) "(>Hγpaid● & [ Hstepinv | Hstepinv ])".

  (* Case: the ghost update has not been used yet. *)
  {
    iDestruct "Hstepinv" as "(Hupdate & >Hac)".
    (* We learn [nc1 + nc2 ≤ ac]. *)
    iDestruct (own_auth_max_nat_le with "Hγpaid● Hγpaid◯") as "%Hleq".
    (* Therefore, we have nc1 + nc2 + 11 time credits at hand. *)
    iDestruct (TC_weaken _ _ Hleq with "Hac") as "[Hnc1 Hnc2]". clear Hleq.
    iAssert (TC (nc1 + 11))%I with "[Hnc1 Hcredits]" as "Hnc1".
    { iSplitL "Hnc1"; iFrame. }
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force the underlying thunk. *)
    iApply (thunk_pay_force with "Htickinv [$Hnc1 $Hthunk $Hp $HR]").
    { set_solver. }
    (* This has consumed at least one time step. (This is fortunate.) *)
    iNext.
    iIntros (v) "(#Hv & #Hval & Hp & HR)".
    (* We can now apply our ghost update, consuming nc2 time credits.
       We must apply this update before closing the invariant, because
       this update produces [□ ψ v], which is needed in order to close
       the invariant. *)
    iMod ("Hupdate" with "HR Hnc2 Hv") as "[HR #Hv']".
    iClear "Hv". iRename "Hv'" into "Hv".
    (* Close the invariant. *)
    iMod ("Hclose" with "[Hγpaid● Hp]") as "Hp".
    { (* The right-hand side of the invariant now holds. *)
      iFrame "Hp". iNext. iExists ac. eauto with iFrame. }
    (* Done. *)
    iModIntro.
    iApply "Post".
    eauto with iFrame.
  }

  (* Case: the ghost update has been used already. *)
  {
    iDestruct "Hstepinv" as (v) "(>#Hval & Hv)".
    (* We have [□ ψ v], so we are happy. *)
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force this thunk, which we know has been forced already.
       The result must be [v]. We do not obtain [□ φ v], but
       we do not need it. *)
    iApply (thunk_force_forced_weak with "Htickinv [$Hcredits $Hthunk $Hval $Hp $HR]").
    { set_solver. }
    iNext.
    iDestruct "Hv" as "#Hv".
    iIntros "(Hp & HR)".
    (* Close the invariant. *)
    iMod ("Hclose" with "[Hγpaid● Hp]") as "Hp".
    { (* The right-hand side of the invariant now holds. *)
      iFrame "Hp". iNext. iExists ac. eauto with iFrame. }
    (* Done. *)
    iApply "Post".
    iModIntro.
    eauto with iFrame.
  }
Qed.

Lemma thunkstep_force_forced_weak p F t n R ψ v F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ ThunkStep p F t n R ψ ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ RET «v» ; ThunkToken p F' ∗ R }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & #Hval & Hp & HR) Post".
  destruct_thunk. iClear "Hinv Hγpaid◯".

  (* Remarkably, we do not even need to open the invariant. *)

  (* We force the underlying thunk using the same law,
     and do not execute the ghost update, as we are not
     required to produce [□ ψ v]. *)

  iApply (thunk_force_forced_weak
    with "Htickinv [$Hcredits $Hthunk $Hval $Hp $HR]");
    [ set_solver |].

  (* Done. *)
  eauto.

Qed.

Lemma thunkstep_pay p F F' E n k t R ψ :
  F ⊆ F' →
  F ⊆ E →
  ThunkToken p F' -∗ ThunkStep p F t n R ψ -∗
  TC k ={E}=∗
  ThunkToken p F'  ∗ ThunkStep p F t (n-k) R ψ.
Proof.
  iIntros (? ?) "Hp #Hthunk Hk".
  destruct_thunk.

  (* Open the invariant. *)
  open_invariant.
  iDestruct "Hstepinv" as (ac) "(>Hγpaid● & Hstep)".

  (* Increment the ghost payment record from [ac] to [ac + k]. This is
     done in both branches of the case analysis (which follows). *)
  iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγpaid● Hγpaid◯")
    as ">[Hγpaid●' #Hγpaid◯']".
  iClear "Hγpaid◯". iRename "Hγpaid◯'" into "Hγpaid◯".

  (* Perform a case analysis. *)
  iDestruct "Hstep" as "[ Hstep | Hstep ]".

  (* Case: the ghost update has not yet been used. *)
  {
    iDestruct "Hstep" as "(Hupdate & >Hac)".
    (* We have [ac + k] time credits. *)
    iAssert (TC (ac + k)) with "[Hac Hk]" as "Hack"; first by iSplitL "Hac".
    (* The invariant can be closed. *)
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists (ac+k). auto with iFrame. }
    iModIntro.
    iExists γpaid, nc1, nc2, φ, F1, N. iFrame "Hthunk Hinv".
    repeat pure_conjunct.
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [Thunk] assertion. *)
    iApply (own_auth_max_nat_weaken with "[$]").
    lia.
  }

  (* Case: the ghost update has been used. *)
  {
    iDestruct "Hstep" as (v) "(>#Hval & #Hv)".
    (* The invariant can be closed. In this case, no new time credits are
       stored in the invariant. The extra payment is wasted. *)
    iClear "Hk".
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists (ac+k). auto with iFrame. }
    iModIntro.
    iExists γpaid, nc1, nc2, φ, F1, N. iFrame "Hthunk Hinv".
    repeat pure_conjunct.
    iApply (own_auth_max_nat_weaken with "[$]").
    lia.
  }

Qed.

(* -------------------------------------------------------------------------- *)

(* We now check that the API is satisfied. *)

Global Instance thunkbase_api :
  BasicThunkAPI ThunkStep ThunkVal.
Proof.
  constructor.
  { eauto using confront_thunkval_thunkval. }
  { eauto using thunkstep_weakening. }
  { eauto using thunkstep_force_spec. }
  { eauto using thunkstep_force_forced_weak. }
  { eauto using thunkstep_pay. }
Qed.

End Step.
