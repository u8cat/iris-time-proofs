From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.
From iris_time Require Import ThunksCode ThunksBase.

(* -------------------------------------------------------------------------- *)

Section Proofs.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp Σ.
Implicit Type φ : val → iProp Σ.

Implicit Type γpaid γdecided : gname.
Implicit Type nc ac : nat.
Implicit Type f v : val.

Definition ThunkStepInv t γpaid nc R φ ψ : iProp Σ :=

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

Definition ThunkStep p N t n R ψ : iProp Σ :=

  ∃ γpaid nc1 nc2 φ,
      Thunk p (N .@ false) t nc1 R φ
    ∗ na_inv p (N .@ true) (ThunkStepInv t γpaid nc2 R φ ψ)
    ∗ own γpaid (◯ MaxNat (nc1 + nc2 - n))

.

(* -------------------------------------------------------------------------- *)

Global Instance thunkstep_persistent p N t n R ψ :
  Persistent (ThunkStep p N t n R ψ).
Proof using.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_weakening p N t n₁ n₂ R ψ :
  n₁ ≤ n₂ →
  ThunkStep p N t n₁ R ψ -∗
  ThunkStep p N t n₂ R ψ.
Proof.
  iIntros (?) "Hthunk".
  iDestruct "Hthunk" as (γpaid nc1 nc2 φ) "(? & ? & Hγpaid◯)".
  iExists γpaid, nc1, nc2, φ. iFrame.
  iDestruct (own_auth_max_nat_weaken with "Hγpaid◯") as "$".
  lia.
Qed.

(* -------------------------------------------------------------------------- *)

Lemma thunkstep_consequence E p N t n1 n2 n R φ ψ :
  TC 0 -∗ (* TODO get rid of this? *)
  Thunk p (N .@ false) t n1 R φ -∗ (* TODO namespace trouble? *)
  (∀ v, R -∗ TC n2 -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v) -∗
  ⌜ n1 + n2 ≤ n ⌝ ={E}=∗
  ThunkStep p N t n R ψ.
Proof.
  iIntros "Hcredits #Hthunk Hupdate %Hleq".
  (* Allocate the ghost cell γpaid. *)
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● Hγpaid◯]".
  iExists γpaid, n1, n2, φ.
  rewrite (_ : n1 + n2 - n = 0); [| lia].
  iFrame "Hthunk".
  iFrame "Hγpaid◯".
  (* Allocate the invariant. *)
  iApply na_inv_alloc.
  iNext.
  (* The number of available credits is initially zero. *)
  iExists 0.
  iFrame "Hγpaid●".
  (* The left-hand disjunct initially holds. *)
  iLeft.
  iFrame "Hcredits Hupdate".
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [force]. *)

Lemma thunkstep_force_spec p N F t R ψ :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ ThunkStep p N t 0 R ψ ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ ψ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Hp & HR) Post".
  iDestruct "Hthunk" as (γpaid nc1 nc2 φ) "#(Hthunk & Hinv & Hγpaid◯)".
  rewrite Nat.sub_0_r. (* nc - 0 = nc *)

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hinv Hp")
    as ">(Hstepinv & Hp & Hclose)";
    [done|eauto with ndisj|]. (* side conditions about masks *)

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
    { eauto with ndisj. }
    (* This has consumed at least one time step. (This is fortunate.) *)
    iNext.
    iIntros (v) "(#Hv & #Hval & Hp & HR)".
    (* We can now apply our ghost update, consuming nc2 time credits. *)
    iMod ("Hupdate" with "HR Hnc2 Hv") as "[HR #Hv']".
    iClear "Hv". iRename "Hv'" into "Hv".
    (* Close the invariant. *)
    iMod ("Hclose" with "[Hγpaid● Hp]") as "Hp".
    { (* The right-hand side of the invariant now holds. *)
      iFrame "Hp". iNext. iExists ac. eauto with iFrame. }
    (* Done. *)
    iModIntro.
    iApply "Post".
    iFrame "Hv Hval Hp HR".
  }

  (* Case: the ghost update has been used already. *)
  {
    iDestruct "Hstepinv" as (v) "(>#Hval & Hv)".
    (* We have [□ ψ v], so we are happy. *)
    (* Allow a ghost update after we force this thunk. *)
    iApply wp_fupd.
    (* Force this thunk, which we know has been forced already.
       The result must be [v]. *)
    iApply (thunk_force_forced with "Htickinv [$Hcredits $Hthunk $Hval $Hp $HR]").
    { eauto with ndisj. }
    iNext.
    iDestruct "Hv" as "#Hv".
    iIntros "(_ & Hp & HR)".
    (* Close the invariant. *)
    iMod ("Hclose" with "[Hγpaid● Hp]") as "Hp".
    { (* The right-hand side of the invariant now holds. *)
      iFrame "Hp". iNext. iExists ac. eauto with iFrame. }
    (* Done. *)
    iApply "Post".
    iModIntro.
    iFrame "Hv Hval Hp HR".
  }
Qed.

Lemma thunkstep_pay p N F E n k t R ψ :
  ↑N ⊆ F →
  ↑N ⊆ E →
  na_own p F -∗ ThunkStep p N t n R ψ -∗
  TC k ={E}=∗
  na_own p F  ∗ ThunkStep p N t (n-k) R ψ.
Proof.
  iIntros (? ?) "Hp #Hthunk Hk".
  iDestruct "Hthunk" as (γpaid nc1 nc2 φ) "#(Hthunk & Hinv & Hγpaid◯)".

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hinv Hp") as ">(Hstep & Hp & Hclose)";
    [ eauto with ndisj | eauto with ndisj |].
  iDestruct "Hstep" as (ac) "(>Hγpaid● & Hstep)".

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
    iExists γpaid, nc1, nc2, φ. iFrame "Hthunk Hinv".
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
    iExists γpaid, nc1, nc2, φ. iFrame "Hthunk Hinv".
    iApply (own_auth_max_nat_weaken with "[$]").
    lia.
  }

Qed.

End Proofs.
