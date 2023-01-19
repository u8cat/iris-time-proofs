From stdpp Require Import namespaces.
From iris.base_logic Require Import invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_min_nat.

Section Debits.

  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (authR $ optionUR min_natR)}.

  Implicit Type γ : gname.
  Implicit Type m n k : nat.
  Implicit Type Q : iProp Σ.
  Implicit Type E : coPset.

  Definition debitN : namespace := nroot .@ "debit".

  Definition DebitInv γ Q : iProp Σ :=
    ∃ n, own γ (● MinNat' n) ∗ (TC n ==∗ □ Q). (* TODO: should probably be a fupd *)
    (* TODO a different branch contains an attempt to change this definition:
    ∃ n, own γ (● MinNat' n) ∗ ((⌜n ≠ 0⌝ ∗ (TC n ==∗ □ Q)) ∨ □ Q)
       this allows fixing [force], but breaks [pay]. *)
  Definition Debit n Q : iProp Σ :=
    ∃ γ, inv debitN (DebitInv γ Q) ∗ own γ (◯ MinNat' n).

  #[global] Instance debit_persistent n Q : Persistent (Debit n Q) := _.

  Lemma debit_create n Q E :
    (TC n ==∗ □ Q) ={E}=∗ Debit n Q.
  Proof.
    iIntros "HQ".
    iMod (own_alloc (● MinNat' n ⋅ ◯ MinNat' n)) as (γ) "[H● H◯]";
      first by apply auth_both_valid_2.
    iExists γ. iFrame. iApply inv_alloc. iNext. iExists n. by iFrame.
  Qed.

  Lemma debit_weaken n₁ n₂ Q :
    (n₁ ≤ n₂)%nat →
    Debit n₁ Q -∗
    Debit n₂ Q.
  Proof.
    iIntros (I) "H". iDestruct "H" as (γ) "[Hinv H◯]". iExists γ. iFrame "Hinv".
    by iApply own_auth_min_nat_weaken.
  Qed.

  Lemma debit_pay n k Q E :
    ↑debitN ⊆ E →
    Debit n Q -∗ TC k ={E}=∗ Debit (n-k) Q.
  Proof.
    iIntros (?) "H Htc". iDestruct "H" as (γ) "[#Hinv H◯]".
    iMod (inv_acc with "Hinv") as "[Hinner Hclose]"; first done.
    iDestruct "Hinner" as (m) "[>H● HQ]".
    iDestruct (auth_min_nat_update_decr' with "H● H◯") as ">[H● H◯]".
    iMod ("Hclose" with "[H● Htc HQ]") as "_".
    { iNext. iExists (m-k). iFrame "H●". iIntros "Htc'". iApply "HQ".
      iCombine "Htc Htc'" as "Htc". iApply (TC_weaken with "Htc"). lia. }
    { iModIntro. iExists γ. by iFrame. }
  Qed.

  Lemma debit_force Q E :
    ↑debitN ⊆ E →
    Debit 0 Q ={E}=∗ ▷ □ Q.
  Proof.
    iIntros (?) "H". iDestruct "H" as (γ) "[Hinv H◯]".
    iMod (inv_acc with "Hinv") as "[Hinner Hclose]"; first done.
    iDestruct "Hinner" as (m) "[>H● HQ]".
    iDestruct (own_auth_min_nat_le with "H● H◯") as % ->%Nat.le_0_r. iClear "H◯".
    iDestruct (bi.later_wand with "HQ") as "HQ". iMod zero_TC as "Htc0".
    iDestruct ("HQ" with "Htc0") as "HQ".
    rewrite /DebitInv.
    (* FIXME: how to duplicate ▷ (|==> □ Q) ?
        "H●" : own γ (● MinNat' 0)
        "Hclose" : ▷ (∃ n, own γ (● MinNat' n) ∗ (TC n ==∗ □ Q)) ={E∖↑debitN,E}=∗ True
        "HQ" : ▷ (|==> □ Q)
        --------------------------------------∗
        |={E∖↑debitN,E}=> ▷ □ Q
    *)
    iMod ("Hclose" with "[H● HQ]") as "_".
    { iNext. iExists 0. by auto with iFrame. }
    { admit. }
  Admitted.

End Debits.
