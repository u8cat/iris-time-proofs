From iris Require Export  algebra.auth algebra.numbers.
From iris Require Import  algebra.excl base_logic.lib.own proofmode.proofmode.

#[global] Notation MinNat' n := (Some (MinNat n)).

Section Auth_min_nat.
  Context `{inG Σ (authR $ optionUR min_natR)}.

  Lemma auth_min_nat_alloc (n : nat) :
    ⊢ |==> ∃ γ, own γ (● MinNat' n) ∗ own γ (◯ MinNat' n).
  Proof.
    iMod (own_alloc (● MinNat' n ⋅ ◯ MinNat' n)) as (γ) "[? ?]".
    - by apply auth_both_valid_2.
    - by auto with iFrame.
  Qed.

  Lemma own_auth_min_nat_le (γ : gname) (m n : nat) :
    own γ (● MinNat' m) -∗
    own γ (◯ MinNat' n) -∗
    ⌜(m ≤ n)%nat⌝.
  Proof.
    iIntros "H● H◯".
    by iDestruct (own_valid_2 with "H● H◯")
      as %[ [ ?
            | (? & ? & [=<-] & [=<-] & [[=->]%leibniz_equiv | ?%min_nat_included])
            ] % option_included _] % auth_both_valid_discrete.
  Qed.

  Lemma own_auth_min_nat_weaken (γ : gname) (n₁ n₂ : nat) :
    (n₁ ≤ n₂)%nat →
    own γ (◯ MinNat' n₁) -∗
    own γ (◯ MinNat' n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = n₁ `min` n₂)%nat ; last lia.
    rewrite -min_nat_op_min Some_op auth_frag_op. iDestruct "H" as "[_$]".
  Qed.
  Global Arguments own_auth_min_nat_weaken _ (_ _ _)%nat_scope.

  Lemma own_auth_min_nat_infinity (γ : gname) :
    ⊢ |==> own γ (◯ None).
  Proof.
    by apply own_unit.
  Qed.

  Lemma auth_min_nat_update_read_auth (γ : gname) (m : nat) :
    own γ (● MinNat' m) -∗
    |==> own γ (● MinNat' m) ∗ own γ (◯ MinNat' m).
  Proof.
    iIntros "H●". rewrite -own_op. iApply (own_update with "H●").
    apply auth_update_alloc. rewrite -[x in _ ~l~> (_, x)] left_id.
    apply core_id_local_update; last done. by apply _.
  Qed.

  Lemma auth_min_nat_update_decr (γ : gname) (m k : nat) :
    own γ (● MinNat' m) -∗
    |==> own γ (● MinNat' (m - k)).
  Proof.
    iIntros "H●".
    iMod (auth_min_nat_update_read_auth with "H●") as "H●◯".
    iAssert (|==> own γ (● MinNat' (m - k)) ∗ own γ (◯ MinNat' (m - k)))%I
      with "[-]" as ">[$ _]"; last done.
    rewrite - 2!own_op. iApply (own_update with "H●◯").
    apply auth_update, option_local_update, min_nat_local_update. cbn. lia.
  Qed.

  Lemma auth_min_nat_update_decr' (γ : gname) (m n k : nat) :
    own γ (● MinNat' m) -∗
    own γ (◯ MinNat' n) -∗
    |==> own γ (● MinNat' (m - k)) ∗ own γ (◯ MinNat' (n - k)).
  Proof.
    iIntros "H● H◯". iDestruct (own_auth_min_nat_le with "H● H◯") as %I.
    rewrite -[in own _ (◯ MinNat' (_-_))] (own_auth_min_nat_weaken _ (m-k) (n-k)); last lia.
    iCombine "H● H◯" as "H●◯". rewrite -own_op. iApply (own_update with "H●◯").
    apply auth_update, option_local_update, min_nat_local_update. cbn. lia.
  Qed.

End Auth_min_nat.
