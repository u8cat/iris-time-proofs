From iris Require Export  algebra.auth algebra.numbers.
From iris Require Import  algebra.excl base_logic.lib.own proofmode.tactics.

Notation "'●max_nat' n" := (auth_auth (A:=max_natUR) (DfracOwn 1%Qp) n%nat) (at level 20).
Notation "'◯max_nat' n" := (auth_frag (A:=max_natUR) n%nat) (at level 20).

Local Coercion max_nat_car : max_nat >-> nat.

Section Auth_max_nat.
  Context `{inG Σ (authR max_natUR)}.

  Lemma auth_max_nat_alloc (n : max_nat) :
    ⊢ |==> ∃ γ, own γ (●max_nat n) ∗ own γ (◯max_nat n).
  Proof.
    iMod (own_alloc (●max_nat n ⋅ ◯max_nat n)) as (γ) "[? ?]".
    - by apply auth_both_valid_2.
    - by auto with iFrame.
  Qed.
  Global Arguments auth_max_nat_alloc _%nat.

  Lemma own_auth_max_nat_le (γ : gname) (m n : max_nat) :
    own γ (●max_nat m) -∗
    own γ (◯max_nat n) -∗
    ⌜(n ≤ m)%nat⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as % [[k ->] _] % auth_both_valid_discrete.
    iPureIntro. apply Max.le_max_l.
  Qed.

  Lemma own_auth_max_nat_weaken (γ : gname) (n₁ n₂ : max_nat) :
    (n₂ ≤ n₁)%nat →
    own γ (◯max_nat n₁) -∗
    own γ (◯max_nat n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = n₁ ⋅ n₂)%nat.
    - rewrite auth_frag_op. iDestruct "H" as "[_$]".
    - destruct n₁, n₂. rewrite max_nat_op. f_equal. simpl in I. lia.
  Qed.
  Global Arguments own_auth_max_nat_weaken _ (_ _ _)%nat_scope.

  Lemma own_auth_max_nat_null (γ : gname) (m : max_nat) :
    own γ (●max_nat m) -∗
    own γ (●max_nat m) ∗ own γ (◯max_nat (MaxNat 0)).
  Proof.
    by rewrite - own_op.
  Qed.
  Global Arguments own_auth_max_nat_null _ _%nat_scope.

  Lemma auth_max_nat_update_read_auth (γ : gname) (m : max_nat) :
    own γ (●max_nat m) -∗
    |==> own γ (●max_nat m) ∗ own γ (◯max_nat m).
  Proof.
    iIntros "H●".
    iDestruct (own_auth_max_nat_null with "H●") as "[H● H◯]".
    (iMod (own_update_2 with "H● H◯") as "[$ $]" ; last done).
    apply auth_update, max_nat_local_update. lia.
  Qed.
  Global Arguments auth_max_nat_update_read_auth _ _%nat_scope.

  Lemma auth_max_nat_update_incr (γ : gname) (m k : max_nat) :
    own γ (●max_nat m) -∗
    |==> own γ (●max_nat (MaxNat (m + k))).
  Proof.
    iIntros "H●". iDestruct (own_auth_max_nat_null with "H●") as "[H● H◯]".
    iMod (own_update_2 with "H● H◯") as "[$ _]" ; last done.
    apply auth_update, max_nat_local_update. destruct m. simpl. lia.
  Qed.
  Global Arguments auth_max_nat_update_incr _ (_ _)%nat_scope.

  Lemma auth_max_nat_update_incr' (γ : gname) (m n k : max_nat) :
    own γ (●max_nat m) -∗
    own γ (◯max_nat n) -∗
    |==> own γ (●max_nat (MaxNat (m + k))) ∗ own γ (◯max_nat (MaxNat (n + k))).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_auth_max_nat_le with "H● H◯") as %I. iClear "H◯".
    iDestruct (auth_max_nat_update_incr _ _ k with "H●") as ">H●".
    iDestruct (auth_max_nat_update_read_auth with "H●") as ">[$ H◯]".
    iModIntro.
    rewrite (_ : MaxNat (m + k) = MaxNat (n + k) ⋅ MaxNat (m + k))%nat.
    - iDestruct "H◯" as "[$ _]".
    - rewrite max_nat_op. f_equal. lia.
  Qed.
  Global Arguments auth_max_nat_update_incr' _ (_ _ _)%nat_scope.
End Auth_max_nat.
