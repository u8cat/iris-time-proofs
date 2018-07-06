From iris Require Export  algebra.auth  base_logic.lib.own  proofmode.tactics.



Notation "'●mnat' n" := (Auth (A:=mnat) (Excl' n%nat) ε) (at level 20).
Notation "'◯mnat' n" := (Auth (A:=mnat) None n%nat) (at level 20).

Section Auth_mnat.

  Context `{inG Σ (authR mnatUR)}.

  Lemma auth_mnat_alloc (n : mnat) :
    (|==> ∃ γ, own γ (●mnat n) ∗ own γ (◯mnat n))%I.
  Proof.
    by iMod (own_alloc (●mnat n ⋅ ◯mnat n)) as (γ) "[? ?]" ; auto with iFrame.
  Qed.
  Global Arguments auth_mnat_alloc _%nat.

  Lemma own_auth_mnat_le (γ : gname) (m n : mnat) :
    own γ (●mnat m) -∗
    own γ (◯mnat n) -∗
    ⌜(n ≤ m)%nat⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as % [[k ->] _] % auth_valid_discrete_2.
    iPureIntro. apply Max.le_max_l.
  Qed.

  Lemma own_auth_mnat_weaken (γ : gname) (n₁ n₂ : mnat) :
    (n₂ ≤ n₁)%nat →
    own γ (◯mnat n₁) -∗
    own γ (◯mnat n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = n₁ `max` n₂)%nat ; last (by rewrite max_l).
    iDestruct "H" as "[_$]".
  Qed.
  Global Arguments own_auth_mnat_weaken _ (_ _ _)%nat_scope.

  Lemma own_auth_mnat_null (γ : gname) (m : mnat) :
    own γ (●mnat m) -∗
    own γ (●mnat m) ∗ own γ (◯mnat 0).
  Proof.
    by rewrite - own_op.
  Qed.
  Global Arguments own_auth_mnat_null _ _%nat_scope.

  Lemma auth_mnat_update_read_auth (γ : gname) (m : mnat) :
    own γ (●mnat m) -∗
    |==> own γ (●mnat m) ∗ own γ (◯mnat m).
  Proof.
    iIntros "H●".
    iDestruct (own_auth_mnat_null with "H●") as "[H● H◯]".
    (iMod (own_update_2 with "H● H◯") as "[$ $]" ; last done).
    apply auth_update, mnat_local_update. lia.
  Qed.
  Global Arguments auth_mnat_update_read_auth _ _%nat_scope.

  Lemma auth_mnat_update_incr (γ : gname) (m k : mnat) :
    own γ (●mnat m) -∗
    |==> own γ (●mnat (m + k : mnat)).
  Proof.
    iIntros "H●". iDestruct (own_auth_mnat_null with "H●") as "[H● H◯]".
    iMod (own_update_2 with "H● H◯") as "[$ _]" ; last done.
    apply auth_update, mnat_local_update. lia.
  Qed.
  Global Arguments auth_mnat_update_incr _ (_ _)%nat_scope.

  Lemma auth_mnat_update_incr' (γ : gname) (m n k : mnat) :
    own γ (●mnat m) -∗
    own γ (◯mnat n) -∗
    |==> own γ (●mnat (m + k : mnat)) ∗ own γ (◯mnat (n + k : mnat)).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_auth_mnat_le with "H● H◯") as %I. iClear "H◯".
    iDestruct (auth_mnat_update_incr _ _ k with "H●") as ">H●".
    iDestruct (auth_mnat_update_read_auth with "H●") as ">[$ H◯]".
    iModIntro.
    rewrite (_ : m + k = (n + k) `max` (m + k))%nat ; last lia.
    iDestruct "H◯" as "[$ _]".
  Qed.
  Global Arguments auth_mnat_update_incr' _ (_ _ _)%nat_scope.

End Auth_mnat.