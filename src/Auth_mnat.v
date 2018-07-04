From iris Require Export  algebra.auth  base_logic.lib.own  proofmode.tactics.



Notation "'●mnat' n" := (Auth (A:=mnat) (Excl' n%nat) ε) (at level 20).
Notation "'◯mnat' n" := (Auth (A:=mnat) None n%nat) (at level 20).

Section Auth_mnat.

  Context `{inG Σ (authR mnatUR)}.

  Lemma own_auth_mnat_null (γ : gname) (m : mnat) :
    own γ (●mnat m) -∗
    own γ (●mnat m) ∗ own γ (◯mnat 0).
  Proof.
    by rewrite - own_op (_ : ●mnat m ⋅ ◯mnat 0 = ●mnat m).
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

End Auth_mnat.