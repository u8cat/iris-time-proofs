From iris.heap_lang Require Import proofmode notation.
Require Import TimeReceipts.
Require Import stdpp.numbers.

Open Scope Z_scope.

Definition w : nat := 64.
(*Definition max_uint : Z := Eval compute in 1 ≪ w.
Definition max_int : Z := Eval compute in 1 ≪ (w-1).
Definition min_int : Z := Eval compute in - max_int.*)
Definition max_int : Z := 1 ≪ (w-1).
Definition min_int : Z := - max_int.
Definition max_uint : Z := 2 * max_int.

Section machine_int.

Context `{heapG Σ}.

Definition is_machine_int (n : Z) : iProp Σ :=
  ⌜min_int ≤ n < max_int⌝%I.

Definition machine_int_add : val :=
  λ: "x" "y",
    ("x" + "y" + #max_int) `rem` #max_uint - #max_int.

Lemma machine_int_add_spec n1 n2 :
  {{{ is_machine_int n1 ∗ is_machine_int n2 ∗ ⌜min_int ≤ n1+n2 < max_int⌝ }}}
  machine_int_add #n1 #n2
  {{{ RET #(n1+n2) ; is_machine_int (n1+n2) }}}.
Proof.
  iIntros (Φ) "(_ & _ & %) Post". repeat (wp_pure _).
  (* boring arithmetic proof: *)
  assert ((n1 + n2 + max_int) `rem` max_uint - max_int = n1 + n2) as ->. {
    assert ((n1 + n2 + max_int) `rem` max_uint = n1 + n2 + max_int). {
      (*assert (min_int = -max_int) by done.
      assert (max_int + max_int = max_uint) by done.*)
      apply Z.rem_small. unfold min_int, max_uint in *. lia.
    }
    lia.
  }
  by iApply "Post".
Qed.

End machine_int.

Section clock_int.

Context `{timeReceiptHeapG Σ}.
Context (nmax : nat).
Context `(nmax ≤ max_int).

Definition is_clock_int (n : nat) : iProp Σ :=
  TR n.

  Lemma TR_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TR n₁ -∗ TR n₂.
  Require Import Auth_nat.
  Proof. apply own_auth_nat_weaken. Qed.

  Lemma TR_lt_nmax n (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant nmax -∗ TR n ={E}=∗ TR n ∗ ⌜n < nmax⌝%nat.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec nmax n) as [ I | I ] ; last by iFrame.
    iDestruct (TR_weaken n nmax with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TR_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

Lemma clock_int_add_spec n1 n2 :
  TR_invariant nmax -∗
  {{{ is_clock_int n1 ∗ is_clock_int n2 }}}
  machine_int_add #n1 #n2
  {{{ RET #(n1+n2) ; is_clock_int (n1+n2) }}}.
Proof.
  iIntros "#Htrinv" (Φ) "!# (H1 & H2) Post".
  iAssert (TR (n1+n2)) with "[H1 H2]" as "H" ; first by (rewrite TR_plus ; iFrame).
  iDestruct (TR_lt_nmax with "Htrinv H") as ">(H & %)" ; first done.
  wp_apply (machine_int_add_spec n1 n2 with "[] [H Post]") .
  {
    iPureIntro. unfold min_int in *. lia.
  }
  {
    iNext ; iIntros "%". iApply "Post". iFrame "H".
  }
Qed.

End clock_int.

Section snapclock_int.

Context `{timeReceiptHeapG Σ}.
Context (nmax : nat).
Context `(nmax ≤ max_int).

Definition is_snapclock_int (n : nat) : iProp Σ :=
  TRdup n.

  Lemma TRdup_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TRdup n₁ -∗ TRdup n₂.
  Require Import Auth_mnat.
  Proof. apply own_auth_mnat_weaken. Qed.

  Lemma TRdup_lt_nmax n (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant nmax -∗ TRdup n ={E}=∗ TRdup n ∗ ⌜n < nmax⌝%nat.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec nmax n) as [ I | I ] ; last by iFrame.
    iDestruct (TRdup_weaken n nmax with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TRdup_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

Lemma snapclock_int_incr_spec n1 :
  TR_invariant nmax -∗
  {{{ is_snapclock_int n1 }}}
  tock #() ;; machine_int_add #n1 #1
  {{{ RET #(n1+1) ; is_snapclock_int (n1+1) }}}.
Proof.
  iIntros "#Htrinv" (Φ) "!# H1 Post".
  wp_apply (tock_spec_simple nmax #() with "Htrinv H1"). iIntros "(_ & H)".
  iDestruct (TRdup_lt_nmax with "Htrinv H") as ">(H & %)" ; first done.
  wp_seq.
  wp_apply (machine_int_add_spec n1 1 with "[] [H Post]") .
  {
    iPureIntro. unfold min_int in *. lia.
  }
  {
    iNext ; iIntros "%". iApply "Post". iFrame "H".
  }
Qed.

Lemma snapclock_int_add_spec n1 n2 m :
  TR_invariant nmax -∗
  {{{ is_snapclock_int n1 ∗ is_snapclock_int n2
    ∗ is_snapclock_int m ∗ ⌜n1+n2 ≤ m⌝ }}}
  machine_int_add #n1 #n2
  {{{ RET #(n1+n2) ; is_snapclock_int (n1+n2) }}}.
Proof.
  iIntros "#Htrinv" (Φ) "!# (_ & _ & Hm & %) Post".
  iDestruct (TRdup_lt_nmax with "Htrinv Hm") as ">(Hm & %)" ; first done.
  iDestruct (TRdup_weaken m (n1 + n2) with "Hm") as "H" ; first lia.
  wp_apply (machine_int_add_spec n1 n2 with "[] [H Post]") .
  {
    iPureIntro. unfold min_int in *. lia.
  }
  {
    iNext ; iIntros "%". iApply "Post". iFrame "H".
  }
Qed.

End snapclock_int.