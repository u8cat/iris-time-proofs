From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeReceipts.

(* Author: Glen Mével, Jan 17, 2022 *)

Ltac wp_tick_faa := wp_tick ; wp_faa.

Definition make_gen : val :=
  λ: <>,
    let: "count" := ref #0 in
    (λ: <>, FAA "count" #1).



Section Proof.

Context `{!timeReceiptHeapG Σ} (tr_max : nat).

Definition P_def (count : loc) (S : gset Z) : iProp Σ :=
  (∃ (n : nat),
    count ↦ #n ∗ TR n ∗ ⌜∀ x, x ∈ S → x < n⌝
  )%I.

Print Exclusive.
Search _ Exclusive.
Search _ (_ ↦ _)%I.
Search _ (_ ↦ _)%I False%I.

Lemma P_excl count S1 S2 :
  P_def count S1 ∗ P_def count S2 -∗ False.
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as (n1) "(H1 & _)".
  iDestruct "H2" as (n2) "(H2 & _)".
Admitted.

Proposition make_gen_spec :
  TR_invariant tr_max -∗
  {{{ True }}}
  « make_gen #() »
  {{{ (gen_id : val), RET gen_id ;
    ∃ (P : gset Z → iProp Σ),
      P ∅
    ∗ ∀ (S : gset Z),
        {{{ P S }}}
        gen_id #()
        {{{ (id : Z), RET #id ; ⌜id ∉ S⌝ ∗ P ( S ∪ {[id]} ) }}}
  }}}.
Proof.
  iIntros "#TRInv !>" (Φ) "_ Post".
  wp_tick_rec. wp_tick_alloc ℓ. wp_tick_let.
  wp_pures. wp_tick.
  iMod zero_TR as "TR0" =>//.
  wp_value_head.
  iApply "Post". iExists (P_def ℓ). iSplitL.
  {
    iExists 0%nat. iFrame. iIntros (?) ; by rewrite elem_of_empty.
  }
  {
    iIntros (S Ψ) "!# Pre Post".
    iDestruct "Pre" as (n) "(Hℓ & HTR & HS)" ; iDestruct "HS" as %HS.
    wp_rec. wp_tick_faa. iApply "Post".
    iSplitR ; first iPureIntro.
    { naive_solver lia. }
    {
      iExists (n+1)%nat.
      rewrite (_ : n + 1 = (n + 1)%nat) ; last lia.
      rewrite (_ : Datatypes.S n = (n + 1)%nat) ; last lia.
      iIntros "{$Hℓ $HTR} % !% %".
      set_unfold.
      naive_solver lia.
    }
  }
Qed.

End Proof.



Section SimplerProof.

Context `{!timeReceiptHeapG Σ} (tr_max : nat).

Definition P_def' (count : loc) (n : nat) : iProp Σ :=
  (count ↦ #n ∗ TR n)%I.

Print Exclusive.
Search _ Exclusive.
Search _ (_ ↦ _)%I.
Search _ (_ ↦ _)%I False%I.

Lemma P_excl' count n1 n2 :
  P_def' count n1 ∗ P_def' count n2 -∗ False.
Proof.
  iIntros "[H1 H2]".
  iDestruct "H1" as "(H1 & _)".
  iDestruct "H2" as "(H2 & _)".
Admitted.

Proposition make_gen_spec' :
  TR_invariant tr_max -∗
  {{{ True }}}
  « make_gen #() »
  {{{ (gen_id : val), RET gen_id ;
    ∃ (P : nat → iProp Σ),
      P 0%nat
    ∗ ∀ (next_id : nat),
        {{{ P next_id }}}
        gen_id #()
        {{{ RET #next_id ; P (next_id + 1)%nat }}}
  }}}.
Proof.
  iIntros "#TRInv !>" (Φ) "_ Post".
  wp_tick_rec. wp_tick_alloc ℓ. wp_tick_let.
  wp_pures. wp_tick.
  iMod zero_TR as "TR0" =>//.
  wp_value_head.
  iApply "Post". iExists (P_def' ℓ).
  iFrame.
  iIntros (n Ψ) "!# Pre Post".
  iDestruct "Pre" as "(Hℓ & HTR)".
  wp_rec. wp_tick_faa. iApply "Post".
  rewrite (_ : (n + 1)%Z = (n + 1)%nat) ; last lia.
  rewrite (_ : S n = (n + 1)%nat) ; last lia.
  iIntros "{$Hℓ $HTR} % !% %".
Qed.

End SimplerProof.
