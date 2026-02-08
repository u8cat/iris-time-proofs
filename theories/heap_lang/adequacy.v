From iris.program_logic Require Export weakestpre adequacy.
From iris.algebra Require Import auth.
From iris_time Require Import Auth_nat.
From iris_time.heap_lang Require Import proofmode notation.
From iris.proofmode Require Import proofmode.
Set Default Proof Using "Type".

Class heapGpreS Σ := HeapGpreS {
  #[global] heap_preG_iris :: invGpreS Σ;
  #[global] heap_preG_heap :: gen_heapGpreS loc val Σ;
  #[local] heap_preG_nat :: inG Σ (authR natUR);
}.

Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val; GFunctor (authR natUR)].
Global Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Definition heap_adequacy Σ `{heapGpreS Σ} s e σ φ :
  (∀ `{heapGS Σ}, TC (σ.(tick_counter)) ⊢ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (auth_nat_alloc σ.(tick_counter)) as (γ) "[Htc● Htc◯]".
  iModIntro.
  iExists (λ σ κs, (gen_heap_interp σ.(heap) ∗ own γ (●nat σ.(tick_counter)))%I),
    (λ _, True%I). iFrame.
  iApply (Hwp (HeapGS _ _ _ _ _)). iFrame.
Qed.
