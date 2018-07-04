From iris.heap_lang Require Import proofmode notation adequacy.
From iris.algebra Require Import auth.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import classes.
From stdpp Require Import namespaces.

Require Import Auth_nat TimeCredits.

Local Notation γ := timeCreditHeapG_name.
Local Notation ℓ := timeCreditLoc_loc.

Lemma gen_heap_ctx_mapsto {Σ : gFunctors} {Hgen : gen_heapG loc val Σ} (σ : state) (l : loc) (v v' : val) :
  σ !! l = Some v →
  gen_heap_ctx σ -∗
  l ↦ v' -∗
  ⌜v = v'⌝.
Proof.
  iIntros (Hσ) "Hheap Hl".
  rewrite /gen_heap_ctx /=.
  unfold mapsto ; destruct mapsto_aux as [_->] ; rewrite /mapsto_def /=.
  iDestruct (own_valid_2 with "Hheap Hl") as %H.
  iPureIntro.
  assert (CmraDiscrete (gen_heapUR loc val)) as Hdiscrete by apply _.
  apply ((auth_valid_discrete_2 (H:=Hdiscrete))) in H as [H _].
  apply gen_heap_singleton_included in H.
  pose proof (eq_stepl Hσ H) as E. by injection E.
Qed.

  Lemma spec_tctranslation__bounded {Σ} m (ψ : val → Prop) e :
    (∀ `{timeCreditHeapG Σ},
      TICKCTXT -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{!timeCreditLoc} `{!timeCreditHeapPreG Σ} σ1 t2 σ2 (z : Z),
      rtc step ([«e»], S«σ1, m») (T«t2», S«σ2, z») →
      0 ≤ z.
  Proof.
    intros Hspec Hloc HtcPreG σ1 t2 σ2 z Hsteps.
    (* apply the invariance result. *)
    apply (wp_invariance Σ _ NotStuck «e» S«σ1,m» T«t2» S«σ2,z») ; simpl ; last assumption.
    intros HinvG.
    (* … now we have to prove a WP for some state interpretation, for which
     * we settle the needed invariant TICKCTXT. *)
    set σ' := S«σ1».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (own_alloc (● to_gen_heap (<[ℓ := #m]> σ') ⋅ ◯ to_gen_heap {[ℓ := #m]}))
      as (h) "[Hh● Hℓ◯]".
    {
      apply auth_valid_discrete_2 ; split.
      - rewrite - insert_delete ; set σ'' := delete ℓ σ'.
        unfold to_gen_heap ; rewrite 2! fmap_insert fmap_empty insert_empty.
        exists (to_gen_heap σ'').
        rewrite (@gmap.insert_singleton_op _ _ _ _ (to_gen_heap σ'')) //.
        rewrite lookup_fmap ; apply fmap_None, lookup_delete.
      - apply to_gen_heap_valid.
    }
    (* allocate the ghost state associated with ℓ: *)
    iMod (auth_nat_alloc m) as (γ) "[Hγ● Hγ◯]".
    (* packing all those bits, build the heap instance necessary to use time credits: *)
    destruct HtcPreG as [[HinvPreG [HgenHeapPreInG]] HinG] ; simpl ; clear HinvPreG.
    pose (Build_timeCreditHeapG Σ (HeapG Σ HinvG (GenHeapG _ _ Σ _ _ HgenHeapPreInG h)) HinG _ γ)
      as HtcHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TICKCTXT)%I with "[Hℓ◯ Hγ●]" as "> #Hinv".
    {
      iApply inv_alloc.
      iExists m.
      unfold mapsto ; destruct mapsto_aux as [_ ->] ; simpl.
      unfold to_gen_heap ; rewrite fmap_insert fmap_empty insert_empty.
      by iFrame.
    }
    (* finally, use the user-given specification: *)
    iModIntro. iExists gen_heap_ctx. iFrame "Hh●".
    iSplitL ; first (iApply (Hspec with "Hinv Hγ◯") ; auto).
    (* it remains to prove that the interpretation of the final state, along
     * with the invariant, implies the inequality… *)
    iIntros "Hheap2".
    (* open the invariant: *)
    iInv timeCreditN as (m') ">[Hc Hγ●]" "InvClose".
    (* derive that z = m' (that is, the relative integer is in fact a natural integer): *)
    iDestruct (gen_heap_ctx_mapsto with "Hheap2 Hc") as %Eq ; first (by apply lookup_insert) ;
    injection Eq as ->.
    (* close the invariant (in fact, this is not required): *)
    iMod ("InvClose" with "[-]") as "_" ; first by auto with iFrame.
    (* conclude: *)
    iMod (fupd_intro_mask' ⊤ ∅) as "_" ; first done. iPureIntro.
    lia.
  Qed.