From iris.heap_lang Require Import proofmode notation adequacy.
From iris.algebra Require Import auth.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import classes.
From stdpp Require Import namespaces.

Require Import Auth_nat Misc Reduction Tactics.
Require Export Translation Simulation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.



(*
 * Prerequisites on the global monoid Σ
 *)

Class timeCreditHeapPreG Σ := {
  timeCreditHeapPreG_heapPreG :> heapPreG Σ ;
  timeCreditHeapPreG_inG :> inG Σ (authR natUR) ;
}.

Class timeCreditLoc := {
  timeCreditLoc_loc : loc ;
}.

Class timeCreditHeapG Σ := {
  timeCreditHeapG_heapG :> heapG Σ ;
  timeCreditHeapG_inG :> inG Σ (authR natUR) ;
  timeCreditHeapG_loc :> timeCreditLoc ;
  timeCreditHeapG_name : gname ;
}.

Local Notation γ := timeCreditHeapG_name.
Local Notation ℓ := timeCreditLoc_loc.



(*
 * Implementation and specification of `TC` and `tick`
 *)

Section Tick.

  Context `{timeCreditLoc}.

  (* This code is irrelevant for tick_spec but has to be unsafe for proving
   * the safety theorem: *)
  Definition fail : val :=
    λ: <>, #() #().

(*
  Definition tick : val :=
    λ: "x", if: ! #ℓ < #1 then fail #() else (FAA #ℓ (- #1) ;; "x").
*)
  Definition tick : val :=
    tick fail ℓ.

End Tick.



Section TickSpec.

  Context `{timeCreditHeapG Σ}.

  Definition TC (n : nat) : iProp Σ :=
    own γ (◯nat n).

  Lemma TC_plus m n :
    TC (m + n) ≡ (TC m ∗ TC n)%I.
  Proof. by rewrite /TC auth_frag_op own_op. Qed.
  Lemma TC_succ n :
    TC (S n) ≡ (TC 1%nat ∗ TC n)%I.
  Proof. by rewrite (eq_refl : S n = 1 + n)%nat TC_plus. Qed.

  Lemma TC_timeless n :
    Timeless (TC n).
  Proof. exact _. Qed.

  (* note: IntoAnd false will become IntoSep *)
  Global Instance into_sep_TC_plus m n p : IntoAnd p (TC (m + n)) (TC m) (TC n).
  Proof. rewrite /IntoAnd TC_plus ; iIntros "[Hm Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TC_plus m n : FromAnd false (TC (m + n)) (TC m) (TC n).
  Proof. by rewrite /FromAnd TC_plus. Qed.
  Global Instance into_sep_TC_succ n p : IntoAnd p (TC (S n)) (TC 1) (TC n).
  Proof. rewrite /IntoAnd TC_succ ; iIntros "[H1 Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TC_succ n : FromAnd false (TC (S n)) (TC 1) (TC n).
  Proof. by rewrite /FromAnd [TC (S n)] TC_succ. Qed.

  Definition timeCreditN := nroot .@ "timeCredit".

  Definition TICKCTXT : iProp Σ :=
    inv timeCreditN (∃ (m:nat), ℓ ↦ #m ∗ own γ (●nat m))%I.

  Theorem tick_spec s E e v :
    ↑timeCreditN ⊆ E →
    IntoVal e v →
    TICKCTXT -∗
    {{{ ▷ TC 1 }}} tick e @ s ; E {{{ RET v ; True }}}.
  Proof.
    intros ? <- % of_to_val. iIntros "#Inv" (Ψ) "!# Hγ◯ HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value n of location ℓ: *)
    wp_bind (! _)%E ;
    iInv timeCreditN as (n) ">(Hℓ & Hγ●)" "InvClose".
    wp_load.
    (* deduce that n ≥ 1, because we hold a time credit: *)
    iDestruct (own_auth_nat_le with "Hγ● Hγ◯") as %I.
    (* close the invariant: *)
    iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether n ≤ 0: *)
    wp_op ; destruct (bool_decide (n ≤ 0)) eqn:Im ; wp_if.
    (* — if n ≤ 0 then this is absurd, because we hold a time credit: *)
    - apply Is_true_eq_left, bool_decide_spec in Im.
      exfalso ; lia.
    (* — otherwise: *)
    - clear Im.
      wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
      iInv timeCreditN as (n') ">(Hℓ & Hγ●)" "InvClose".
      (* test whether the value ℓ is still k, by comparing n with n': *)
      destruct (nat_eq_dec n n') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with n−1 instead of n: *)
        replace (Z.of_nat n - 1) with (Z.of_nat (n - 1)%nat) by lia.
        iMod (auth_nat_update_decr _ _ _ 1 with "Hγ● Hγ◯") as "[Hγ● Hγ◯]" ; first done.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. by iApply "HΨ".
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ Hℓ Hγ● ]") as "_" ; [ by auto with iFrame | iModIntro ] ; clear dependent n.
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ◯ HΨ").
  Qed.

  Theorem tick_spec_simple v :
    TICKCTXT -∗
    {{{ TC 1 }}} tick v {{{ RET v ; True }}}.
  Proof.
    iIntros "#Hinv" (Ψ) "!# HTC HΨ".
    by iApply (tick_spec with "Hinv [HTC//] HΨ").
  Qed.

End TickSpec.



(*
 * Operation semantics of `tick`
 *)

Section Tick_lemmas.

  Context `{timeCreditLoc}.

  (* Semantics in the “successful” case. *)

  Lemma exec_tick_success n v σ :
    prim_exec  (tick v) (<[ℓ := #(S n)]> σ)  v (<[ℓ := #n]> σ)  [].
  Proof. by apply exec_tick_success. Qed.

(* MERGE: to be merged into Iris: *)
  Definition head_stuck e σ :=
  to_val e = None ∧ head_irreducible e σ.
  Lemma head_stuck_stuck e σ :
    head_stuck e σ → sub_redexes_are_values e → stuck e σ.
  Proof.
    intros [] ?. split; first done.
    by apply prim_head_irreducible.
  Qed.
(* /MERGE *)

  (* Semantics in the “failing” case. *)

  Lemma not_safe_tick v σ :
    ¬ safe (tick v) (<[ℓ := #0]> σ).
  Proof.
    assert (prim_exec  (tick v) (<[ℓ := #0]> σ)  (#() #()) (<[ℓ := #0]> σ)  []) as Hexec.
    {
      unlock tick Simulation.tick.
      apply prim_exec_cons_nofork
      with (
        let: "k" := ! #ℓ in
        if: "k" ≤ #0 then
          fail #()
        else if: CAS #ℓ "k" ("k" - #1) then
          v
        else
          tick v
      )%E  (<[ℓ := #0]> σ).
      {
        prim_step ; first exact _.
        replace (rec: "tick" "x" := _)%E with (of_val tick) by by unlock tick Simulation.tick.
        unfold subst ; simpl ; fold subst.
        rewrite ! subst_is_closed_nil // ; apply is_closed_of_val.
      }
      apply prim_exec_cons_nofork
      with (
        let: "k" := #0 in
        if: "k" ≤ #0 then
          fail #()
        else if: CAS #ℓ "k" ("k" - #1) then
          v
        else
          tick v
      )%E  (<[ℓ := #0]> σ).
      {
        prim_step.
        apply lookup_insert.
      }
      apply prim_exec_cons_nofork
      with (
        if: #0 ≤ #0 then
          fail #()
        else if: CAS #ℓ #0 (#0 - #1) then
          v
        else
          tick v
      )%E  (<[ℓ := #0]> σ).
      {
        prim_step ; first exact _.
        unfold subst ; simpl ; fold subst.
        rewrite ! subst_is_closed_nil // ; apply is_closed_of_val.
      }
      apply prim_exec_cons_nofork
      with (
        if: #true then
          fail #()
        else if: CAS #ℓ #0 (#0 - #1) then
          v
        else
          tick v
      )%E  (<[ℓ := #0]> σ).
      {
        prim_step.
      }
      apply prim_exec_cons_nofork
      with (fail #())%E (<[ℓ := #0]> σ).
      {
        prim_step.
      }
      apply prim_exec_cons_nofork
      with (#() #())%E (<[ℓ := #0]> σ).
      {
        unlock fail.
        by prim_step.
      }
      apply prim_exec_nil.
    }
    assert (¬ safe (#() #()) (<[ℓ := #0]> σ)) as Hnotsafe.
    {
      apply stuck_not_safe, head_stuck_stuck, ectxi_language_sub_redexes_are_values.
      - split ; first done. inversion 1.
      - intros [] ; try discriminate 1 ; inversion 1 ; by eauto.
    }
    intros Hsafe. eapply Hnotsafe, safe_exec_nofork, prim_exec_exec ; eassumption.
  Qed.
  Lemma not_safe_tick' e v σ :
    to_val e = Some v →
    ¬ safe (tick e) (<[ℓ := #0]> σ).
  Proof.
    intros <- % of_to_val. apply not_safe_tick.
  Qed.

End Tick_lemmas.



(*
 * Simulation
 *)

Notation tctranslation := (translation tick).
Notation tctranslationV := (translationV tick).
Notation tctranslationS := (translationS tick).
Notation tctranslationKi := (translationKi tick).
Notation tctranslationK := (translationK tick).

Notation "E« e »" := (tctranslation e%E).
Notation "V« v »" := (tctranslationV v%V).
Notation "Ki« ki »" := (tctranslationKi ki).
Notation "K« K »" := (tctranslationK K).
Notation "S« σ »" := (tctranslationS σ%V).
Notation "S« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (tctranslationS σ%V)).
Notation "T« t »" := (tctranslation <$> t%E).

Notation "« e »" := (tctranslation e%E).
Notation "« e »" := (tctranslation e%E) : expr_scope.
Notation "« v »" := (tctranslationV v%V) : val_scope.

(* for some reason, these notations make parsing fail,
 * even if they only regard printing… *)
(*
Notation "« e »" := (tctranslation e%E) (only printing).
Notation "« v »" := (tctranslationV v%V) (only printing).
Notation "« ki »" := (tctranslationKi ki) (only printing).
Notation "« K »" := (tctranslationK K) (only printing).
Notation "« σ »" := (tctranslationS σ%V) (only printing).
Notation "« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (tctranslationS σ%V)) (only printing).
Notation "« t »" := (tctranslation <$> t%E) (only printing).
*)

Section Simulation.

  Context `{Hloc : timeCreditLoc}.

  (* Simulation in the “successful” case. *)

  Definition simulation_exec_success := simulation_exec_success _ tick exec_tick_success.
  Definition simulation_exec_success' := simulation_exec_success' _ tick exec_tick_success.

  (* Simulation in the “failing” case. *)

  Local Ltac not_safe_tick :=
    lazymatch goal with
    | |- ¬ safe ?e _ =>
        reshape_expr e ltac:(fun K e' =>
          apply not_safe_fill' with K e' ; first reflexivity ;
          eapply not_safe_tick'
        )
    end ;
    by simpl_to_of_val.

  Lemma simulation_head_step_failure e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    destruct 1 as
      [ (* BetaS *) f x e1 e2 v2 e' σ  Hval_e2 Hclosed_e1 ->
      | | | | | | | |
      | (* ForkS *) e1 σ
      | | | | | | ] ;
    cbn [translation] ;
    rewrite_into_values ; rewrite ? translation_of_val ;
    try not_safe_tick.
    (* BetaS f x e1 e2 v2 e' σ : *)
    - assert (Closed (f :b: x :b: []) « e1 ») by by apply is_closed_translation.
      not_safe_tick.
    (* ForkS e σ : *)
    - eapply not_safe_prim_step ; last prim_step.
      eapply (not_safe_tick #()).
  Qed.

  Lemma simulation_prim_step_failure e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [ K e1' e2' -> -> H ].
    rewrite translation_fill.
    by eapply not_safe_fill, simulation_head_step_failure.
  Qed.

  Lemma simulation_step_failure t1 σ1 t2 σ2 :
    step (t1, σ1) (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [e1 σ1_ e2 σ2_ efs t t' E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <-.
    exists e1 ; split ; first set_solver.
    by eapply simulation_prim_step_failure.
  Qed.

  Local Lemma simulation_exec_failure_now n t1 σ1 t2 σ2 :
    nsteps step (S n) (t1, σ1) (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    make_eq (S n) as Sn En.
    make_eq (t1, σ1) as config1 E1.
    destruct 1 as [ ? | ? ? [] ? ? _ ], E1.
    - discriminate En.
    - by eapply simulation_step_failure.
  Qed.

  Lemma simulation_exec_failure m n e1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    is_closed [] e1 →
    nsteps step (m + S n) ([e1], σ1) (t2, σ2) →
    ¬ safe «e1» S«σ1, m».
  Proof.
    intros Hℓ Hclosed Hnsteps.
    assert (
      ∃ t3 σ3,
        rtc step (T«[e1]», S«σ1, m») (T«t3», S«σ3, 0») ∧
        ∃ e3, e3 ∈ t3 ∧
        ¬ safe «e3» S«σ3, 0»
    ) as (t3 & σ3 & Hsteps & e3 & E3 & Hsafe).
    {
      apply nsteps_split in Hnsteps as ((t3, σ3) & Hnsteps1to3 & Hnsteps3to2).
      exists t3, σ3 ; repeat split.
      - assert (σ3 !! ℓ = None) by (eapply loc_fresh_in_dom_nsteps ; cycle 1 ; eassumption).
        assert (Forall (is_closed []) [e1]) by auto.
        replace m with (m+0)%nat by lia.
        apply simulation_exec_success ; assumption.
      - by eapply simulation_exec_failure_now.
    }
    apply (elem_of_list_fmap_1 tctranslation) in E3.
    eapply not_safe_exec ; eassumption.
  Qed.

End Simulation.



Section Soundness.

  (* assuming the safety of the translated expression,
   * a proof that the computation time of the original expression is bounded. *)

  Local Lemma gt_sum m n :
    (m > n)%nat → ∃ (k : nat), m = (n + S k)%nat.
  Proof.
    intro. exists (m - S n)%nat. lia.
  Qed.
  Lemma safe_tctranslation__bounded `{timeCreditLoc} m e σ t2 σ2 n :
    is_closed [] e →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    nsteps step n ([e], σ) (t2, σ2) →
    (n ≤ m)%nat.
  Proof.
    intros Hclosed Hfresh Hsafe Hnsteps.
    (* reasoning by contradiction: assume (n > m), ie. (n = m + S k) for some k: *)
    apply not_gt ; intros [k ->] % gt_sum.
    (* apply the simulation lemma: *)
    by eapply simulation_exec_failure.
  Qed.

  (* assuming the safety of the translated expression,
   * a proof that the original expression is safe. *)

(*
  Lemma safe_tctranslation__safe_here `{timeCreditLoc} m e σ :
    is_closed [] e →
    loc_fresh_in_expr ℓ e →
    safe «e» S«σ, m» →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros Hclosed Hfresh Hsafe.
    (* case analysis on whether e is a value… *)
    destruct (to_val e) as [ v | ] eqn:Hnotval.
    (* — if e is a value, then we get the result immediately: *)
    - left. eauto.
    (* — if e is not a value, then we show that it is reducible: *)
    - right.
      (* we decompose e into a maximal evaluation context K and a head-redex: *)
      pose proof (not_val_fill_active_item _ Hclosed Hnotval) as He ; clear Hclosed Hnotval.
      destruct He as [ (K & e1 & ->) | (K & ki & v & -> & Hactive) ].
      (* — either e = K[Fork e1]: *)
      + (* then we easily derive a reduction from e: *)
        eexists _, _, _. apply Ectx_step', ForkS.
      (* — or e = K[ki[v]] where ki is an active item: *)
      + (* it is enough to show that ki[v] is reducible: *)
        apply loc_fresh_in_expr_fill_inv in Hfresh ;
        rewrite -> translation_fill in Hsafe ; apply safe_fill_inv in Hsafe ;
        apply reducible_fill ;
        clear K.
        (* we deduce the reducibility of ki[v] from that of «ki»[«v»]: *)
        eapply active_item_translation_reducible ; [ done | done | ].
        (* remind that « ki[v] » = «ki»[tick «v»]: *)
        rewrite -> translation_fill_item_active in Hsafe ; last done.
        (* we have that «ki»[tick «v»] reduces to «ki»[«v»]
         * (thanks to the safety hypothesis, m ≥ 1 and ‘tick’ can be run): *)
        assert (
          prim_exec (fill_item Ki«ki» (tick V«v»)) S«σ, m»
                    (fill_item Ki«ki» V«v»)        S«σ, m-1» []
        ) as Hsteps % prim_exec_exec.
        {
          assert (fill [Ki«ki»] = fill_item Ki«ki») as E by reflexivity ; destruct E.
          apply prim_exec_fill. apply safe_fill_inv in Hsafe.
          destruct m as [ | m ] ; first (exfalso ; eapply not_safe_tick, Hsafe).
          replace (S m - 1)%nat with m by lia.
          apply exec_tick_success.
        }
        (* using the safety of «ki»[tick «v»], we proceed by case analysis… *)
        eapply Hsafe in Hsteps as [ Hisval | Hred ] ; auto using elem_of_list_here.
        (* — either «ki»[«v»] is a value: this is not possible because ki is active. *)
        * simpl in Hisval. rewrite active_item_not_val in Hisval ;
          [ by apply is_Some_None in Hisval | by apply is_active_translationKi ].
        (* — or «ki»[«v»] reduces to something: this is precisely what we need. *)
        * exact Hred.
  Qed.
  Lemma safe_tctranslation__safe `{timeCreditLoc} m e σ t2 σ2 e2 :
    is_closed [] e →
    loc_fresh_in_expr ℓ e2 →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    rtc step ([e], σ) (t2, σ2) →
    e2 ∈ t2 →
    is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    intros Hclosed Hℓe Hℓσ Hsafe [n Hnsteps] % rtc_nsteps He2.
    assert (n ≤ m)%nat by by eapply safe_tctranslation__bounded.
    assert (safe «e2» S«σ2, m-n») as Hsafe2.
    {
      eapply safe_exec.
      - eapply elem_of_list_fmap_1. eassumption.
      - eassumption.
      - change [«e»] with T«[e]». apply simulation_exec_success' ; auto.
    }
    assert (is_closed [] e2) as Hclosede2.
    {
      assert (Forall (is_closed []) t2) as Hclosedt2
        by eauto using nsteps_rtc, is_closed_exec.
      by eapply Forall_forall in Hclosedt2 ; last exact He2.
    }
    by eapply safe_tctranslation__safe_here.
  Qed.

  (* assuming the adequacy of the translated expression,
   * a proof that the original expression has adequate results. *)

  Lemma adequate_tctranslation__adequate_result `{timeCreditLoc} m (φ : val → Prop) e σ t2 σ2 v2 :
    is_closed [] e →
    σ2 !! ℓ = None →
    adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV) →
    rtc step ([e], σ) (of_val v2 :: t2, σ2) →
    φ v2.
  Proof.
    intros Hclosed Hfresh Hadq [n Hnsteps] % rtc_nsteps.
    assert (safe «e» S«σ, m») as Hsafe by by eapply safe_adequate.
    assert (n ≤ m)%nat by by eapply safe_tctranslation__bounded.
    replace (φ v2) with ((φ ∘ invtranslationV) (tctranslationV v2))
      by (simpl ; by rewrite invtranslationV_translationV).
    eapply adequate_result ; first done.
    change [«e»%E] with T«[e]».
    replace (of_val «v2» :: _) with (T«of_val v2 :: t2») by by rewrite - translation_of_val.
    eapply simulation_exec_success' ; eauto.
  Qed.

  (* now let’s combine the three results. *)

  Lemma adequate_tctranslation__adequate_and_bounded m (φ : val → Prop) e σ :
    is_closed [] e →
    (∀ `{timeCreditLoc}, adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV)) →
    adequate NotStuck e σ φ  ∧  bounded_time e σ m.
  Proof.
    intros Hclosed Hadq.
    split ; first split.
    (* (1) adequate result: *)
    - intros t2 σ2 v2 Hsteps.
      (* build a location ℓ which is not in the domain of σ2: *)
      pose (Build_timeCreditLoc (fresh (dom (gset loc) σ2))) as Hloc.
      assert (σ2 !! ℓ = None)
        by (simpl ; eapply not_elem_of_dom, is_fresh).
      by eapply adequate_tctranslation__adequate_result.
    (* (2) safety: *)
    - intros t2 σ2 e2 _ Hsteps He2.
      (* build a location ℓ which is fresh in e2 and in the domain of σ2: *)
      pose (set1 := loc_set_of_expr e2 : gset loc).
      pose (set2 := dom (gset loc) σ2 : gset loc).
      pose (Build_timeCreditLoc (fresh (set1 ∪ set2))) as Hloc.
      eassert (ℓ ∉ set1 ∪ set2) as [Hℓ1 Hℓ2] % not_elem_of_union
        by (unfold ℓ ; apply is_fresh).
      assert (loc_fresh_in_expr ℓ e2)
        by by apply loc_not_in_set_is_fresh.
      assert (σ2 !! ℓ = None)
        by by (simpl ; eapply not_elem_of_dom).
      specialize (Hadq Hloc) as Hsafe % safe_adequate.
      by eapply safe_tctranslation__safe.
    (* (3) bounded execution time: *)
    - intros t2 σ2 k.
      (* build a location ℓ which is not in the domain of σ2: *)
      pose (Build_timeCreditLoc (fresh (dom (gset loc) σ2))) as Hloc.
      assert (σ2 !! ℓ = None)
        by (unfold ℓ ; eapply not_elem_of_dom, is_fresh).
      specialize (Hadq Hloc) as Hsafe % safe_adequate.
      by eapply safe_tctranslation__bounded.
  Qed.

  (* finally, derive the adequacy assumption from a Hoare triple in Iris. *)

  Lemma spec_tctranslation__adequate {Σ} m (ψ : val → Prop) e :
    (∀ `{timeCreditHeapG Σ},
      TICKCTXT -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{timeCreditHeapPreG Σ} `{timeCreditLoc} σ, adequate NotStuck «e» S«σ,m» ψ.
  Proof.
    intros Hspec HpreG Hloc σ.
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
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
    pose (Build_timeCreditHeapG Σ (HeapG Σ _ (GenHeapG _ _ Σ _ _ _ h)) _ _ γ)
      as HtcHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TICKCTXT)%I with "[Hℓ◯ Hγ●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists m.
      unfold mapsto ; destruct mapsto_aux as [_ ->] ; simpl.
      unfold to_gen_heap ; rewrite fmap_insert fmap_empty insert_empty.
      by iFrame.
    }
    iModIntro.
    (* finally, use the user-given specification: *)
    iExists gen_heap_ctx. iFrame "Hh●".
    iApply (Hspec with "Hinv Hγ◯") ; auto.
  Qed.
*)

  Lemma adequate_tctranslation__adequate m (φ : val → Prop) e σ :
    is_closed [] e →
    (∀ `{timeCreditLoc}, adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV)) →
    adequate_n NotStuck m e σ φ.
  Proof.
    intros.
    apply (adequate_translation__adequate (λ ℓ1, @tick {| timeCreditLoc_loc := ℓ1 |})).
    - intro ℓ1.
      rewrite (_ : ℓ1 = @timeCreditLoc_loc {| timeCreditLoc_loc := ℓ1 |}) ; last done.
      apply exec_tick_success.
    - done.
    - intro ℓ1.
      rewrite (_ : ℓ1 = @timeCreditLoc_loc {| timeCreditLoc_loc := ℓ1 |}) ; last done.
      done.
  Qed.

  Lemma adequate_tctranslation__bounded m (φ : val → Prop) e σ :
    is_closed [] e →
    (∀ `{timeCreditLoc}, adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV)) →
    bounded_time e σ m.
  Proof.
    intros Hclosed Hadq.
    (* (3) bounded execution time: *)
    - intros t2 σ2 k.
      (* build a location ℓ which is not in the domain of σ2: *)
      pose (Build_timeCreditLoc (fresh (dom (gset loc) σ2))) as Hloc.
      assert (σ2 !! ℓ = None)
        by (unfold ℓ ; eapply not_elem_of_dom, is_fresh).
      specialize (Hadq Hloc) as Hsafe % safe_adequate.
      by eapply safe_tctranslation__bounded.
  Qed.

  (* now let’s combine the three results. *)

  Lemma adequate_tctranslation__adequate_and_bounded m (φ : val → Prop) e σ :
    is_closed [] e →
    (∀ (k : nat), (k ≥ m)%nat → ∀ `{timeCreditLoc}, adequate NotStuck «e» S«σ, k» (φ ∘ invtranslationV)) →
    adequate NotStuck e σ φ  ∧  bounded_time e σ m.
  Proof.
    intros Hclosed Hadq.
    assert (bounded_time e σ m) as Hbounded
      by (eapply adequate_tctranslation__bounded, Hadq ; [ assumption | lia ]).
    assert (adequate_n NotStuck (m + 1) e σ φ) as Hadqm
      by (apply adequate_tctranslation__adequate, Hadq ; [ assumption | lia ]).
    clear Hadq.
    split ; last done.
    split.
    - intros t2 σ2 v2 [n Hnsteps] % rtc_nsteps.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply adequate_n_result ; try done ; lia.
    - intros t2 σ2 e2 _ [n Hnsteps] % rtc_nsteps He2.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply adequate_n_not_stuck ; try done ; lia.
  Qed.

  (* finally, derive the adequacy assumption from a Hoare triple in Iris. *)

  Lemma spec_tctranslation__adequate {Σ} m (ψ : val → Prop) e :
    (∀ `{timeCreditHeapG Σ},
      TICKCTXT -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{timeCreditHeapPreG Σ} `{timeCreditLoc} σ, ∀ (k : nat), (k ≥ m)%nat → adequate NotStuck «e» S«σ,k» ψ.
  Proof.
    intros Hspec HpreG Hloc σ k Ik.
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (own_alloc (● to_gen_heap (<[ℓ := #k]> σ') ⋅ ◯ to_gen_heap {[ℓ := #k]}))
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
    iMod (auth_nat_alloc k) as (γ) "[Hγ● Hγ◯]".
    (* packing all those bits, build the heap instance necessary to use time credits: *)
    pose (Build_timeCreditHeapG Σ (HeapG Σ _ (GenHeapG _ _ Σ _ _ _ h)) _ _ γ)
      as HtcHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TICKCTXT)%I with "[Hℓ◯ Hγ●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists k.
      unfold mapsto ; destruct mapsto_aux as [_ ->] ; simpl.
      unfold to_gen_heap ; rewrite fmap_insert fmap_empty insert_empty.
      by iFrame.
    }
    iModIntro.
    (* finally, use the user-given specification: *)
    iExists gen_heap_ctx. iFrame "Hh●".
    iDestruct (own_auth_nat_weaken _ _ _ Ik with "Hγ◯") as "Hγ◯".
    iApply (Hspec with "Hinv Hγ◯") ; auto.
  Qed.

  Theorem spec_tctranslation__adequate_and_bounded {Σ} m (φ : val → Prop) e :
    is_closed [] e →
    (∀ `{timeCreditHeapG Σ},
      TICKCTXT -∗
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ `{timeCreditHeapPreG Σ} σ,
      adequate NotStuck e σ φ  ∧  bounded_time e σ m.
  Proof.
    intros Hclosed Hspec HpreG σ.
    apply adequate_tctranslation__adequate_and_bounded ; first done.
    intros k Ik Hloc. by eapply spec_tctranslation__adequate.
  Qed.

  Theorem abstract_spec_tctranslation__adequate_and_bounded {Σ} m (φ : val → Prop) e :
    is_closed [] e →
    (∀ `{heapG Σ} (TC : nat → iProp Σ) (tick : val),
      (∀ m n, TC (m + n)%nat ≡ (TC m ∗ TC n)%I) →
      (∀ n, Timeless (TC n)) →
      (∀ v, {{{ TC 1%nat }}} tick v {{{ RET v ; True }}}) -∗
      {{{ TC m }}} translation tick e {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : heapPreG Σ} {_ : inG Σ (authR natUR)} σ,
      adequate NotStuck e σ φ  ∧  bounded_time e σ m.
  Proof.
    intros Hclosed Hspec HpreG HinG σ.
    (* a record of type (timeCreditHeapPreG Σ) is inferred from HpreG and HinG: *)
    eapply spec_tctranslation__adequate_and_bounded ; try done.
    clear HpreG HinG.
    intros HtcHeapG.
    specialize (Hspec _ TC tick).
    iIntros "#Hinv".
    iApply Hspec.
    - exact TC_plus.
    - iIntros (v). iApply (tick_spec_simple with "Hinv").
  Qed.

End Soundness.



(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Section Tactics.

From iris.proofmode Require Import coq_tactics tactics.
From iris.program_logic Require Export weakestpre.
From iris.heap_lang Require Export tactics lifting.
Import uPred.
Context {Σ : gFunctors}.
Implicit Types Φ : val → iProp Σ.
Implicit Types Δ : envs (iResUR Σ).

  (* concrete version: *)
  Lemma tac_wp_tick `{timeCreditHeapG Σ} Δ Δ' Δ'' s E i j n K e v Φ :
    ↑timeCreditN ⊆ E →
    IntoVal e v →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ  = Some (true, TICKCTXT) →
    envs_lookup j Δ' = Some (false, TC (S n)) →
    envs_simple_replace j false (Esnoc Enil j (TC n)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K v @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (App tick e) @ s; E {{ Φ }}).
  Proof.
    unfold envs_entails => HsubsetE ????? Hentails''.
    rewrite envs_lookup_persistent_sound // persistently_elim. apply wand_elim_r'.
    rewrite -wp_bind.
    eapply wand_apply ; first by (iIntros "HTC1 HΦ #Htick" ; iApply (tick_spec with "Htick HTC1 HΦ")).
    rewrite into_laterN_env_sound -later_sep /=. apply later_mono.
    rewrite envs_simple_replace_sound // ; simpl.
    rewrite TC_succ -sep_assoc. apply sep_mono_r.
    iIntros "[HTC Hwand] _". iApply Hentails''. iApply "Hwand" ; by iFrame.
  Qed.

(*
  (* abstract version: *)
  Lemma tac_wp_tick_abstr `{heapG Σ} (TC : nat → iProp Σ) (tick : val) Δ Δ' Δ'' s E i j n K e v Φ :
    IntoVal e v →
    MaybeIntoLaterNEnvs 1 Δ Δ' →
    envs_lookup i Δ' = Some (true,  ∀ (v : val), {{{ TC 1%nat }}} tick v @ s ; E {{{ RET v ; True }}})%I →
    envs_lookup j Δ' = Some (false, TC (S n)) →
    envs_simple_replace i false (Esnoc Enil j (TC n)) Δ' = Some Δ'' →
    envs_entails Δ'' (WP fill K e @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (App tick e) @ s; E {{ Φ }}).
  Admitted.
*)

End Tactics.

Ltac wp_tick :=
  let solve_TICKCTXT _ :=
    iAssumptionCore || fail "wp_tick: cannot find TICKCTXT" in
  let solve_TC _ :=
    iAssumptionCore || fail "wp_tick: cannot find TC (S _)" in
  let finish _ :=
    wp_expr_simpl ; try first [ wp_pure (Seq (Lit LitUnit) _) | wp_value_head ] in
  iStartProof ;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first
        [ reshape_expr e ltac:(fun K e' =>
            eapply (tac_wp_tick _ _ _ _ _ _ _ _ K) ; [ | exact _ | ..]
          )
        | fail 1 "wp_tick: cannot find 'tick ?v' in" e ] ;
      [ try solve_ndisj
      | exact _
      | solve_TICKCTXT ()
      | solve_TC ()
      | env_cbv ; reflexivity
      | finish () ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      fail "wp_tick is not implemented for twp"
  | _ => fail "wp_tick: not a 'wp'"
  end.