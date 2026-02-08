From iris_time Require Import Base.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import coq_tactics.
From iris_time.heap_lang Require Export adequacy.
From iris_time.heap_lang Require Import proofmode notation lang.
From iris_time Require Import Auth_nat Reduction Tactics.
From iris_time Require Export Simulation.
Import uPred.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.

(*
 * Operational semantics of `tick`
 *)

Section Tick_lemmas.

  (* Semantics in the “successful” case. *)

  (* Already proved in Simulation *)
  (* Lemma exec_tick_success n v σ :
    prim_exec  (Tick v) (state_set_tick_counter (S n) σ)  v (state_set_tick_counter n σ)  [].
  Proof. by apply exec_tick_success. Qed. *)

  (* Semantics in the “failing” case. *)

  Lemma not_safe_tick v σ :
    ¬ safe (Tick v) (state_set_tick_counter 0 σ).
  Proof.
    apply stuck_not_safe, base_stuck_stuck, ectxi_language_sub_redexes_are_values.
    - split; first done. inversion 1. simplify_eq.
    - intros []; try discriminate 1; inversion 1; by eauto.
  Qed.

End Tick_lemmas.



(*
 * Simulation
 *)

Section Simulation.

  (* Simulation in the “successful” case. *)

  (* Definition simulation_exec_success := simulation_exec_success fail.
  Definition simulation_exec_success' := simulation_exec_success' fail. *)

  (* Simulation in the “failing” case. *)

  Local Ltac not_safe_tick :=
    lazymatch goal with
    | |- ¬ safe ?e _ =>
        reshape_expr false e ltac:(fun K e' =>
          apply not_safe_fill' with K e' ; first reflexivity ;
          eapply not_safe_tick
        )
    end ;
    done.

  Lemma simulation_head_step_failure e1 σ1 κ e2 σ2 efs :
    head_step e1 σ1 κ e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    destruct 1 as
      [(* RecS *) f x e σ
      | | | | | | | | | | | |
      | (* ForkS *) e1 σ
      | | | | | | | ] ;
    simpl_trans ;
    try not_safe_tick.
    (* RecS f x e σ : *)
    - eapply not_safe_prim_step; last prim_step.
      eapply not_safe_tick.
    (* ForkS e σ : *)
    - eapply not_safe_prim_step ; last prim_step.
      eapply not_safe_tick.
  Qed.

  Lemma simulation_prim_step_failure e1 σ1 κ e2 σ2 efs :
    prim_step e1 σ1 κ e2 σ2 efs →
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [ K e1' e2' -> -> H ].
    rewrite translation_fill.
    by eapply not_safe_fill, simulation_head_step_failure.
  Qed.

  Lemma simulation_step_failure t1 σ1 κ t2 σ2 :
    step (t1, σ1) κ (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    intros [e1 σ1_ e2 σ2_ efs t t' E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <-.
    exists e1 ; split ; first set_solver.
    by eapply simulation_prim_step_failure.
  Qed.

  Local Lemma simulation_exec_failure_now n t1 σ1 t2 σ2 :
    relations.nsteps erased_step (S n) (t1, σ1) (t2, σ2) →
    ∃ e1, e1 ∈ t1 ∧
    ¬ safe «e1» S«σ1, 0».
  Proof.
    make_eq (S n) as Sn En.
    make_eq (t1, σ1) as config1 E1.
    destruct 1 as [ ? | ? ? [] ? [? ?] _ ], E1.
    - discriminate En.
    - by eapply simulation_step_failure.
  Qed.

  Lemma simulation_exec_failure m n e1 σ1 t2 σ2 :
    tick_free_config ([e1], σ1) →
    relations.nsteps erased_step (m + S n) ([e1], σ1) (t2, σ2) →
    ¬ safe «e1» S«σ1, m».
  Proof.
    intros Htf Hnsteps.
    assert (
      ∃ t3 σ3,
        rtc erased_step (T«[e1]», S«σ1, m») (T«t3», S«σ3, 0») ∧
        ∃ e3, e3 ∈ t3 ∧
        ¬ safe «e3» S«σ3, 0»
    ) as (t3 & σ3 & Hsteps & e3 & E3 & Hsafe).
    {
      apply nsteps_split in Hnsteps as ((t3, σ3) & Hnsteps1to3 & Hnsteps3to2).
      exists t3, σ3 ; repeat split.
      - replace m with (m+0)%nat by lia.
        apply simulation_exec_success ; assumption.
      - by eapply simulation_exec_failure_now.
    }
    apply (list_elem_of_fmap_2 translation) in E3.
    eapply not_safe_exec ; eassumption.
  Qed.

End Simulation.



Section Soundness.

  (* See also `TimeCreditsAltProofs.v` *)

  (* assuming the safety of the translated expression,
   * a proof that the computation time of the original expression is bounded. *)

  Local Lemma gt_sum m n :
    (m > n)%nat → ∃ (k : nat), m = (n + S k)%nat.
  Proof.
    intro. exists (m - S n)%nat. lia.
  Qed.
  Lemma safe_tctranslation__bounded m e σ t2 σ2 n :
    tick_free_config ([e], σ) →
    safe «e» S«σ, m» →
    relations.nsteps erased_step n ([e], σ) (t2, σ2) →
    (n ≤ m)%nat.
  Proof.
    intros Htf Hsafe Hnsteps.
    (* reasoning by contradiction: assume (n > m), ie. (n = m + S k) for some k: *)
    apply not_gt ; intros [k ->] % gt_sum.
    (* apply the simulation lemma: *)
    by eapply simulation_exec_failure.
  Qed.

  Lemma adequate_tctranslation__bounded m φ e σ :
    tick_free_config ([e], σ) →
    (adequate NotStuck «e» S«σ, m» (λ v σ, φ (invtranslationV v))) →
    bounded_time e σ m.
  Proof.
    intros Htf Hadq.
    intros t2 σ2 k.
    destruct Hadq as [_ Hsafe].
    by eapply safe_tctranslation__bounded.
  Qed.

  (* Definition adequate_tctranslation__nadequate := adequate_translation__nadequate fail. *)

  (* now let’s combine the three results. *)

  Lemma adequate_tctranslation__adequate_and_bounded m φ e σ :
    tick_free_config ([e],σ) →
    (∀ (k : nat), (k ≥ m)%nat →
      adequate NotStuck «e» S«σ, k» (λ v σ, φ (invtranslationV v))
    ) →
    adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Htf Hadq.
    assert (bounded_time e σ m) as Hbounded.
      by (eapply adequate_tctranslation__bounded, Hadq ; [done|lia]).
    assert (nadequate NotStuck (m + 1) e σ φ) as Hadqm
      by (apply adequate_translation__nadequate, Hadq ; [done|lia]).
    clear Hadq.
    split ; last done.
    split.
    - intros t2 σ2 v2 [n Hnsteps] % rtc_nsteps.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply nadequate_result ; try done ; lia.
    - intros t2 σ2 e2 _ [n Hnsteps] % rtc_nsteps He2.
      assert (n ≤ m)%nat as Inm by by eapply Hbounded.
      eapply nadequate_not_stuck ; try done ; lia.
  Qed.

  (* finally, derive the adequacy assumption from a Hoare triple in Iris. *)

  Lemma spec_tctranslation__adequate_translation {Σ} m ψ e :
    (∀ `{!heapGS Σ},
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{!heapGpreS Σ} σ,
      ∀ (k : nat), (k ≥ m)%nat → adequate NotStuck «e» S«σ,k» (λ v σ, ψ v).
  Proof.
    intros Hspec HpreG σ k Ik.
    (* apply the adequacy results. *)
    apply (heap_adequacy Σ). clear HpreG.
    iIntros (HG) "HTC". simpl.
    iApply (Hspec with "[HTC]"); last by auto.
    iApply (TC_weaken with "HTC"). lia.
  Qed.

  Theorem spec_tctranslation__adequate_and_bounded {Σ} m φ e :
    tick_free_expr e →
    (∀ `{!heapGS Σ},
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ `{!heapGpreS Σ} σ, tick_free_state σ →
      adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Htfe Hspec HpreG σ Htfσ.
    apply adequate_tctranslation__adequate_and_bounded.
    { split; [apply Forall_cons|]; done. }
    intros k Ik. by eapply spec_tctranslation__adequate_translation.
  Qed.

  (* A simplification for common use-cases: when the return value does not
   * contain a closure, there is no need to compose the postcondition φ with
   * the translation: *)
  Theorem spec_tctranslation__adequate_and_bounded' {Σ} m (φ : val → Prop) e :
    tick_free_expr e →
    (∀ v, φ v → closure_free v) →
    (∀ `{!heapGS Σ},
      {{{ TC m }}} «e» {{{ v, RET v ; ⌜φ v⌝ }}}
    ) →
    ∀ `{!heapGpreS Σ} σ, tick_free_state σ →
      adequate NotStuck e σ (λ v σ, φ v)  ∧  bounded_time e σ m.
  Proof.
    intros Htfe Hφ Hspec HpreG σ Htfσ.
    apply (spec_tctranslation__adequate_and_bounded (Σ:=Σ)) ; try assumption.
    intros HtcHeapG.
    iIntros (Φ) "Htc Post".
    wp_apply (Hspec with "Htc"). iIntros (v Hv).
    iApply ("Post" with "[%]").
    by apply closure_free_predicate.
  Qed.

End Soundness.
