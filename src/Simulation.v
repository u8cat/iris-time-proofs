From iris.heap_lang Require Import notation proofmode.
From iris.program_logic Require Import adequacy.

Require Import Misc Reduction Tactics.
Require Export Translation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type ℓ : loc.
Implicit Type m n : nat.



Class TickCounter := { tick_counter : loc }.
Notation "S« σ , n »" := (<[tick_counter := LitV (LitInt n%nat)]> (translationS σ%V)).
(* Notation "« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (translationS σ%V)) (only printing). *)
Local Notation ℓ := tick_counter.



Section Simulation. (* this whole file is parameterized by a “runtime_error” value *)
Context (runtime_error : val).



(*
 * Definition of “tick”
 *)

Definition tick {Hloc : TickCounter} : val :=
  rec: "tick" "x" :=
    let: "k" := ! #ℓ in
    if: "k" ≤ #0 then
      runtime_error #()
    else if: CAS #ℓ "k" ("k" - #1) then
      "x"
    else
      "tick" "x".

Local Instance Tick_tick (Hloc: TickCounter) : Tick :=
  {| Translation.tick := tick |}.



(*
 * Operational behavior of “tick”
 *)

Section Tick_exec.

  Context {Hloc : TickCounter}.

  Lemma exec_tick_success n v σ :
    prim_exec  (tick v) (<[ℓ := #(S n)]> σ)  v (<[ℓ := #n]> σ)  [].
  Proof.
    unlock tick.
    apply prim_exec_cons_nofork
    with (
      let: "k" := ! #ℓ in
      if: "k" ≤ #0 then
        runtime_error #()
      else if: CAS #ℓ "k" ("k" - #1) then
        v
      else
        tick v
    )%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step ; first exact _.
      replace (rec: "tick" "x" := _)%E with (of_val tick) by by unlock tick.
      unfold subst ; simpl ; fold subst.
      rewrite ! subst_is_closed_nil // ; apply is_closed_of_val.
    }
    apply prim_exec_cons_nofork
    with (
      let: "k" := #(S n) in
      if: "k" ≤ #0 then
        runtime_error #()
      else if: CAS #ℓ "k" ("k" - #1) then
        v
      else
        tick v
    )%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step.
      apply lookup_insert.
    }
    apply prim_exec_cons_nofork
    with (
      if: #(S n) ≤ #0 then
        runtime_error #()
      else if: CAS #ℓ #(S n) (#(S n) - #1) then
        v
      else
        tick v
    )%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step ; first exact _.
      unfold subst ; simpl ; fold subst.
      rewrite ! subst_is_closed_nil // ; apply is_closed_of_val.
    }
    apply prim_exec_cons_nofork
    with (
      if: #false then
        runtime_error #()
      else if: CAS #ℓ #(S n) (#(S n) - #1) then
        v
      else
        tick v
    )%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step.
    }
    apply prim_exec_cons_nofork
    with  (if: CAS #ℓ #(S n) (#(S n) - #1) then v else tick v)%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step.
    }
    apply prim_exec_cons_nofork
    with  (if: CAS #ℓ #(S n) (#(S n - 1)) then v else tick v)%E  (<[ℓ := #(S n)]> σ).
    {
      prim_step.
    }
    apply prim_exec_cons_nofork
    with  (if: #true then v else tick v)%E  (<[ℓ := #(S n - 1)]> (<[ℓ := #(S n)]> σ)).
    {
      prim_step.
      apply lookup_insert.
    }
    replace (S n - 1) with (Z.of_nat n) by lia.
    rewrite insert_insert.
    apply prim_exec_cons_nofork
    with  v  (<[ℓ := #n]> σ).
    {
      prim_step.
    }
    apply prim_exec_nil.
  Qed.

  Lemma exec_tick_aux e1 v2 σ :
    is_closed [] e1 →
    prim_exec (tick_aux (λ: <>, e1) v2)%E σ
              (e1 (tick v2)           )   σ [].
  Proof.
    intros ; assert (Closed [] e1) by exact.
    unfold tick_aux ; unlock.
    eapply prim_exec_cons_nofork.
    {
      prim_step.
      - rewrite /= decide_left //.
      - exact _.
    }
    eapply prim_exec_cons_nofork.
    {
      prim_step ;
      fold subst.
      rewrite subst_is_closed_nil ; last apply is_closed_of_val.
      exact _.
    }
    eapply prim_exec_cons_nofork, prim_exec_nil ; simpl.
    {
      unfold subst ; simpl ; fold subst.
      rewrite subst_is_closed_nil ; last assumption.
      rewrite subst_is_closed_nil ; last by apply is_closed_subst, is_closed_of_val.
      rewrite subst_is_closed_nil ; last apply is_closed_of_val.
      by prim_step.
    }
  Qed.

End Tick_exec.



(*
 * Simulation lemma
 *)

Section SimulationLemma.

  Context {Hloc : TickCounter}.

  (* from a reduction of the source expression,
   * deduce a reduction of the translated expression. *)

  Lemma exec_tick_success' n e v σ :
    to_val e = Some v →
    prim_exec  (tick e) (<[ℓ := #(S n)]> σ)  e (<[ℓ := #n]> σ)  [].
  Proof.
    intros <- % of_to_val. eapply exec_tick_success.
  Qed.

  Local Ltac exec_tick_success :=
    lazymatch goal with
    | |- prim_exec ?e _ _ _ _ =>
        reshape_expr e ltac:(fun K e' =>
          eapply prim_exec_fill' with K e' _ ; [ done | done | ] ;
          eapply exec_tick_success'
        )
    end ;
    by simpl_to_of_val.
  (* in this tactic, the parameter ‘afterwards’ allows to unify the expression
   * resulting from the step before running the tactic ‘prim_step’;
   * this matters when the reduction rule to apply is directed by the syntax of
   * the result (more specifically, ‘CasFailS’ would be picked instead of
   * ‘CasSucS’ if we did not unify the result with ‘#true’ beforehand). *)
  Local Ltac tick_then_step_then afterwards :=
    eapply prim_exec_transitive_nofork ; first (
      exec_tick_success
    ) ;
    eapply prim_exec_cons_nofork, afterwards ; first (
      prim_step
    ).
  Local Ltac tick_then_step_then_stop :=
    tick_then_step_then prim_exec_nil.

  Lemma simulation_head_step_success n e1 σ1 e2 σ2 efs :
    σ2 !! ℓ = None →
    is_closed [] e1 →
    head_step e1 σ1 e2 σ2 efs →
    prim_exec «e1» S«σ1, S n» «e2» S«σ2, n» T«efs».
  Proof.
    intros Hℓ Hclosed Hstep.
    destruct Hstep as
      [ (* BetaS *) f x e1 e2 v2 e' σ  Hval_e2 Hclosed_e1 ->
      | (* UnOpS *) op e v v' σ  Hval_e Hopeval
      | (* BinOpS *) op e1 e2 v1 v2 v' σ  Hval_e1 Hval_e2 Hopeval
      | (* IfTrueS  *) e1 e2 σ
      | (* IfFalseS *) e1 e2 σ
      | (* FstS *) e1 v1 e2 v2 σ  Hval_e1 Hval_e2
      | (* SndS *) e1 v1 e2 v2 σ  Hval_e1 Hval_e2
      | (* CaseLS *) e0 v0 e1 e2 σ  Hval_e0
      | (* CaseRS *) e0 v0 e1 e2 σ  Hval_e0
      | (* ForkS *) e σ
      | (* AllocS *) e v σ l  Hval_e Hfree_l
      | (* LoadS *) l v σ  Hbound_l
      | (* StoreS *) l e v σ  Hval_e Hisbound_l
      | (* CasFailS *) l e1 v1 e2 v2 vl σ  Hval_e1 Hval_e2 Hbound_l Hneq_vl_v1
      | (* CasSucS *) l e1 v1 e2 v2 σ  Hval_e1 Hval_e2 Hbound_l
      | (* FaaS *) l i1 e2 i2 σ  Hval_e2 Hbound_l
      ] ;
    cbn [translation fmap list_fmap] ;
    rewrite_into_values ; rewrite ? translation_of_val ;
    (try (
      assert (ℓ ≠ l) as I by (by apply lookup_insert_None in Hℓ as [ _ I ]) ;
      rewrite translationS_insert insert_commute ; last exact I
    )).
    (* BetaS f x e1 e2 v2 e' σ : *)
    - assert (Closed (f :b: x :b: []) « e1 ») by by apply is_closed_translation.
      rewrite 2! translation_subst' translation_of_val.
      tick_then_step_then_stop.
    (* UnOpS op e v v' σ : *)
    - tick_then_step_then_stop.
      by apply un_op_eval_translation.
    (* BinOpS op e1 e2 v1 v2 v' σ : *)
    - tick_then_step_then_stop.
      by apply bin_op_eval_translation.
    (* IfTrueS e1 e2 σ : *)
    - tick_then_step_then_stop.
    (* IfFalseS e1 e2 σ : *)
    - tick_then_step_then_stop.
    (* FstS e1 v1 e2 v2 σ : *)
    - tick_then_step_then_stop.
    (* SndS e1 v1 e2 v2 σ : *)
    - tick_then_step_then_stop.
    (* CaseLS e0 v0 e1 e2 σ : *)
    - tick_then_step_then exec_tick_aux.
      (* this is the only place where we need the term to be closed (because
       * the reduction rules for Case are adhoc somehow: *)
      simpl in Hclosed ; repeat (apply andb_True in Hclosed as [ Hclosed ? ]).
      by apply is_closed_translation.
    (* CaseRS e0 v0 e1 e2 σ : *)
    - tick_then_step_then exec_tick_aux.
      (* this is the only place where we need the term to be closed (because
       * the reduction rules for Case are adhoc somehow: *)
      simpl in Hclosed ; repeat (apply andb_True in Hclosed as [ Hclosed ? ]).
      by apply is_closed_translation.
    (* ForkS e σ : *)
    - replace [« e »] with ([« e »] ++ []) by apply app_nil_r.
      eapply prim_exec_cons.
      + prim_step.
      + exec_tick_success.
    (* AllocS e v σ l : *)
    - tick_then_step_then_stop.
      apply lookup_insert_None ; auto using lookup_translationS_None.
    (* LoadS l v σ : *)
    - tick_then_step_then_stop.
      assert (ℓ ≠ l) as I by (intros <- ; rewrite -> Hℓ in * ; discriminate).
      rewrite lookup_insert_ne ; last exact I.
      by apply lookup_translationS_Some.
    (* StoreS l e v σ : *)
    - tick_then_step_then_stop.
      rewrite lookup_insert_ne ; last exact I.
      by apply lookup_translationS_is_Some.
    (* CasFailS l e1 v1 e2 v2 vl σ : *)
    - tick_then_step_then_stop.
      + assert (ℓ ≠ l) as I by (intros <- ; rewrite -> Hℓ in * ; discriminate).
        rewrite lookup_insert_ne ; last done.
        by apply lookup_translationS_Some.
      + eauto using translationV_injective.
    (* CasSucS l e1 v1 e2 v2 σ : *)
    - tick_then_step_then_stop.
      rewrite lookup_insert_ne ; last exact I.
      by apply lookup_translationS_Some.
    (* FaaS l i1 e2 i2 σ : *)
    - tick_then_step_then_stop.
      rewrite lookup_insert_ne ; last exact I.
      change (#i1)%V with V« #i1 ».
      by apply lookup_translationS_Some.
  Qed.

  Lemma simulation_prim_step_success n e1 σ1 e2 σ2 efs :
    σ2 !! ℓ = None →
    is_closed [] e1 →
    prim_step e1 σ1 e2 σ2 efs →
    prim_exec «e1» S«σ1, S n» «e2» S«σ2, n» T«efs».
  Proof.
    intros Hℓ Hclosed [ K e1' e2' -> -> H ].
    rewrite 2! translation_fill.
    apply is_closed_fill_inv in Hclosed.
    by eapply prim_exec_fill, simulation_head_step_success.
  Qed.

  Lemma simulation_step_success n t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    Forall (is_closed []) t1 →
    step (t1, σ1) (t2, σ2) →
    rtc step (T«t1», S«σ1, S n») (T«t2», S«σ2, n»).
  Proof.
    intros Hℓ Hclosed Hstep.
    destruct Hstep as [ e1 σ1_ e2 σ2_ efs t t' E1 E2 Hprimstep ] ;
    injection E1 as -> <- ;
    injection E2 as -> <-.
    repeat rewrite ? fmap_app ? fmap_cons.
    apply Forall_app, proj2, Forall_cons, proj1 in Hclosed.
    by apply exec_frame_singleton_thread_pool, prim_exec_exec, simulation_prim_step_success.
  Qed.

  Lemma simulation_exec_success m n t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    Forall (is_closed []) t1 →
    nsteps step m (t1, σ1) (t2, σ2) →
    rtc step (T«t1», S«σ1, m+n») (T«t2», S«σ2, n»).
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hℓ Hclosed Hnsteps.
    revert t1 σ1 E1 Hclosed ;
    induction Hnsteps as [ config | m' config1 (t3, σ3) config2 Hstep Hsteps IHnsteps ] ;
    intros t1 σ1 E1 Hclosed.
    - destruct E2 ; injection E1 as -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      specialize (IHnsteps eq_refl t3 σ3 eq_refl).
      assert (σ3 !! ℓ = None) as Hℓ3 by (eapply loc_fresh_in_dom_nsteps ; cycle 1 ; eassumption).
      assert (Forall (is_closed []) t3) as Hclosed3 by by eapply is_closed_step.
      specialize (IHnsteps Hclosed3).
      eapply rtc_transitive.
      + apply simulation_step_success ; cycle -1 ; eassumption.
      + apply IHnsteps.
  Qed.

  Lemma simulation_exec_success' m n t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    Forall (is_closed []) t1 →
    (m ≤ n)%nat →
    nsteps step m (t1, σ1) (t2, σ2) →
    rtc step (T«t1», S«σ1, n») (T«t2», S«σ2, n-m»).
  Proof.
    intros Hℓ Hclosed I.
    replace #n with #(m + (n-m))%nat ; last (repeat f_equal ; lia).
    by apply simulation_exec_success.
  Qed.

  (* from a reduction of the translated expression,
   * deduce a reduction of the source expression. *)

  (* note: this does not depend on the operational behavior of `tick`. *)

  Local Ltac exhibit_prim_step e2 :=
    eexists e2, _, _ ; simpl ; prim_step.

  Local Ltac eexhibit_prim_step :=
    eexists _, _, _ ; simpl ; prim_step.

  Lemma active_item_translation_reducible ki v σ m :
    ectx_item_is_active ki →
    loc_fresh_in_expr ℓ (fill_item ki v) →
    reducible (fill_item Ki«ki» V«v») S«σ, m» →
    reducible (fill_item ki v) σ.
  Proof.
    intros Hactive Hfresh (e2' & σ2' & efs & Hheadstep % active_item_prim_step_is_head_step) ;
      last by apply is_active_translationKi.
    make_eq (fill_item Ki«ki» V«v») as e1' Ee1' ; rewrite Ee1' in Hheadstep.
    make_eq (S«σ, m») as σ1' Eσ1' ; rewrite Eσ1' in Hheadstep.
    destruct Hheadstep as
      [ (* BetaS *) f x e1 e2 v2 e' σ1  Hval_e2 Hclosed_e1 E'
      | (* UnOpS *) op e1 v1 v' σ1  Hval_e1 Hopeval
      | (* BinOpS *) op e1 e2 v1 v2 v' σ1  Hval_e1 Hval_e2 Hopeval
      | (* IfTrueS  *) e1 e2 σ1
      | (* IfFalseS *) e1 e2 σ1
      | (* FstS *) e1 v1 e2 v2 σ1  Hval_e1 Hval_e2
      | (* SndS *) e1 v1 e2 v2 σ1  Hval_e1 Hval_e2
      | (* CaseLS *) e0 v0 e1 e2 σ1  Hval_e0
      | (* CaseRS *) e0 v0 e1 e2 σ1  Hval_e0
      | (* ForkS *) e σ1
      | (* AllocS *) e1 v1 σ1 l  Hval_e1 Hfree_l
      | (* LoadS *) l v1 σ1  Hbound_l
      | (* StoreS *) l e1 v1 σ1  Hval_e1 Hisbound_l
      | (* CasFailS *) l e1 v1 e2 v2 vl σ1  Hval_e1 Hval_e2 Hbound_l Hneq_vl_v1
      | (* CasSucS *) l e1 v1 e2 v2 σ1  Hval_e1 Hval_e2 Hbound_l
      | (* FaaS *) l i1 e2 i2 σ1  Hval_e2 Hbound_l
      ] ;
    destruct ki ; try contradiction Hactive ; try discriminate Ee1' ;
    injection Ee1' ; clear Ee1' ;
    repeat (intros -> || intros <- || intros -> % translationV_lit_inv_expr || intros E) ;
    destruct Eσ1' ;
    repeat lazymatch goal with H : to_val (of_val «_»%V) = Some _ |- _ =>
      rewrite to_of_val in H ; injection H as <-
    end .
    (* replacing the state S«σ, m» with S«σ»: *)
    all: first [
        apply lookup_insert_None in Hfree_l as [Hfree_l _]
      | apply lookup_insert_Some in Hbound_l as [ [<- _] | [_ Hbound_l] ] ; first naive_solver
      | apply lookup_insert_is_Some in Hisbound_l as [ <- | [_ Hisbound_l] ] ; first naive_solver
      | idtac
    ].
    (* BetaS *)
    - destruct v1 ; try discriminate E.
      eexhibit_prim_step.
    (* UnOpS *)
    - eexhibit_prim_step.
      by eapply un_op_eval_translation_inv.
    (* BinOpS *)
    - eexhibit_prim_step.
      by eapply bin_op_eval_translation_inv.
    (* IfTrueS *)
    - eexhibit_prim_step.
    (* IfFalseS *)
    - eexhibit_prim_step.
    (* FstS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* SndS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* CaseLS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* CaseRS *)
    - destruct v ; try discriminate E.
      eexhibit_prim_step.
    (* AllocS *)
    - eexhibit_prim_step.
      by eapply lookup_translationS_None_inv.
    (* LoadS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & _).
      eexhibit_prim_step.
    (* StoreS *)
    - eexhibit_prim_step.
      by eapply lookup_translationS_is_Some_inv.
    (* CasFailS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & ->).
      exhibit_prim_step (#false)%E.
      intros ? % (f_equal translationV). contradiction.
    (* CasSucS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & -> % translationV_injective).
      exhibit_prim_step (#true)%E.
    (* FaaS *)
    - apply lookup_translationS_Some_inv in Hbound_l as (? & ? & -> % eq_sym % translationV_lit_inv).
      rewrite to_of_val in Hval_e2 ; injection Hval_e2 as -> % translationV_lit_inv.
      eexhibit_prim_step.
  Qed.

  (* assuming the safety of the translated expression,
   * a proof that the original expression is m-safe. *)

  Lemma safe_translation__safe_here m e σ :
    is_closed [] e →
    loc_fresh_in_expr ℓ e →
    (m > 0)%nat →
    safe «e» S«σ, m» →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros Hclosed Hfresh Im Hsafe.
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
         * (m ≥ 1 so ‘tick’ can be run): *)
        assert (
          prim_exec (fill_item Ki«ki» (tick V«v»)) S«σ, m»
                    (fill_item Ki«ki» V«v»)        S«σ, m-1» []
        ) as Hsteps % prim_exec_exec.
        {
          assert (fill [Ki«ki»] = fill_item Ki«ki») as E by reflexivity ; destruct E.
          apply prim_exec_fill. apply safe_fill_inv in Hsafe.
          rewrite {+1} (_ : m = S (m-1)) ; last lia.
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
  Lemma safe_translation__safe m n e σ t2 σ2 e2 :
    is_closed [] e →
    loc_fresh_in_expr ℓ e2 →
    σ2 !! ℓ = None →
    safe «e» S«σ, m» →
    nsteps step n ([e], σ) (t2, σ2) →
    (n < m)%nat →
    e2 ∈ t2 →
    is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    intros Hclosed Hℓe Hℓσ Hsafe Hnsteps Inm He2.
    assert (safe «e2» S«σ2, m-n») as Hsafe2.
    {
      eapply safe_exec.
      - eapply elem_of_list_fmap_1. eassumption.
      - eassumption.
      - change [«e»] with T«[e]». apply simulation_exec_success' ; [ assumption | auto | lia | assumption ].
    }
    assert (is_closed [] e2) as Hclosede2.
    {
      assert (Forall (is_closed []) t2) as Hclosedt2
        by eauto using nsteps_rtc, is_closed_exec.
      by eapply Forall_forall in Hclosedt2 ; last exact He2.
    }
    assert (m - n > 0)%nat by lia.
    by eapply safe_translation__safe_here.
  Qed.

  (* assuming the adequacy of the translated expression,
   * a proof that the original expression has m-adequate results. *)

  Lemma adequate_translation__adequate_result m n (φ : val → Prop) e σ t2 σ2 v2 :
    is_closed [] e →
    σ2 !! ℓ = None →
    adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV) →
    nsteps step n ([e], σ) (of_val v2 :: t2, σ2) →
    (n ≤ m)%nat →
    φ v2.
  Proof.
    intros Hclosed Hfresh Hadq Hnsteps Inm.
    assert (safe «e» S«σ, m») as Hsafe by by eapply safe_adequate.
    replace (φ v2) with ((φ ∘ invtranslationV) (translationV v2))
      by (simpl ; by rewrite invtranslationV_translationV).
    eapply adequate_result ; first done.
    change [«e»%E] with T«[e]».
    replace (of_val «v2» :: _) with (T«of_val v2 :: t2») by by rewrite - translation_of_val.
    eapply simulation_exec_success' ; eauto.
  Qed.

End SimulationLemma. (* we close the section here as we now want to quantify over all locations *)

(* now let’s combine the two results. *)

Record adequate_n (s : stuckness) (n : nat) e1 σ1 (φ : val → Prop) := {
  adequate_n_result k t2 σ2 v2 :
   nsteps step k ([e1], σ1) (of_val v2 :: t2, σ2) → (k ≤ n)%nat → φ v2;
  adequate_n_not_stuck k t2 σ2 e2 :
   s = NotStuck →
   nsteps step k ([e1], σ1) (t2, σ2) →
   (k < n)%nat →
   e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
}.

Lemma adequate_translation__adequate m (φ : val → Prop) e σ :
  is_closed [] e →
  (∀ {Hloc : TickCounter}, adequate NotStuck «e» S«σ, m» (φ ∘ invtranslationV)) →
  adequate_n NotStuck m e σ φ.
Proof.
  intros Hclosed Hadq.
  split.
  (* (1) adequate result: *)
  - intros n t2 σ2 v2 Hnsteps Inm.
    (* build a location ℓ which is not in the domain of σ2: *)
    pose (Hloc := Build_TickCounter (fresh (dom (gset loc) σ2)) : TickCounter).
    assert (σ2 !! ℓ = None)
      by (simpl ; eapply not_elem_of_dom, is_fresh).
    by eapply adequate_translation__adequate_result.
  (* (2) safety: *)
  - intros n t2 σ2 e2 _ Hnsteps Inm He2.
    (* build a location ℓ which is fresh in e2 and in the domain of σ2: *)
    pose (set1 := loc_set_of_expr e2 : gset loc).
    pose (set2 := dom (gset loc) σ2 : gset loc).
    pose (Hloc := Build_TickCounter (fresh (set1 ∪ set2)) : TickCounter).
    eassert (ℓ ∉ set1 ∪ set2) as [Hℓ1 Hℓ2] % not_elem_of_union
      by (unfold ℓ ; apply is_fresh).
    assert (loc_fresh_in_expr ℓ e2)
      by by apply loc_not_in_set_is_fresh.
    assert (σ2 !! ℓ = None)
      by by (simpl ; eapply not_elem_of_dom).
    specialize (Hadq Hloc) as Hsafe % safe_adequate.
    by eapply safe_translation__safe.
Qed.

End Simulation.