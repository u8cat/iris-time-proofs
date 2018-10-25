From iris.heap_lang Require Import lang notation.
From iris.heap_lang Require Import adequacy.
From stdpp Require Import relations fin_maps gmap.

From iris_time Require Import Misc Tactics.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.



(*
 * Reduction
 *)

Section Reduction.

  Definition bounded_time e σ m : Prop :=
    ∀ t2 σ2 n, nsteps step n ([e], σ) (t2, σ2) → (n ≤ m)%nat.

  Inductive prim_exec (e1 : expr) (σ1 : state) : expr → state → list expr → Prop :=
  | prim_exec_nil :
      prim_exec e1 σ1 e1 σ1 []
  | prim_exec_cons (e2 : expr) (σ2 : state) (efs2 : list expr) e3 σ3 efs3 :
      prim_step e1 σ1 e2 σ2 efs2 →
      prim_exec e2 σ2 e3 σ3 efs3 →
      prim_exec e1 σ1 e3 σ3 (efs2 ++ efs3).

  Lemma prim_exec_cons_nofork e1 σ1 e2 σ2 e3 σ3 efs3 :
    prim_step e1 σ1 e2 σ2 []   →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 efs3.
  Proof.
    intros. change efs3 with ([] ++ efs3). by eapply prim_exec_cons.
  Qed.

  Lemma prim_exec_transitive e1 σ1 e2 σ2 efs2 e3 σ3 efs3 :
    prim_exec e1 σ1 e2 σ2 efs2 →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 (efs2 ++ efs3).
  Proof.
    induction 1 ; intros ? ; first assumption.
    rewrite - app_assoc. eapply prim_exec_cons ; eauto.
  Qed.
  Lemma prim_exec_transitive_nofork e1 σ1 e2 σ2 e3 σ3 efs3 :
    prim_exec e1 σ1 e2 σ2 [] →
    prim_exec e2 σ2 e3 σ3 efs3 →
    prim_exec e1 σ1 e3 σ3 efs3.
  Proof.
    intros. change efs3 with ([] ++ efs3). by eapply prim_exec_transitive.
  Qed.

  Lemma thread_pool_grows_after_step t1 σ1 t2 σ2 :
    step (t1, σ1) (t2, σ2) →
    (length t1 ≤ length t2)%nat.
  Proof.
    intros [e1 σ1_ e2 σ2_ efs t t' E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <-.
    repeat rewrite ? app_length ? cons_length. lia.
  Qed.
  Lemma thread_pool_grows_after_exec t1 σ1 t2 σ2 :
    rtc step (t1, σ1) (t2, σ2) →
    (length t1 ≤ length t2)%nat.
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hsteps.
    revert t1 σ1 E1 ;
    induction Hsteps as [ config | config1 (t3, σ3) config2 Hstep _ IHsteps ] ;
    intros t1 σ1 E1.
    - destruct E2 ; injection E1 as -> ->.
      done.
    - destruct E2, E1.
      eapply Nat.le_trans.
      + by eapply thread_pool_grows_after_step.
      + by eapply IHsteps.
  Qed.
  Lemma thread_pool_is_cons_after_step t1 σ1 t2 σ2 :
    step (t1, σ1) (t2, σ2) →
    ∃ e2 t2', t2 = e2 :: t2'.
  Proof.
    intros Hstep.
    assert (0 < length t1)%nat as I.
    {
      destruct Hstep as [e1 σ1_ _ _ _ ta tb E1 _ _] ; injection E1 as -> _.
      rewrite app_length cons_length. lia.
    }
    destruct t2.
    - apply thread_pool_grows_after_step, le_not_lt in Hstep. contradiction.
    - eauto.
  Qed.
  Lemma thread_pool_is_cons_after_exec e1 t1' σ1 t2 σ2 :
    rtc step (e1 :: t1', σ1) (t2, σ2) →
    ∃ e2 t2', t2 = e2 :: t2'.
  Proof.
    destruct t2.
    - intros ? % thread_pool_grows_after_exec % Nat.nle_succ_0 ; contradiction.
    - eauto.
  Qed.

  Lemma step_insert_in_thread_pool (n : nat) t t1 σ1 t2 σ2 :
    (n ≤ length t1)%nat →
    step (t1, σ1) (t2, σ2) →
    step (take n t1 ++ t ++ drop n t1, σ1) (take n t2 ++ t ++ drop n t2, σ2).
  Proof.
    intros I Hstep.
    destruct Hstep as [e1 σ1_ e2 σ2_ efs ta tb E1 E2 Hprimstep] ; simpl in * ;
    injection E1 as -> <- ; injection E2 as -> <-.
    pose proof (le_lt_dec n (length ta)) as J.
    destruct J as [ J | J ].
    (* if n ≤ length ta: *)
    - rewrite ! take_app_le ? drop_app_le ; [ | exact J ..].
      rewrite ! app_assoc.
      eapply step_atomic ; last eassumption ; reflexivity.
    (* if length ta < n: *)
    - rewrite app_length cons_length in I.
      assert (  (length ta ≤ n)%nat
              ∧ (0 < n - length ta)%nat
              ∧ (n - length ta - 1 ≤ length tb)%nat )
        as (J1 & J2 & J3) by lia.
      rewrite ! take_app_ge ? drop_app_ge ; [ | exact J1 ..].
      rewrite ! take_cons   ? drop_cons   ; [ | exact J2 ..].
      rewrite   take_app_le ? drop_app_le ; [ | exact J3 ..].
      eapply step_atomic ; last eassumption ; rewrite - ! app_assoc /= //.
  Qed.
  Lemma exec_insert_in_thread_pool (n : nat) t t1 σ1 t2 σ2 :
    (n ≤ length t1)%nat →
    rtc step (t1, σ1) (t2, σ2) →
    rtc step (take n t1 ++ t ++ drop n t1, σ1) (take n t2 ++ t ++ drop n t2, σ2).
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros I H.
    revert t1 σ1 E1 I ;
    induction H as [ config | config1 (t3, σ3) config2 Hstep _ IHsteps ] ;
    intros t1 σ1 E1 I.
    - destruct E2 ; injection E1 as -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      eapply rtc_l.
      + by eapply step_insert_in_thread_pool.
      + by eapply IHsteps, le_trans, thread_pool_grows_after_step.
  Qed.
  Lemma exec_frame_thread_pool t1 σ1 t2 σ2 ta tb :
    rtc step (t1, σ1) (t2, σ2) →
    let n := length t1 in
    rtc step (ta ++ t1 ++ tb, σ1) (ta ++ take n t2 ++ tb ++ drop n t2, σ2).
  Proof.
    intros Hsteps n.
    replace (t1 ++ tb) with (take n t1 ++ tb ++ drop n t1)
      by by rewrite firstn_all drop_all app_nil_r.
    apply (exec_insert_in_thread_pool 0 ta), (exec_insert_in_thread_pool n tb) ; first lia ; done.
  Qed.
  Lemma exec_frame_singleton_thread_pool e1 σ1 e2 t2 σ2 t t' :
    rtc step ([e1], σ1) (e2 :: t2, σ2) →
    rtc step (t ++ e1 :: t', σ1) (t ++ e2 :: t' ++ t2, σ2).
  Proof.
    change (e1 :: t') with ([e1] ++ t').
    apply exec_frame_thread_pool.
  Qed.

  Lemma prim_step_step e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    step ([e1], σ1) (e2 :: efs, σ2).
  Proof.
    intros. by eapply step_atomic with _ _ _ _ _ [] [].
  Qed.
  Lemma prim_exec_exec e1 σ1 e2 σ2 efs :
    prim_exec e1 σ1 e2 σ2 efs →
    rtc step ([e1], σ1) (e2 :: efs, σ2).
  Proof.
    induction 1 ; econstructor ; eauto using prim_step_step, (exec_frame_singleton_thread_pool _ _ _ _ _ []).
  Qed.

  Lemma prim_step_fill K e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs →
    prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof.
    intros [ K' e1' e2' -> -> Hheadstep ].
    rewrite - 2! fill_app.
    by econstructor.
  Qed.
  Lemma prim_exec_fill K e1 σ1 e2 σ2 efs :
    prim_exec e1 σ1 e2 σ2 efs →
    prim_exec (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof.
    induction 1 ; econstructor ; eauto using prim_step_fill.
  Qed.
  Lemma prim_exec_fill' K e1 σ1 e2 σ2 efs e1' e2' :
    fill K e1 = e1' →
    fill K e2 = e2' →
    prim_exec e1 σ1 e2 σ2 efs →
    prim_exec e1' σ1 e2' σ2 efs.
  Proof.
    intros <- <-. apply prim_exec_fill.
  Qed.

  Lemma step_fill K e1 t1' σ1 e2 t2' σ2 :
    step (e1 :: t1', σ1) (e2 :: t2', σ2) →
    step (fill K e1 :: t1', σ1) (fill K e2 :: t2', σ2).
  Proof.
    intros Hstep.
    destruct Hstep as [ e1' ? e2' ? efs ta tb E1 E2 ] ;
    destruct ta as [ | ? ta ] ;
    injection E1 as <- -> <- ; injection E2 as <- -> <-.
    - by eapply step_atomic with _ _ _ _ _ [] _, prim_step_fill.
    - by eapply step_atomic with _ _ _ _ _ (fill K e2 :: ta) tb.
  Qed.
  Lemma exec_fill K e1 t1' σ1 e2 t2' σ2 :
    rtc step (e1 :: t1', σ1) (e2 :: t2', σ2) →
    rtc step (fill K e1 :: t1', σ1) (fill K e2 :: t2', σ2).
  Proof.
    make_eq (e1 :: t1', σ1) as config1 E1.
    make_eq (e2 :: t2', σ2) as config2 E2.
    intros Hsteps.
    revert e1 t1' σ1 E1 ;
    induction Hsteps as [ config | config1 (t3, σ3) config2 Hstep _ IHsteps ] ;
    intros e1 t1' σ1 E1.
    - destruct E2 ; injection E1 as -> -> ->.
      apply rtc_refl.
    - destruct E2, E1.
      assert (∃ e3 t3', t3 = e3 :: t3') as (e3 & t3' & ->)
        by by eapply thread_pool_is_cons_after_step.
      eapply rtc_l.
      + by apply step_fill.
      + by apply IHsteps.
  Qed.

  Lemma reducible_fill K e σ :
    reducible e σ →
    reducible (fill K e) σ.
  Proof.
    intros (e' & σ' & efs & Hstep).
    eexists _, _, _.
    by apply prim_step_fill.
  Qed.

End Reduction.



(*
 * Closed expressions
 *)

Section Closed.

  Lemma is_closed_fill_inv xs K e :
    is_closed xs (fill K e) →
    is_closed xs e.
  Proof.
    replace K with (rev (rev K)) by apply rev_involutive.
    induction (rev K) as [ | [] revK' ] ; first done ;
    rewrite /= fill_app /= ; naive_solver.
  Qed.

  Lemma is_closed_fill xs K e :
    is_closed xs e →
    (∃ e0, is_closed xs (fill K e0)) →
    is_closed xs (fill K e).
  Proof.
    intros He [e0 HK] ; revert HK.
    replace K with (rev (rev K)) by apply rev_involutive.
    induction (rev K) as [ | [] revK' ] ; first done ;
    rewrite /= !fill_app /= ; naive_solver.
  Qed.

  Lemma is_closed_head_step xs e1 σ1 e2 σ2 efs :
    is_closed xs e1 →
    head_step e1 σ1 e2 σ2 efs →
    is_closed xs e2 ∧ Forall (is_closed xs) efs.
  Proof.
    intros Hclosed Hstep.
    destruct Hstep as
      [ (* BetaS *) f x e1 e2 v2 e' σ  Hval_e2 Hclosed_e1 ->
      | | | | | | | | | | | | | | | ] ;
    (split ; last auto) ;
    rewrite_into_values ;
    try (by apply is_closed_of_val) ;
    try naive_solver.
    (* BetaS f x e1 e2 v2 e' σ : *)
    - apply is_closed_do_subst', is_closed_do_subst' ; try naive_solver. by apply is_closed_of_val.
  Qed.
  Lemma is_closed_prim_step xs e1 σ1 e2 σ2 efs :
    is_closed xs e1 →
    prim_step e1 σ1 e2 σ2 efs →
    is_closed xs e2 ∧ Forall (is_closed xs) efs.
  Proof.
    intros HKe1' [K e1' e2' -> -> Hstep] ; simpl in *. 
    eapply is_closed_head_step in Hstep as [??] ; last by eapply is_closed_fill_inv.
    eauto using is_closed_fill.
  Qed.
  Lemma is_closed_step xs t1 σ1 t2 σ2 :
    Forall (is_closed xs) t1 →
    step (t1, σ1) (t2, σ2) →
    Forall (is_closed xs) t2.
  Proof.
    intros Hclosed Hstep.
    destruct Hstep as [e1 σ1_ e2 σ2_ efs tl tr E1 E2 Hstep] ;
    injection E1 as -> <- ; injection E2 as -> <- ;
    simpl.
    rewrite -> ? Forall_app, ? Forall_cons in Hclosed. repeat (destruct Hclosed as [? Hclosed]).
    eapply is_closed_prim_step in Hstep as [??] ; last eassumption.
    repeat (rewrite ? Forall_app ? Forall_cons ; repeat split) ; assumption.
  Qed.
  Lemma is_closed_exec xs t1 σ1 t2 σ2 :
    Forall (is_closed xs) t1 →
    rtc step (t1, σ1) (t2, σ2) →
    Forall (is_closed xs) t2.
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hclosed Hsteps.
    revert t1 σ1 E1 Hclosed ;
    induction Hsteps as [ config | config1 (t3, σ3) config2 Hstep _ IHsteps ] ;
    intros t1 σ1 E1 Hclosed.
    - destruct E2 ; injection E1 as -> _.
      done.
    - destruct E2, E1.
      eapply is_closed_step in Hstep ; last done.
      by eapply IHsteps.
  Qed.

End Closed.



(*
 * Fresh locations
 *)

Section FreshLocation.

  Lemma loc_fresh_in_dom_head_step ℓ e1 σ1 e2 σ2 efs :
    σ2 !! ℓ = None →
    head_step e1 σ1 e2 σ2 efs →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H ; try done ;
    by apply lookup_insert_None in Hℓ as [ Hℓ _ ].
  Qed.
  Lemma loc_fresh_in_dom_prim_step ℓ e1 σ1 e2 σ2 efs :
    σ2 !! ℓ = None →
    prim_step e1 σ1 e2 σ2 efs →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H ;
    by eapply loc_fresh_in_dom_head_step.
  Qed.
  Lemma loc_fresh_in_dom_step ℓ t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    step (t1, σ1) (t2, σ2) →
    σ1 !! ℓ = None.
  Proof.
    intros Hℓ H ; destruct H as [ ? ? ? ? ? ? ? E1 E2 Hstep ] ;
    injection E1 as -> <- ; injection E2 as -> <- ;
    by eapply loc_fresh_in_dom_prim_step.
  Qed.
  Lemma loc_fresh_in_dom_nsteps ℓ m t1 σ1 t2 σ2 :
    σ2 !! ℓ = None →
    nsteps step m (t1, σ1) (t2, σ2) →
    σ1 !! ℓ = None.
  Proof.
    make_eq (t1, σ1) as config1 E1.
    make_eq (t2, σ2) as config2 E2.
    intros Hℓ H.
    revert t1 σ1 E1 ;
    induction H as [ config | _ config1 (t3, σ3) config2 Hstep _ IHnsteps ] ;
    intros t1 σ1 E1.
    - destruct E2 ; injection E1 as -> ->.
      done.
    - destruct E2, E1.
      specialize (IHnsteps eq_refl t3 σ3 eq_refl).
      eapply loc_fresh_in_dom_step ; eassumption.
  Qed.

  Fixpoint loc_set_of_expr e : gset loc :=
    match e with
    | Lit (LitLoc l) => {[ l ]}
    | Lit _ | Var _ => empty
    | Rec _ _ e
    | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
       loc_set_of_expr e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2 =>
       loc_set_of_expr e1 ∪ loc_set_of_expr e2
    | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
       loc_set_of_expr e0 ∪ loc_set_of_expr e1 ∪ loc_set_of_expr e2
    end.

  Fixpoint loc_fresh_in_expr (ℓ : loc) e : bool :=
    match e with
    | Lit (LitLoc l) => bool_decide (ℓ ≠ l)
    | Lit _ | Var _ => true
    | Rec _ _ e
    | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Alloc e | Load e =>
       loc_fresh_in_expr ℓ e
    | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | Store e1 e2 | FAA e1 e2 =>
       loc_fresh_in_expr ℓ e1 && loc_fresh_in_expr ℓ e2
    | If e0 e1 e2 | Case e0 e1 e2 | CAS e0 e1 e2 =>
       loc_fresh_in_expr ℓ e0 && loc_fresh_in_expr ℓ e1 && loc_fresh_in_expr ℓ e2
    end.

  Lemma loc_not_in_set_is_fresh (ℓ : loc) e :
    ℓ ∉ loc_set_of_expr e →
    loc_fresh_in_expr ℓ e.
  Proof.
    (* this works but is slow: *)
(*     induction e ; try set_solver. *)
    (* fast manual proof: *)
    induction e ; simpl ;
    intros Hnotin ; repeat (apply not_elem_of_union in Hnotin as [Hnotin ?]) ;
    auto 10.
    (* only remaining case: e = Lit l *)
    case_match ; set_solver.
  Qed.

  Lemma loc_fresh_in_expr_fill_inv (ℓ : loc) K e :
    loc_fresh_in_expr ℓ (fill K e) →
    loc_fresh_in_expr ℓ e.
  Proof.
    revert e.
    induction K as [ | Ki K IH ] ; first done.
    intros e Hitem % IH.
    destruct Ki ; naive_solver.
  Qed.

End FreshLocation.



(*
 * Active context items and maximal contexts
 *)

Section ActiveItem.

  Definition ectx_item_is_active (Ki : ectx_item) : bool :=
    match Ki with
    | AppLCtx _ | UnOpCtx _ | BinOpLCtx _ _ | IfCtx _ _ | FstCtx | SndCtx
    | CaseCtx _ _ | AllocCtx | LoadCtx | StoreLCtx _ | CasLCtx _ _ | FaaLCtx _ => true
    | _ => false
    end.

  Definition immediate_sub_redexes_are_values e0 : Prop :=
    ∀ ki e1, e0 = fill_item ki e1 → is_Some (to_val e1).

  Definition maximal_ectx e K0 e0 : Prop :=
    e = fill K0 e0
  ∧ to_val e0 = None
  ∧ immediate_sub_redexes_are_values e0.

  Local Ltac maximal_ectx_from_subterm IH :=
    let E := fresh "E" in
    let v1 := fresh "v1" in
    lazymatch type of IH with to_val ?e1 = None → _ =>
      destruct (to_val e1) as [ v1 | ] eqn:E ; [
        apply of_to_val in E as <-
      |
        let K0 := fresh "K0" in
        destruct (IH eq_refl) as (K0 & ? & -> & ? & ?) ; clear IH ;
        lazymatch goal with |- to_val ?e = None → _ =>
          reshape_expr e ltac:(fun K1 _ =>
            eexists (K0 ++ K1), _ ; split ; [|split] ;
            [ by erewrite fill_app | assumption | assumption ]
          )
        end
      ] ; []
    end.

  Local Ltac maximal_ectx_empty :=
    eexists [], _ ; split ; [|split] ;
    [ reflexivity | assumption | ] ;
    intros [] ; try discriminate ; inversion 1 ; rewrite to_of_val ; eauto.

  Lemma not_val_maximal_ectx e :
    to_val e = None →
    ∃ K0 e0, maximal_ectx e K0 e0.
  Proof.
    induction e ;
      try maximal_ectx_from_subterm IHe  ;
      try maximal_ectx_from_subterm IHe3 ;
      try maximal_ectx_from_subterm IHe2 ;
      try maximal_ectx_from_subterm IHe1 ;
      maximal_ectx_empty.
  Qed.

  Local Ltac rewrite_immediate_sub_redexes_into_values Hsubterms :=
    (* we perform rewriting for each immediate sub-redex of e (we read e again
     * after each iteration because previous rewritings reveal new contexts): *)
    repeat (lazymatch type of Hsubterms with immediate_sub_redexes_are_values ?e =>
        reshape_expr e ltac:(fun K e1 =>
          (* we are only interested in contexts of depth 1; moreover, for
           * termination purposes, we do nothing when the hole e1 is already
           * a value: *)
          lazymatch constr:(pair K e1) with
          | pair _ (of_val ?v) =>
              fail
          | pair [ ?Ki ] _ =>
              let v := fresh "v" in
              destruct (Hsubterms Ki e1 eq_refl) as (v & <-%of_to_val)
          end
        )
    end).

  Local Ltac exhibit_active_item :=
    lazymatch goal with |- exists ki v, ?e = fill_item ki (of_val v) ∧ Is_true (ectx_item_is_active ki) =>
        reshape_expr e ltac:(fun K e1 =>
          (* we are only interested in contexts of depth 1; moreover, we are
           * supposed to get a value in the hole: *)
          lazymatch constr:(pair K e1) with
          | pair [ ?Ki ] (of_val ?v) =>
              (* we try to conclude with that context item (if it is not active,
               * then the proof will fail, thus we do not need to test it ourself): *)
              by exists Ki, v
          end
        )
    end.

  Lemma sub_redexes_values_active_item e0 :
    is_closed [] e0 →
    to_val e0 = None →
    immediate_sub_redexes_are_values e0 →
      (∃ e1, e0 = Fork e1)
    ∨ (∃ (ki : ectx_item) (v : val),
        e0 = fill_item ki v
      ∧ ectx_item_is_active ki).
  Proof.
    intros Hclosed Hnotval Hsubterms.
    destruct e0 ;
      rewrite_immediate_sub_redexes_into_values Hsubterms ;
      (* most cases are solved by exhibiting a solution: *)
      try (right ; exhibit_active_item) ;
      (* some cases contradict the assumption that e0 is not a value: *)
      rewrite /= ? to_of_val in Hnotval ;
      try discriminate Hnotval.
    (* remaining cases : *)
    (* Var: contradict the closedness assumption *)
    - contradiction Hclosed.
    (* Rec: contradict either closedness or the fact that e0 is not a value *)
    - case_match ; [ discriminate Hnotval | contradiction Hclosed ].
    (* Fork: the only really special case *)
    - left. eauto.
  Qed.

  Lemma not_val_fill_active_item e :
    is_closed [] e →
    to_val e = None →
      (∃ K e1, e = fill K (Fork e1))
    ∨ (∃ K ki v, e = fill K (fill_item ki v) ∧ ectx_item_is_active ki).
  Proof.
    intros Hclosed (K & e0 & -> & Hnotval & Hsubterms) % not_val_maximal_ectx.
    apply is_closed_fill_inv in Hclosed.
    apply sub_redexes_values_active_item in Hsubterms
      as [ [e1 ->] | (ki & v & -> & Hactive) ] ; naive_solver.
  Qed.

  Lemma active_item_not_val ki e :
    ectx_item_is_active ki →
    to_val (fill_item ki e) = None.
  Proof.
    destruct ki ; try contradiction ; auto.
  Qed.

  Lemma active_item_sub_redexes_values ki v :
    ectx_item_is_active ki →
    immediate_sub_redexes_are_values (fill_item ki v).
  Proof.
    destruct ki ; try contradiction ; intros _ ;
    intros [] ? ; try discriminate 1 ;
    injection 1 ; repeat (intros <- || intros _) ; rewrite to_of_val ; eauto.
  Qed.

  Lemma active_item_prim_step_is_head_step ki v σ1 e2 σ2 efs :
    ectx_item_is_active ki →
    prim_step (fill_item ki v) σ1 e2 σ2 efs →
    head_step (fill_item ki v) σ1 e2 σ2 efs.
  Proof.
    intros Hactive Hstep.
    destruct Hstep as [K' e1' e2' E1 E2 Hheadstep] ; simpl in *.
    pose revK' := rev K' ; replace K' with (rev revK') in * by apply rev_involutive ; clearbody revK'.
    destruct revK' as [ | ki' revK' ].
    - by rewrite E1 E2.
    - exfalso.
      rewrite /= fill_app /= in E1.
      assert (immediate_sub_redexes_are_values (fill_item ki v)) as Hsubterms
        by by apply active_item_sub_redexes_values.
      assert (is_Some $ to_val (fill (rev revK') e1'))
        by by eapply Hsubterms.
      eapply val_head_stuck, fill_not_val, eq_None_not_Some in Hheadstep.
      eauto.
  Qed.

End ActiveItem.



(*
 * Safety
 *)

Section Safety.

  Definition safe e σ : Prop :=
    adequate NotStuck e σ (λ _ _, True).

(*
  Lemma safe_alt e σ :
    safe e σ
    ↔
    ∀ t2 σ2 e2,
      rtc step ([e], σ) (t2, σ2) →
      e2 ∈ t2 →
      is_Some (to_val e2) ∨ reducible e2 σ2.
  Proof.
    split.
    - intros [ _ H ]. eauto.
    - intros H. split ; eauto.
  Qed.
*)

  Lemma safe_adequate e σ (φ : val → state → Prop) :
    adequate NotStuck e σ φ →
    safe e σ.
  Proof.
    intros [_ ?]. by split.
  Qed.

(*
  Lemma safe_iff_adequate e σ :
    safe e σ
    ↔
    ∃ (φ : val → Prop), adequate NotStuck e σ φ.
  Proof.
    split.
    - eauto.
    - intros [_ [_ ?]]. by split.
  Qed.

  Lemma not_safe_iff_not_adequate e σ :
    ¬ safe e σ
    ↔
    ∀ (φ : val → Prop), ¬ adequate NotStuck e σ φ.
  Proof.
    split.
    - intros Hnotsafe _ Hsafe%safe_adequate. contradiction.
    - intros Hnotadq [φ Hadq]%safe_iff_adequate. eapply Hnotadq, Hadq.
  Qed.
*)

  Lemma safe_here e σ :
    safe e σ →
    is_Some (to_val e) ∨ reducible e σ.
  Proof.
    intros H. apply H with [e] ; constructor.
  Qed.

  Lemma safe_exec e1 σ1 t2 e2 σ2 :
    e2 ∈ t2 →
    safe e1 σ1 →
    rtc step ([e1], σ1) (t2, σ2) →
    safe e2 σ2.
  Proof.
    intros E2 Hsafe1 Hsteps1to2.
    split ; first done. intros t3 σ3 e3 _ Hsteps2to3 E3.
    apply elem_of_list_split in E2 as (t2' & t2'' & ->).
    apply thread_pool_is_cons_after_exec in Hsteps2to3 as E3' ; destruct E3' as (e3' & t3' & ->).
    assert (e3 ∈ t2' ++ e3' :: t2'' ++ t3') by set_solver.
    eapply Hsafe1 ; try done.
    eapply rtc_transitive ; first eassumption.
    eapply exec_frame_singleton_thread_pool ; eassumption.
  Qed.

  Lemma not_safe_exec e1 σ1 t2 e2 σ2 :
    e2 ∈ t2 →
    ¬ safe e2 σ2 →
    rtc step ([e1], σ1) (t2, σ2) →
    ¬ safe e1 σ1.
  Proof.
    eauto 10 using safe_exec.
  Qed.

  Lemma safe_exec_nofork e1 σ1 e2 σ2 :
    safe e1 σ1 →
    rtc step ([e1], σ1) ([e2], σ2) →
    safe e2 σ2.
  Proof.
    intros. eapply safe_exec ; [ constructor | eassumption | eassumption ].
  Qed.

  Lemma safe_prim_step e1 σ1 e2 σ2 efs :
    safe e1 σ1 →
    prim_step e1 σ1 e2 σ2 efs →
    safe e2 σ2.
  Proof.
    intros. eapply safe_exec ; [ constructor | eassumption | ].
    eapply rtc_l, rtc_refl. apply prim_step_step. eassumption.
  Qed.

  Lemma not_safe_prim_step e1 σ1 e2 σ2 efs :
    ¬ safe e2 σ2 →
    prim_step e1 σ1 e2 σ2 efs →
    ¬ safe e1 σ1.
  Proof.
    eauto using safe_prim_step.
  Qed.

  Lemma stuck_not_safe e1 σ1 :
    stuck e1 σ1 →
    ¬ safe e1 σ1.
  Proof.
    intros Hstuck Hsafe%safe_here.
    destruct Hstuck as [ Hnotval%eq_None_not_Some Hnotred%not_reducible ].
    destruct Hsafe as [ Hval | Hred ] ; contradiction.
  Qed.

  Lemma stuck_fill K e σ :
    stuck e σ →
    stuck (fill K e) σ.
  Proof.
    intros [ Hnotval Hirred ].
    unfold stuck.
    split.
    - by apply fill_not_val.
    - intros e' σ' efs [K1 e1 e'1 E -> Hstep] ; simpl in *.
      eapply step_by_val in E as HK ; try done ; destruct HK as [K'1 -> ].
      rewrite fill_app in E ; apply fill_inj in E.
      eapply Hirred. econstructor ; [|reflexivity|] ; eassumption.
  Qed.

  Lemma safe_fill_inv K e σ :
    safe (fill K e) σ →
    safe e σ.
  Proof.
    intros [_ Hsafe]. split ; first done.
    intros t' σ' e' _ Hsteps He'.
    destruct He' as [ e' t' | e' e'0 t' He' ].
    - eapply exec_fill in Hsteps.
      specialize (Hsafe _ _ _ eq_refl Hsteps (elem_of_list_here _ _)). clear Hsteps.
      destruct Hsafe as [ Hval | Hred ].
      + left. by eapply fill_val.
      + destruct (to_val e') eqn:Hnotval ; first by eauto. right.
        destruct Hred as (_ & σ'' & efs & [ K2 e'2 e''2 Efill _ Hstep ]) ; simpl in *.
        eapply step_by_val in Efill as Efill' ; try eassumption ; destruct Efill' as [K' ->].
        rewrite fill_app in Efill ; apply fill_inj in Efill as ->.
        exists (fill K' e''2), σ'', efs.
        by apply Ectx_step'.
    - eapply exec_fill in Hsteps.
      eapply Hsafe ; eauto using elem_of_list_further.
  Qed.

  Lemma not_safe_fill K e σ :
    ¬ safe e σ →
    ¬ safe (fill K e) σ.
  Proof.
    eauto using safe_fill_inv.
  Qed.

  Lemma not_safe_fill' K e e' σ :
    fill K e = e' →
    ¬ safe e σ →
    ¬ safe e' σ.
  Proof.
    intros <-. apply not_safe_fill.
  Qed.

  (* n-adequacy: *)
  Record nadequate (s : stuckness) (n : nat) e1 σ1 (φ : val → Prop) : Prop := {
    nadequate_result k t2 σ2 v2 :
     nsteps step k ([e1], σ1) (of_val v2 :: t2, σ2) → (k ≤ n)%nat → φ v2;
    nadequate_not_stuck k t2 σ2 e2 :
     s = NotStuck →
     nsteps step k ([e1], σ1) (t2, σ2) →
     (k < n)%nat →
     e2 ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 σ2)
  }.

  (* n-safety: *)
  Definition nsafe n e σ : Prop :=
    nadequate NotStuck n e σ (λ _, True).

End Safety.