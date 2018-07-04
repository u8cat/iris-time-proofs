From iris.heap_lang Require Import notation.
From stdpp Require Import fin_maps.

Require Import Reduction.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.



(*
 * Translation with any arbitrary expression for [tick]
 *)

Section Translation.

  Variable tick : val.

  Fixpoint translation (e : expr) : expr :=
    match e with
    (* Base lambda calculus *)
    | Var _           => e
    | Rec f x e       => Rec f x (translation e)
    | App e1 e2       => (translation e1) (tick $ translation e2)
    (* Base types and their operations *)
    | Lit _           => e
    | UnOp op e       => UnOp op (tick $ translation e)
    | BinOp op e1 e2  => BinOp op (translation e1) (tick $ translation e2)
    | If e0 e1 e2     => If (tick $ translation e0) (translation e1) (translation e2)
    (* Products *)
    | Pair e1 e2      => Pair (translation e1) (translation e2)
    | Fst e           => Fst (tick $ translation e)
    | Snd e           => Snd (tick $ translation e)
    (* Sums *)
    | InjL e          => InjL (translation e)
    | InjR e          => InjR (translation e)
    | Case e0 e1 e2   =>
        let tick' : val := (λ: "f" "x", "f" #() (tick "x"))%V in
        Case (tick $ translation e0)
          (tick' (λ: <>, translation e1))
          (tick' (λ: <>, translation e2))
    (* Concurrency *)
    | Fork e          => tick $ Fork (translation e)
    (* Heap *)
    | Alloc e         => Alloc (tick $ translation e)
    | Load e          => Load (tick $ translation e)
    | Store e1 e2     => Store (translation e1) (tick $ translation e2)
    | CAS e0 e1 e2    => CAS (translation e0) (translation e1) (tick $ translation e2)
    | FAA e1 e2       => FAA (translation e1) (tick $ translation e2)
    end %E.

  Lemma is_closed_translation xs e :
    is_closed xs e →
    is_closed xs (translation e).
  Proof.
    assert (∀ xs, is_closed xs tick) by (intro ; apply is_closed_of_val).
    revert xs. induction e ; simpl ; unlock ; naive_solver.
  Qed.

  Fixpoint translationV (v : val) : val :=
    match v with
    | @RecV f x e C => @RecV f x (translation e) (is_closed_translation _ _ C)
    | LitV _        => v
    | PairV v1 v2   => PairV (translationV v1) (translationV v2)
    | InjLV v       => InjLV (translationV v)
    | InjRV v       => InjRV (translationV v)
    end.

  Definition translationS (σ : state) : state :=
    translationV <$> σ.

  Let tickCtx : ectx_item := AppRCtx tick.

  Definition translationKi (Ki : ectx_item) : ectx_item :=
    match Ki with
    | AppLCtx e2      => AppLCtx (tick $ translation e2)
    | AppRCtx v1      => AppRCtx (translationV v1)
    | UnOpCtx op      => UnOpCtx op
    | BinOpLCtx op e2 => BinOpLCtx op (tick $ translation e2)
    | BinOpRCtx op v1 => BinOpRCtx op (translationV v1)
    | IfCtx e1 e2     => IfCtx (translation e1) (translation e2)
    | PairLCtx e2     => PairLCtx (translation e2)
    | PairRCtx v1     => PairRCtx (translationV v1)
    | FstCtx          => FstCtx
    | SndCtx          => SndCtx
    | InjLCtx         => InjLCtx
    | InjRCtx         => InjRCtx
    | CaseCtx e1 e2   =>
        let tick' : val := (λ: "f" "x", "f" #() (tick "x"))%V in
        CaseCtx
          (tick' (λ: <>, translation e1))%E
          (tick' (λ: <>, translation e2))%E
    | AllocCtx        => AllocCtx
    | LoadCtx         => LoadCtx
    | StoreLCtx e2    => StoreLCtx (tick $ translation e2)
    | StoreRCtx v1    => StoreRCtx (translationV v1)
    | CasLCtx e1 e2   => CasLCtx (translation e1) (tick $ translation e2)
    | CasMCtx v0 e2   => CasMCtx (translationV v0) (tick $ translation e2)
    | CasRCtx v0 v1   => CasRCtx (translationV v0) (translationV v1)
    | FaaLCtx e2      => FaaLCtx (tick $ translation e2)
    | FaaRCtx v1      => FaaRCtx (translationV v1)
    end.

  Definition translationKi_aux (Ki : ectx_item) : ectx _ :=
    if ectx_item_is_active Ki then
      [ tickCtx ; translationKi Ki ]
    else
      [ translationKi Ki ].

  Definition translationK (K : ectx heap_ectx_lang) : ectx _ :=
    concat (translationKi_aux <$> K).

(*
 * Lemmas about translation
 *)

  Lemma is_closed_translation_inv xs e :
    is_closed xs (translation e) →
    is_closed xs e.
  Proof.
    revert xs. induction e ; naive_solver.
  Qed.

  Lemma translation_subst x e1 e2 :
    translation (subst x e2 e1) = subst x (translation e2) (translation e1).
  Proof.
    induction e1 ;
    unfold subst ; simpl ; fold subst ;
    try case_match ; (* ← this handles the cases of Var and Rec *)
    repeat f_equal ;
    try assumption ;
    rewrite subst_is_closed_nil // ; apply is_closed_of_val.
  Qed.

  Lemma translation_subst' x e1 e2 :
    translation (subst' x e2 e1) = subst' x (translation e2) (translation e1).
  Proof.
    destruct x.
    - reflexivity.
    - apply translation_subst.
  Qed.

  Lemma translation_of_val v :
    translation (of_val v) = of_val (translationV v).
  Proof.
    induction v ; simpl ; firstorder.
  Qed.

  Lemma translation_to_val e v :
    to_val e = Some v →
    to_val (translation e) = Some (translationV v).
  Proof.
    intros <- % of_to_val.
    by rewrite translation_of_val to_of_val.
  Qed.

  Lemma translation_of_val_inv e v' :
    translation e = of_val v' →
    ∃ v, e = of_val v. (* TODO: be more precise? *)
  Proof.
    revert e.
    induction v' as 
      [ (* RecV *) f' x' e1' Hclosed_e1'
      | (* LitV *) lit'
      | (* PairV *) v1' IH1 v2' IH2
      | (* InjLV *) v1' IH1
      | (* InjRV *) v1' IH1
      ] ;
    intros
      [ 
      | (* Rec *) f x e1
      | 
      | (* Lit *) lit
      | | |
      | (* Pair *) e1 e2
      | |
      | (* InjL *) e1
      | (* InjR *) e1
      | | | | | | | ] ;
    try discriminate 1.
    - injection 1 as <- <- <-.
      eassert (Closed (f :b: x :b: []) e1) by by apply is_closed_translation_inv.
      by exists (RecV f x e1).
    - eauto.
    - injection 1 as [v1 ->] % IH1 [v2 ->] % IH2.
      by exists (PairV v1 v2).
    - injection 1 as [v1 ->] % IH1.
      by exists (InjLV v1).
    - injection 1 as [v1 ->] % IH1.
      by exists (InjRV v1).
  Qed.

  Lemma translation_to_val_inv e v' :
    to_val (translation e) = Some v' →
    ∃ v, to_val e = Some v. (* TODO: be more precise? *)
  Proof.
    intros [v ->] % of_to_val % eq_sym % translation_of_val_inv.
    eauto using to_of_val.
  Qed.

  Lemma translation_is_val_inv e :
    is_Some $ to_val (translation e) →
    is_Some $ to_val e.
  Proof.
    intros [_ (v & ->) % translation_to_val_inv]. eauto.
  Qed.

  Lemma translation_not_val_inv e :
    to_val (translation e) = None →
    to_val e = None.
  Proof.
    destruct (to_val e) eqn:? ; last done.
    erewrite translation_to_val ; last eassumption.
    discriminate.
  Qed.

  Lemma translation_not_val e :
    to_val e = None →
    to_val (translation e) = None.
  Proof.
    destruct (to_val (translation e)) eqn:E ; last done.
    apply translation_to_val_inv in E as (? & ->). discriminate.
  Qed.

  Lemma translation_injective e1 e2 :
    translation e1 = translation e2 →
    e1 = e2.
  Proof. (* this is slow because there are 19² subgoals… *)
    (* by induction on e1, generalizing over e2: *)
    revert e2 ; induction e1 ; intros e2 ;
    (* reasoning by case on e2 *)
    destruct e2 ;
    (* eliminating all spurious cases, since e2 must have the same head
       constructor as e1: *)
    try discriminate 1 ; injection 1 ;
    (* all subgoals are straightforward by applying the induction hypotheses: *)
    intros ; f_equal ; auto.
  Qed.

  Lemma translationV_injective v1 v2 :
    translationV v1 = translationV v2 →
    v1 = v2.
  Proof.
    intros E.
    apply of_val_inj, translation_injective.
    rewrite 2! translation_of_val ; f_equal.
    done.
  Qed.

  Lemma translation_fill_item Ki e :
    translation (fill_item Ki e) = fill (translationKi_aux Ki) (translation e).
  Proof.
    destruct Ki ; rewrite /= ? translation_of_val ; reflexivity.
  Qed.

  Lemma translation_fill_item_active (ki : ectx_item) v :
    ectx_item_is_active ki →
    translation (fill_item ki v) = fill_item (translationKi ki) (tick (translationV v)).
  Proof.
    rewrite translation_fill_item translation_of_val.
    unfold translationKi_aux ; destruct (ectx_item_is_active ki) ; last contradiction.
    reflexivity.
  Qed.

  Lemma is_active_translationKi ki :
    ectx_item_is_active ki →
    ectx_item_is_active (translationKi ki).
  Proof.
    by destruct ki.
  Qed.

  Lemma translation_fill K e :
    translation (fill K e) = fill (translationK K) (translation e).
  Proof.
    revert e ; induction K ; intros e.
    - done.
    - rewrite /= fill_app - translation_fill_item //.
  Qed.

  Lemma lookup_translationS_None σ l :
    σ !! l = None →
    translationS σ !! l = None.
  Proof.
    intros H. by rewrite lookup_fmap H.
  Qed.

  Lemma lookup_translationS_Some σ l v :
    σ !! l = Some v →
    translationS σ !! l = Some (translationV v).
  Proof.
    intros H. by rewrite lookup_fmap H.
  Qed.

  Lemma lookup_translationS_is_Some σ l :
    is_Some (σ !! l) →
    is_Some (translationS σ !! l).
  Proof.
    destruct 1. eauto using lookup_translationS_Some.
  Qed.

  Lemma lookup_translationS_None_inv σ l :
    translationS σ !! l = None →
    σ !! l = None.
  Proof.
    unfold translationS ; rewrite lookup_fmap.
    destruct (σ !! l) eqn:E ; rewrite E ; first discriminate.
    done.
  Qed.

  Lemma lookup_translationS_Some_inv σ l v' :
    translationS σ !! l = Some v' →
    ∃ v,  σ !! l = Some v  ∧  v' = translationV v.
  Proof.
    rewrite lookup_fmap.
    destruct (σ !! l) eqn:E ; rewrite E ; last discriminate.
    intros ? % Some_inj ; eauto.
  Qed.

  Lemma lookup_translationS_is_Some_inv σ l :
    is_Some (translationS σ !! l) →
    is_Some (σ !! l).
  Proof.
    intros [_ (? & ? & _) % lookup_translationS_Some_inv]. eauto.
  Qed.

  Lemma translationS_insert l v σ :
    translationS (<[l := v]> σ) = <[l := translationV v]> (translationS σ).
  Proof.
    apply fmap_insert.
  Qed.

  Lemma un_op_eval_translation op v v' :
    un_op_eval op v = Some v' →
    un_op_eval op (translationV v) = Some (translationV v').
  Proof.
    intros H.
    destruct op ;
    destruct v ; try discriminate H ;
    simpl ; case_match ; try discriminate H ;
    by injection H as <-.
  Qed.

  Local Lemma _eval_EqOp_bool_decide v1 v2 :
    bin_op_eval EqOp v1 v2 = Some $ LitV $ LitBool $ bool_decide (v1 = v2).
  Proof.
    destruct v1, v2 ; try done ;
    simpl ; case_match ; try done ;
    simpl ; case_match ; try done ;
    repeat f_equal ; apply bool_decide_iff ; naive_solver.
  Qed.

  Local Lemma _bool_decide_eq_translationV v1 v2 :
    bool_decide (v1 = v2) = bool_decide (translationV v1 = translationV v2).
  Proof.
    apply bool_decide_iff ; split ; intros H.
    - by rewrite H.
    - by eapply translationV_injective.
  Qed.

  Lemma bin_op_eval_translation op v1 v2 v' :
    bin_op_eval op v1 v2 = Some v' →
    bin_op_eval op (translationV v1) (translationV v2) = Some (translationV v').
  Proof.
    intros H.
    destruct op ; try (
      destruct v1, v2 ; try discriminate H ;
      simpl ; case_match ; try discriminate H ;
      simpl ; case_match ; try discriminate H ;
      by injection H as <-
    ).
    (* Remaining case: op = EqOp *)
    rewrite _eval_EqOp_bool_decide in H ; injection H as <-.
    by rewrite _eval_EqOp_bool_decide - _bool_decide_eq_translationV.
  Qed.

  Lemma un_op_eval_translation_inv op v v' :
    un_op_eval op (translationV v) = Some v' →
    un_op_eval op v = Some v'.
  Proof.
    intros H.
    destruct op ;
    destruct v ; try discriminate H ;
    done.
  Qed.

  Lemma bin_op_eval_translation_inv op v1 v2 v' :
    bin_op_eval op (translationV v1) (translationV v2) = Some v' →
    bin_op_eval op v1 v2 = Some v'.
  Proof.
    intros H.
    destruct op ; try (
      destruct v1, v2 ; try discriminate H ;
      done
    ).
    (* Remaining case: op = EqOp *)
    rewrite -> _eval_EqOp_bool_decide in *. injection H as <-.
    by rewrite - _bool_decide_eq_translationV.
  Qed.



  Lemma translationV_lit lit :
    translationV #lit = #lit.
  Proof.
    done.
  Qed.

  Lemma translationV_lit_inv v lit :
    translationV v = #lit →
    v = #lit.
  Proof.
    destruct v ; try discriminate. done.
  Qed.
  Lemma translationV_lit_inv_expr v lit :
    of_val (translationV v) = (#lit)%E →
    v = #lit.
  Proof.
    change (#lit)%E with (of_val (#lit)%V).
    by intros ? % of_val_inj % translationV_lit_inv.
  Qed.

(*
 * Translation as a type class
 *)

Class Translates e e' := translates : (translation e = e').
Class TranslatesV v v' := translatesV : (translationV v = v').

Program Instance Translates_Var: Translates (Var x) (Var x).
Program Instance Translates_Rec: Translates e e' → Translates (Rec f x e ) (Rec f x e').
Program Instance Translates_App: Translates e1 e1' → Translates e2 e2' →
                                 Translates (e1 e2) (e1' (tick e2')).
Program Instance Translates_Lit: Translates (Lit l) (Lit l).
Program Instance Translates_UnOp: Translates e e' → Translates (UnOp op e) (UnOp op (tick e')).
Program Instance Translates_BinOp: Translates e1 e1' → Translates e2 e2' →
                                   Translates (BinOp op e1 e2) (BinOp op e1' (tick e2')).
Program Instance Translates_If: Translates e0 e0' → Translates e1 e1' → Translates e2 e2' →
                                Translates (If e0 e1 e2) (If (tick e0') e1' e2').
Program Instance Translates_Pair: Translates e1 e1' → Translates e2 e2' →
                                Translates (Pair e1 e2) (Pair e1' e2').
Program Instance Translates_Fst: Translates e e' → Translates (Fst e) (Fst (tick e')).
Program Instance Translates_Snd: Translates e e' → Translates (Snd e) (Snd (tick e')).
Program Instance Translates_InjL: Translates e e' → Translates (InjL e) (InjL e').
Program Instance Translates_InjR: Translates e e' → Translates (InjR e) (InjR e').
Let tick' : val := (λ: "f" "x", "f" #() (tick "x"))%V.
Program Instance Translates_Case: Translates e0 e0' → Translates e1 e1' → Translates e2 e2' →
                                  Translates (Case e0 e1 e2) (Case (tick e0') (tick' (λ: <>, e1')%E) (tick' (λ: <>, e2')%E)).
Program Instance Translates_Fork: Translates e e' → Translates (Fork e) (tick (Fork e')).
Program Instance Translates_Alloc: Translates e e' → Translates (Alloc e) (Alloc (tick e')).
Program Instance Translates_Load: Translates e e' → Translates (Load e) (Load (tick e')).
Program Instance Translates_Store: Translates e1 e1' → Translates e2 e2' →
                                   Translates (Store e1 e2) (Store e1' (tick e2')).
Program Instance Translates_CAS: Translates e0 e0' → Translates e1 e1' → Translates e2 e2' →
                                 Translates (CAS e0 e1 e2) (CAS e0' e1' (tick e2')).
Program Instance Translates_FAA: Translates e1 e1' → Translates e2 e2' →
                                 Translates (FAA e1 e2) (FAA e1' (tick e2')).

Instance Translates_of_val: TranslatesV v v' → Translates (of_val v) (of_val v').
  Proof. intros v v' <-. apply translation_of_val. Qed.

Local Lemma Closed_Translates {xs e e'} :
(*   is_closed xs e → translation e = e' → is_closed xs e'. *)
(*   Closed xs e → Translates e e' → Closed xs e'. *)
  Translates e e' → Closed xs e → Closed xs e'.
  Proof. intros <- C. by apply is_closed_translation. Defined.

Program Instance TranslatesV_RecV: ∀ {T : Translates e e'},
                                   ∀ {C : Closed (f :b: x :b: []) e},
                                   TranslatesV (RecV f x e) (@RecV f x e' (Closed_Translates T C)).
Program Instance TranslatesV_LitV: TranslatesV (LitV l) (LitV l).
Program Instance TranslatesV_PairV: TranslatesV e1 e1' → TranslatesV e2 e2' →
                                    TranslatesV (PairV e1 e2) (PairV e1' e2').
Program Instance TranslatesV_InjLV: TranslatesV e e' → TranslatesV (InjLV e) (InjLV e').
Program Instance TranslatesV_InjRV: TranslatesV e e' → TranslatesV (InjRV e) (InjRV e').

Solve All Obligations with repeat (intros <- || intros ?) ; reflexivity.

Definition expr_translation_of e : Set := { e' : expr | Translates e e' }.
Definition infer_Translation {e} {e'} {T : Translates e e'} : expr_translation_of e :=
  exist (Translates e) e' T.

Definition val_translation_of v : Set := { v' : val | TranslatesV v v' }.
Definition infer_TranslationV {v} {v'} {T : TranslatesV v v'} : val_translation_of v :=
  exist (TranslatesV v) v' T.

(* for some reason, the instance `TranslatesV_RecV` does not work well: *)
Ltac solve_val_translation_of_RecV :=
  econstructor ; apply TranslatesV_RecV.
Hint Extern 0 (val_translation_of (RecV _ _ _)) => solve_val_translation_of_RecV.

(* examples: *)

(*
Definition e : expr := #42.
Let e'_aux : expr_translation_of e := infer_Translation.
Definition e' : expr := Eval simpl in proj1_sig e'_aux.
Instance: Translates e e' := proj2_sig e'_aux.
Reset e.

Definition e : expr := (InjR #34, InjL #57).
Let e'_aux : expr_translation_of e := infer_Translation.
Definition e' : expr := Eval simpl in proj1_sig e'_aux.
Instance: Translates e e' := proj2_sig e'_aux.
Reset e.

Definition e : expr := λ: "x" "y", "x" "y" + #1.
Let e'_aux : expr_translation_of e := infer_Translation.
Definition e' : expr := Eval simpl in proj1_sig e'_aux.
Instance: Translates e e' := proj2_sig e'_aux.
Reset e.

Definition v : val := #42.
Let v'_aux : val_translation_of v := infer_TranslationV.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v.

Definition v : val := (InjRV #34, InjLV #57).
Let v'_aux : val_translation_of v := infer_TranslationV.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v.

Definition v : val := RecV <> "x" (#())%E.
Let v'_aux : val_translation_of v. Proof. unfold v ; by auto. Defined.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v'_aux.
Fail Let v'_aux : val_translation_of v := infer_TranslationV.
Fail Instance: TranslatesV v _ := _.
Fail Instance: TranslatesV (RecV <> "x" (#())%E) _ := _.
(* Instance: TranslatesV v (RecV <> "x" (#())%E) := _. apply TranslatesV_RecV. *)
Instance: TranslatesV v (@RecV <> "x" (#())%E (Closed_Translates _ _)) := TranslatesV_RecV.
Let v'_aux : val_translation_of v := infer_TranslationV.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v.

Definition v : val := RecV <> "x" ("x" #1)%E.
Let v'_aux : val_translation_of v. Proof. unfold v ; by auto. Defined.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v'_aux.
Fail Let v'_aux : val_translation_of v := infer_TranslationV.
Fail Instance: TranslatesV v _ := _.
(* Instance: Translates ("x" #1) _ := _. *)
Instance: TranslatesV (RecV <> "x" ("x" #1)%E) (@RecV <> "x" ("x" (tick #1))%E (Closed_Translates _ _)) :=
  TranslatesV_RecV.
(* Instance: TranslatesV v (RecV <> "x" #()) := _. apply TranslatesV_RecV. *)
Instance: TranslatesV v (@RecV <> "x" ("x" (tick #1))%E (Closed_Translates _ _)) := _.
Let v'_aux : val_translation_of v := infer_TranslationV.
Definition v' : val := Eval simpl in proj1_sig v'_aux.
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v.

Definition v : val := λ: "x", "x" #1.
Let v'_aux : val_translation_of v. Proof. unlock v ; by auto. Defined.
Definition v' : val := Eval cbn [proj1_sig] in proj1_sig v'_aux.
Print v'_aux. Print v'. (* ← ugly because of unlock *)
Instance: TranslatesV v v' := proj2_sig v'_aux.
Reset v.
*)

End Translation.



(*
 * (Partial) Inverse translation
 *)

Section InvTranslation.

  Fixpoint invtranslation (e : expr) : expr :=
    match e with
    (* Base lambda calculus *)
    | Var _                      => e
    | Rec f x e                  => Rec f x (invtranslation e)
    | App e1 (App tick e2)       => (invtranslation e1) (invtranslation e2)
    (* Base types and their operations *)
    | Lit _                      => e
    | UnOp op (App tick e)       => UnOp op (invtranslation e)
    | BinOp op e1 (App tick e2)  => BinOp op (invtranslation e1) (invtranslation e2)
    | If (App tick e0) e1 e2     => If (invtranslation e0) (invtranslation e1) (invtranslation e2)
    (* Products *)
    | Pair e1 e2                 => Pair (invtranslation e1) (invtranslation e2)
    | Fst (App tick e)           => Fst (invtranslation e)
    | Snd (App tick e)           => Snd (invtranslation e)
    (* Sums *)
    | InjL e                     => InjL (invtranslation e)
    | InjR e                     => InjR (invtranslation e)
    | Case (App tick e0) (App tick'1 (Rec BAnon BAnon e1)) (App tick'2 (Rec BAnon BAnon e2)) =>
        Case (invtranslation e0) (invtranslation e1) (invtranslation e2)
    (* Concurrency *)
    | App tick (Fork e)          => Fork (invtranslation e)
    (* Heap *)
    | Alloc (App tick e)         => Alloc (invtranslation e)
    | Load (App tick e)          => Load (invtranslation e)
    | Store e1 (App tick e2)     => Store (invtranslation e1) (invtranslation e2)
    | CAS e0 e1 (App tick e2)    => CAS (invtranslation e0) (invtranslation e1) (invtranslation e2)
    | FAA e1 (App tick e2)       => FAA (invtranslation e1) (invtranslation e2)
    | _ => #42
    end %E.

  Lemma is_closed_invtranslation xs e :
    is_closed xs e →
    is_closed xs (invtranslation e).
  Proof.
    revert xs e.
    fix IH 2 => xs [] /= * ;
    repeat case_match ; naive_solver.
  Qed.

  Fixpoint invtranslationV (v : val) : val :=
    match v with
    | @RecV f x e C => @RecV f x (invtranslation e) (is_closed_invtranslation _ _ C)
    | LitV _        => v
    | PairV v1 v2   => PairV (invtranslationV v1) (invtranslationV v2)
    | InjLV v       => InjLV (invtranslationV v)
    | InjRV v       => InjRV (invtranslationV v)
    end.

  Lemma invtranslation_of_val v :
    invtranslation (of_val v) = of_val (invtranslationV v).
  Proof.
    induction v ; simpl ; firstorder.
  Qed.

  Lemma invtranslation_translation tick e :
    invtranslation (translation tick e) = e.
  Proof.
    induction e ; simpl ; firstorder.
  Qed.

  Lemma invtranslationV_translationV tick v :
    invtranslationV (translationV tick v) = v.
  Proof.
    apply of_val_inj. rewrite - invtranslation_of_val - translation_of_val.
    apply invtranslation_translation.
  Qed.

End InvTranslation.



(*
 * Characterizing expressions that are left invariant by translation
 *)

Section ClosureFree.

  Fixpoint closure_free (v : val) : bool :=
    match v with
    | RecV _ _ _ => false
    | LitV _ => true
    | PairV v1 v2 => closure_free v1 && closure_free v2
    | InjLV v1 => closure_free v1
    | InjRV v1 => closure_free v1
    end.

  Lemma closure_free_is_translationV_invariant (tick : val) v :
    closure_free v →
    translationV tick v = v.
  Proof.
    intros ?.
    induction v as
      [ (* RecV *) f x e1 Hclosed_e1
      | (* LitV *) lit
      | (* PairV *) v1 IH1 v2 IH2
      | (* InjLV *) v1 IH1
      | (* InjRV *) v1 IH1
      ] ; simpl.
    - contradiction.
    - done.
    - rewrite -> IH1, IH2 ; naive_solver.
    - rewrite IH1 ; naive_solver.
    - rewrite IH1 ; naive_solver.
  Qed.

  Lemma closure_free_is_invtranslationV_invariant v :
    closure_free v →
    invtranslationV v = v.
  Proof.
    intros ?.
    induction v as
      [ (* RecV *) f x e1 Hclosed_e1
      | (* LitV *) lit
      | (* PairV *) v1 IH1 v2 IH2
      | (* InjLV *) v1 IH1
      | (* InjRV *) v1 IH1
      ] ; simpl.
    - contradiction.
    - done.
    - rewrite -> IH1, IH2 ; naive_solver.
    - rewrite IH1 ; naive_solver.
    - rewrite IH1 ; naive_solver.
  Qed.

  Lemma closure_free_translationV (tick : val) v :
    closure_free v →
    closure_free (translationV tick v).
  Proof.
    intros Hv. by rewrite (closure_free_is_translationV_invariant tick v Hv).
  Qed.

  Lemma closure_free_invtranslationV v :
    closure_free v →
    closure_free (invtranslationV v).
  Proof.
    intros Hv. by rewrite (closure_free_is_invtranslationV_invariant v Hv).
  Qed.

  Lemma closure_free_translationV_iff (tick : val) v :
    closure_free v  ↔  closure_free (translationV tick v).
  Proof.
    split.
    - apply closure_free_translationV.
    - intros H % closure_free_invtranslationV. by rewrite invtranslationV_translationV in H.
  Qed.

  Lemma closure_free_predicate (φ : val → Prop) :
    (∀ (v : val), φ v → closure_free v) →
    ∀ (v : val),
      φ v → φ (invtranslationV v).
  Proof.
    intros Hφ v H.
    by specialize (Hφ _ H) as -> % closure_free_is_invtranslationV_invariant.
  Qed.

End ClosureFree.
