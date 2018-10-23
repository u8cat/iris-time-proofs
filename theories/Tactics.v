From iris.heap_lang Require Export lang tactics.



(*
 * Tactics for reducing terms
 *)

Ltac simpl_to_of_val :=
  rewrite /= ? to_of_val //.

Ltac rewrite_into_values :=
  repeat (lazymatch goal with
  | H : to_val _ = Some _ |- _ =>
      eapply of_to_val in H as <-
  end).

Ltac reshape_expr_ordered b e tac :=
  let rec go K e :=
  match e with
  | _ =>
      lazymatch b with
      | false => tac K e
      | true  => fail
      end
  | App ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (AppRCtx v1 :: K) e2)
  | App ?e1 ?e2 => go (AppLCtx e2 :: K) e1
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2)
  | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (StoreRCtx v1 :: K) e2)
  | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1
  | CAS ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasRCtx v0 v1 :: K) e2)
     | go (CasMCtx v0 e2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0
  | FAA ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (FaaRCtx v1 :: K) e2)
  | FAA ?e1 ?e2 => go (FaaLCtx e2 :: K) e1
  | _ =>
      lazymatch b with
      | false => fail
      | true  => tac K e
      end
  end in go (@nil ectx_item) e.

Local Lemma head_step_into_val e σ e' v' σ' efs :
  IntoVal e' v' →
  head_step e σ (of_val v') σ' efs →
  head_step e σ e' σ' efs.
Proof.
  intros Hval Hstep. by erewrite of_to_val in Hstep.
Qed.

Ltac prim_step :=
  lazymatch goal with
  | |- prim_step ?e _ _ _ _ =>
      reshape_expr_ordered true e ltac:(fun K e' =>
        esplit with K e' _ ; [ reflexivity | reflexivity | ] ;
        (idtac + eapply head_step_into_val) ; econstructor
      )
  end ;
  simpl_to_of_val.