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
  | App ?e1 ?e2 => reshape_val e2 ltac:(fun v2 => go (AppLCtx v2 :: K) e1)
  | App ?e1 ?e2 => go (AppRCtx e1 :: K) e2
  | UnOp ?op ?e => go (UnOpCtx op :: K) e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e2 ltac:(fun v2 => go (BinOpLCtx op v2 :: K) e1)
  | BinOp ?op ?e1 ?e2 => go (BinOpRCtx op e1 :: K) e2
  | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0
  | Pair ?e1 ?e2 => reshape_val e2 ltac:(fun v2 => go (PairLCtx v2 :: K) e1)
  | Pair ?e1 ?e2 => go (PairRCtx e1 :: K) e2
  | Fst ?e => go (FstCtx :: K) e
  | Snd ?e => go (SndCtx :: K) e
  | InjL ?e => go (InjLCtx :: K) e
  | InjR ?e => go (InjRCtx :: K) e
  | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0
  | Alloc ?e => go (AllocCtx :: K) e
  | Load ?e => go (LoadCtx :: K) e
  | Store ?e1 ?e2 => reshape_val e2 ltac:(fun v2 => go (StoreLCtx v2 :: K) e1)
  | Store ?e1 ?e2 => go (StoreRCtx e1 :: K) e2
  | CAS ?e0 ?e1 ?e2 => reshape_val e2 ltac:(fun v2 => first
     [ reshape_val e1 ltac:(fun v1 => go (CasLCtx v1 v2 :: K) e0)
     | go (CasMCtx e0 v2 :: K) e1 ])
  | CAS ?e0 ?e1 ?e2 => go (CasRCtx e0 e1 :: K) e2
  | FAA ?e1 ?e2 => reshape_val e2 ltac:(fun v2 => go (FaaLCtx v2 :: K) e1)
  | FAA ?e1 ?e2 => go (FaaRCtx e1 :: K) e2
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
  intros Hval Hstep. by rewrite Hval in Hstep.
Qed.

Ltac prim_step :=
  lazymatch goal with
  | |- prim_step ?e _ _ _ _ =>
      reshape_expr_ordered true e ltac:(fun K e' =>
        esplit with K e' _ ; [ reflexivity | reflexivity | ] ;
        (idtac + (eapply head_step_into_val; [apply _|])) ; econstructor
      )
  end ;
  simpl_to_of_val.
