From iris.algebra Require Import auth gmap.
From iris_time Require Import Auth_nat.
From iris.base_logic Require Export gen_heap.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From iris_time.heap_lang Require Export lang.
From iris_time.heap_lang Require Import tactics.
From iris.proofmode Require Import proofmode.
From stdpp Require Import fin_maps.
Set Default Proof Using "Type".

Class heapGS Σ := HeapGS {
  heapG_invG : invGS Σ;
  #[global] heapG_gen_heapG :: gen_heapGS loc val Σ;
  #[local] heapG_nat :: inG Σ (authR natUR);
  timeCredit_name : gname ;
}.

Global Instance heapG_irisG `{heapGS Σ} : irisGS heap_lang Σ := {
  iris_invGS := heapG_invG;
  state_interp σ _ κs _ := (gen_heap_interp σ.(heap) ∗
    own timeCredit_name (●nat σ.(tick_counter)))%I;
  num_laters_per_step _ := 0%nat;
  fork_post _ := True%I;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ dq } v" := (pointsto (L:=loc) (V:=val) l dq v%V)
  (at level 20, dq at level 50, format "l  ↦{ dq }  v") : bi_scope.
Notation "l ↦{# q } v" := (pointsto (L:=loc) (V:=val) l (DfracOwn q) v%V)
  (at level 20, q at level 50, format "l  ↦{# q }  v") : bi_scope.
Notation "l ↦ v" :=
  (pointsto (L:=loc) (V:=val) l (DfracOwn 1) v%V) (at level 20) : bi_scope.

Section time_credit.
  Context `{!heapGS Σ}.

  Definition TC  (n : nat) : iProp Σ :=
    ⌜n = 0%nat⌝ ∨ own timeCredit_name (◯nat n).

  (* The use of this lemma is recommended: *)
  Lemma zero_TC_now :
    ⊢ TC 0.
  Proof. iLeft. iPureIntro. reflexivity. Qed.

  (* The following lemma is kept for backwards compatibility. *)
  Lemma zero_TC :
    ⊢ |==> TC 0.
  Proof. iRight. iApply own_unit. Qed.

  Lemma TC_plus m n :
    TC (m + n) ≡ (TC m ∗ TC n)%I.
  Proof.
    rewrite /TC. iSplit.
    + iIntros "[%Heqmn | (Hm & Hn)]".
      - assert (m = 0%nat) by lia.
        assert (n = 0%nat) by lia.
        subst m n.
        eauto.
      - iFrame "Hm Hn".
    + iIntros "([%Heqm | Hm] & [%Heqn | Hn])"; subst.
      - iLeft. eauto.
      - iRight. iFrame "Hn".
      - iRight. rewrite Nat.add_0_r. iFrame "Hm".
      - iRight. iCombine "Hm Hn" as "$".
  Qed.

  Lemma TC_succ n :
    TC (S n) ≡ (TC 1%nat ∗ TC n)%I.
  Proof. by rewrite (eq_refl : S n = 1 + n)%nat TC_plus. Qed.

  Lemma TC_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TC n₁ ⊢ TC n₂.
  Proof.
    rewrite /TC.
    iIntros (?) "[%Heqn1 | Hn1]".
    + iLeft. eauto with lia.
    + iRight. iApply (own_auth_nat_weaken with "Hn1"). eauto. Qed.

  Lemma TC_timeless n :
    Timeless (TC n).
  Proof. exact _. Qed.

  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TC_plus m n : IntoSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof. by rewrite /IntoSep TC_plus. Qed.
  Global Instance from_sep_TC_plus m n : FromSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof. by rewrite /FromSep TC_plus. Qed.
  Global Instance into_sep_TC_succ n : IntoSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof. by rewrite /IntoSep TC_succ. Qed.
  Global Instance from_sep_TC_succ n : FromSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof. by rewrite /FromSep [TC (S n)] TC_succ. Qed.

  Global Instance combine_sep_as_TC_plus m n :
    CombineSepAs (TC m) (TC n) (TC (m + n)).
  Proof using. by rewrite /CombineSepAs TC_plus. Qed.
End time_credit.

(** The tactic [inv_head_step] performs inversion on hypotheses of the shape
[head_step]. The tactic will discharge head-reductions starting from values, and
simplifies hypothesis related to conversions from and to values, and finite map
operations. This tactic is slightly ad-hoc and tuned for proving our lifting
lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Local Hint Extern 0 (base_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (base_reducible_no_obs _ _) => eexists _, _, _; simpl : core.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Local Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : core.
Local Hint Extern 0 (head_step (CAS _ _ _) _ _ _ _ _) => eapply CasSucS : core.
Local Hint Extern 0 (head_step (CAS _ _ _) _ _ _ _ _) => eapply CasFailS : core.
Local Hint Extern 0 (head_step (Alloc _) _ _ _ _ _) => apply alloc_fresh : core.
Local Hint Resolve to_of_val : core.

Global Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.
Global Instance as_val_val v : AsVal (Val v).
Proof. by eexists. Qed.

Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Global Instance alloc_atomic s v : Atomic s (Alloc (Val v)).
Proof. solve_atomic. Qed.
Global Instance load_atomic s v : Atomic s (Load (Val v)).
Proof. solve_atomic. Qed.
Global Instance store_atomic s v1 v2 : Atomic s (Store (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance cas_atomic s v0 v1 v2 : Atomic s (CAS (Val v0) (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance faa_atomic s v1 v2 : Atomic s (FAA (Val v1) (Val v2)).
Proof. solve_atomic. Qed.
Global Instance fork_atomic s e : Atomic s (Fork e).
Proof. solve_atomic. Qed.
Global Instance tick_atomic s v : Atomic s (Tick (Val v)).
Proof. solve_atomic. Qed.
Global Instance skip_atomic s  : Atomic s Skip.
Proof. solve_atomic. Qed.

Local Ltac solve_exec_safe := intros; subst; do 3 eexists; econstructor; eauto.
Local Ltac solve_exec_puredet := simpl; intros; by inv_head_step.
Local Ltac solve_pure_exec :=
  subst; intros ?; apply nsteps_once, pure_base_step_pure_step;
    constructor; [solve_exec_safe | solve_exec_puredet].

Class AsRecV (v : val) (f x : binder) (erec : expr) :=
  as_recv : v = RecV f x erec.
Global Instance AsRecV_recv f x e : AsRecV (RecV f x e) f x e := eq_refl.

(* Pure reductions are automatically performed before any wp_ tactics
   handling impure operations. Since we do not want these tactics to
   unfold locked terms, we do not register this instance explicitely,
   but only activate it by hand in the `wp_rec` tactic, where we
   *actually* want it to unlock. *)
Lemma AsRecV_recv_locked v f x e :
  AsRecV v f x e → AsRecV (locked v) f x e.
Proof. by unlock. Qed.

Global Instance pure_recc f x (erec : expr) :
  PureExec True 1 (Rec f x erec) (Val $ RecV f x erec).
Proof. solve_pure_exec. Qed.
Global Instance pure_pairc (v1 v2 : val) :
  PureExec True 1 (Pair (Val v1) (Val v2)) (Val $ PairV v1 v2).
Proof. solve_pure_exec. Qed.
Global Instance pure_injlc (v : val) :
  PureExec True 1 (InjL $ Val v) (Val $ InjLV v).
Proof. solve_pure_exec. Qed.
Global Instance pure_injrc (v : val) :
  PureExec True 1 (InjR $ Val v) (Val $ InjRV v).
Proof. solve_pure_exec. Qed.

Global Instance pure_beta f x (erec : expr) (v1 v2 : val) `{AsRecV v1 f x erec} :
  PureExec True 1 (App (Val v1) (Val v2)) (subst' x v2 (subst' f v1 erec)).
Proof. unfold AsRecV in *. solve_pure_exec. Qed.

Global Instance pure_unop op v v' :
  PureExec (un_op_eval op v = Some v') 1 (UnOp op (Val v)) (Val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_binop op v1 v2 v' :
  PureExec (bin_op_eval op v1 v2 = Some v') 1 (BinOp op (Val v1) (Val v2)) (Val v').
Proof. solve_pure_exec. Qed.

Global Instance pure_if_true e1 e2 : PureExec True 1 (If (Val $ LitV $ LitBool true) e1 e2) e1.
Proof. solve_pure_exec. Qed.

Global Instance pure_if_false e1 e2 : PureExec True 1 (If (Val $ LitV  $ LitBool false) e1 e2) e2.
Proof. solve_pure_exec. Qed.

Global Instance pure_fst v1 v2 :
  PureExec True 1 (Fst (Val $ PairV v1 v2)) (Val v1).
Proof. solve_pure_exec. Qed.

Global Instance pure_snd v1 v2 :
  PureExec True 1 (Snd (Val $ PairV v1 v2)) (Val v2).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inl v e1 e2 :
  PureExec True 1 (Case (Val $ InjLV v) e1 e2) (App e1 (Val v)).
Proof. solve_pure_exec. Qed.

Global Instance pure_case_inr v e1 e2 :
  PureExec True 1 (Case (Val $ InjRV v) e1 e2) (App e2 (Val v)).
Proof. solve_pure_exec. Qed.

Section lifting.
Context `{heapGS Σ}.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.
Implicit Types efs : list expr.
Implicit Types σ : state.

(** Fork: Not using Texan triples to avoid some unnecessary [True] *)
Lemma wp_fork s E e Φ :
  ▷ WP e @ s; ⊤ {{ _, True }} -∗ ▷ Φ (LitV LitUnit) -∗ WP Fork e @ s; E {{ Φ }}.
Proof.
  iIntros "He HΦ". iApply wp_lift_atomic_base_step; [done|].
  iIntros (σ1 ? κ κs n) "Hσ !>"; iSplit; first by eauto.
  iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step. by iFrame.
Qed.

(** Heap *)
Lemma wp_alloc s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "(Hσ & Hl & _)"; first done.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_alloc_with_meta s E v :
  {{{ True }}} Alloc (Val v) @ s; E {{{ l, RET LitV (LitLoc l); l ↦ v ∗ meta_token l ⊤ }}}.
Proof.
  iIntros (Φ) "_ HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>"; iSplit; first by auto.
  iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iMod (@gen_heap_alloc with "Hσ") as "(Hσ & Hl & Hmeta)"; first done.
  iModIntro; iSplit=> //. iFrame. iApply "HΦ". iFrame.
Qed.

Lemma wp_load s E l dq v :
  {{{ ▷ l ↦{dq} v }}} Load (Val $ LitV $ LitLoc l) @ s; E {{{ RET v; l ↦{dq} v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_store s E l v' v :
  {{{ ▷ l ↦ v' }}} Store (Val $ LitV (LitLoc l)) (Val v) @ s; E
  {{{ RET LitV LitUnit; l ↦ v }}}.
Proof.
  iIntros (Φ) ">Hl HΦ".
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2 σ2 efs Hstep) "_"; inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_fail s E l q v' v1 v2 :
  v' ≠ v1 → vals_cas_compare_safe v' v1 →
  {{{ ▷ l ↦{q} v' }}} CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET LitV (LitBool false); l ↦{q} v' }}}.
Proof.
  iIntros (?? Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
  iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
Qed.

Lemma wp_cas_suc s E l v1 v2 :
  vals_cas_compare_safe v1 v1 →
  {{{ ▷ l ↦ v1 }}} CAS (Val $ LitV $ LitLoc l) (Val v1) (Val v2) @ s; E
  {{{ RET LitV (LitBool true); l ↦ v2 }}}.
Proof.
  iIntros (? Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_faa s E l i1 i2 :
  {{{ ▷ l ↦ LitV (LitInt i1) }}} FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2) @ s; E
  {{{ RET LitV (LitInt i1); l ↦ LitV (LitInt (i1 + i2)) }}}.
Proof.
  iIntros (Φ) ">Hl HΦ". iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros (σ1 ? κ κs n) "[Hσ Htc] !>". iDestruct (@gen_heap_valid with "Hσ Hl") as %?.
  iSplit; first by eauto. iNext; iIntros (v2' σ2 efs Hstep) "_"; inv_head_step.
  iMod (@gen_heap_update with "Hσ Hl") as "[$ Hl]".
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.

Lemma wp_tick s E v :
  {{{ ▷ TC 1 }}} Tick (Val v) @ s ; E {{{ RET v ; True }}}.
Proof.
  iIntros (Φ) ">[%|Htc◯] HΦ"; first done.
  iApply wp_lift_atomic_base_step_no_fork; auto.
  iIntros ([h m] ? κ κs n) "[Hσ Htc●] !>". iDestruct (own_auth_nat_le with "Htc● Htc◯") as %Hle.
  simpl in *. destruct m as [|m]; first lia.
  iSplit; first by eauto. iIntros "!>" (v2' σ2 efs Hstep) "_"; inv_head_step.
  iMod (auth_nat_update_decr _ _ _ 1 with "Htc● Htc◯") as "[Htc● Htc◯]"; first lia.
  assert (∀ n, S n - 1 = n) as -> by lia.
  iModIntro. iSplit=>//. iFrame. by iApply "HΦ".
Qed.
End lifting.
