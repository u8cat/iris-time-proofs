From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksFull.
Open Scope nat_scope.

(* -------------------------------------------------------------------------- *)

(* A short theory of generations. *)

(* A generation is a natural integer. *)

Definition generation := nat.

Implicit Type g : generation.

(* To each generation, corresponds a namespace. *)

Local Definition gen_ns g : namespace :=
  nroot .@ "gthunk" .@ g.

(* The union of the namespaces of all generations in [0, g). *)

Local Fixpoint gens_below_gen g : coPset :=
  match g with
  | O => ∅
  | S g' => gens_below_gen g' ∪ ↑(gen_ns g')
  end.

(* A bound is an optional generation.
   The bound [Some g] encodes the interval [0, g).
   The bound [None] encodes the infinite set [0, +∞). *)

Implicit Type bound : option generation.

(* The union of the namespaces of all generations in [0, bound). *)

Local Definition gens_below_bound bound : coPset :=
  match bound with
  | None => ⊤
  | Some g => gens_below_gen g
  end.

(* [lies_below g bound] determines whether [g] is less than [bound]. *)

Definition lies_below g bound : Prop :=
  match bound with
  | None => True
  | Some g' => g < g'
  end.

(* [g] lies below its successor. *)

Lemma lies_below_succ g :
  lies_below g (Some (g + 1)).
Proof.
  simpl. lia.
Qed.

#[global] Hint Resolve lies_below_succ : thunks.

(* If [g ≤ g'] holds, then the namespace associated with [g'] is disjoint
   with the union of namespaces [gens_below_gen g]. *)

Local Lemma gen_ns_disj_gens_below_gen g g' :
  g ≤ g' →
  ↑gen_ns g' ## gens_below_gen g.
Proof.
  revert g'; induction g; cbn; intros g'.
  - set_solver.
  - intros Hg'. rewrite disjoint_union_r. split.
    + eapply IHg. lia.
    + unfold gen_ns. assert (g ≠ g') by lia. solve_ndisj.
Qed.

(* [gens_below_gen] is monotonic. *)

Local Lemma gens_below_gen_mono g g' :
  g ≤ g' →
  gens_below_gen g ⊆ gens_below_gen g'.
Proof.
  revert g; induction g'; intros g Hg; cbn.
  - assert (g = 0) by lia; by subst g.
  - destruct (decide (g = S g')).
    + subst g. cbn. done.
    + specialize (IHg' g ltac:(lia)). set_solver.
Qed.

(* [gens_below_bound] is monotonic. *)

Local Lemma gens_below_bound_mono g bound :
  lies_below g bound →
  gens_below_gen g ⊆ gens_below_bound bound.
Proof.
  intros Hg.
  destruct bound.
  + apply gens_below_gen_mono. cbn in Hg. lia.
  + cbn. set_solver.
Qed.

(* If [g < g'] holds, then the namespace associated with [g] is contained
   in the union of namespaces [gens_below_gen g']. *)

Local Lemma gen_ns_subseteq_gens_below_gen g g' :
  g < g' →
  ↑gen_ns g ⊆ gens_below_gen g'.
Proof.
  intros Hg.
  assert (HH: ↑gen_ns g ⊆ gens_below_gen (S g)).
  { cbn. set_solver. }
  transitivity (gens_below_gen (S g)); auto.
  by apply gens_below_gen_mono.
Qed.

(* If [lies_below g bound] holds, then the namespace associated with [g] is
   contained in the union of namespaces [gens_below_bound bound]. *)

Local Lemma gen_ns_subseteq_gens_below_bound g bound :
  lies_below g bound →
  ↑gen_ns g ⊆ gens_below_bound bound.
Proof.
  intros. destruct bound.
  { eauto using gen_ns_subseteq_gens_below_gen. }
  { cbn. set_solver. }
Qed.

(* A splitting lemma that follows from [gens_below_bound_mono]. *)

Local Lemma carve_out_gens_below_gen g bound :
  lies_below g bound →
  gens_below_bound bound =
  gens_below_gen g ∪ (gens_below_bound bound ∖ gens_below_gen g).
Proof.
  intros Hg. apply union_difference_L. apply gens_below_bound_mono. auto.
Qed.

(* An inclusion lemma that follows from [gen_ns_subseteq_gens_below_bound].
   If [g] lies below [bound] then the namespace associated with [g] is in
   the union of the namespaces associated with the interval [g, bound). *)

Local Lemma gen_ns_subseteq_interval g bound :
  lies_below g bound →
  ↑gen_ns g ⊆ gens_below_bound bound ∖ gens_below_gen g.
Proof.
  intros Hg.
  apply subseteq_difference_r.
  { eauto using gen_ns_disj_gens_below_gen. }
  { eauto using gen_ns_subseteq_gens_below_bound. }
Qed.

(* -------------------------------------------------------------------------- *)

Section Gthunks.

  Notation valO := (valO heap_lang).
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
  Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
  Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
  Context `{na_invG Σ}.
  Notation iProp := (iProp Σ).
  Open Scope nat_scope.

  Implicit Type p : na_inv_pool_name.
  Implicit Type t : loc.

  Definition own_gens_below_bound p bound :=
    na_own p (gens_below_bound bound).
  (* TODO own_gens_below_bound is part of public spec;
          shorter name needed *)

  Local Lemma own_gens_below_alloc :
    ⊢ |==> ∃ p, own_gens_below_bound p None.
  Proof using. iApply na_alloc. Qed.

  (* TODO parameterize with R *)
  Definition Gthunk p g t n φ : iProp :=
    let F := ↑(gen_ns g) in
    let R := own_gens_below_bound p (Some g) in
    Thunk p F t n R φ.

  Global Instance Gthunk_persistent p g t n φ :
    Persistent (Gthunk p g t n φ).
  Proof using.
    exact _.
  Qed.

  Lemma Gthunk_weaken p g t n1 n2 φ :
    n1 ≤ n2 →
    Gthunk p g t n1 φ -∗
    Gthunk p g t n2 φ.
  Proof using.
    iIntros (?) "Hthunk".
    by iApply thunk_increase_debt.
  Qed.

  Lemma Gthunk_consequence p g t n1 n2 φ ψ E :
    (∀ v, TC n2 -∗ □ φ v ={⊤}=∗ □ ψ v) -∗
    Gthunk p g t  n1       φ  ={E}=∗
    Gthunk p g t (n1 + n2) ψ.
  Proof.
    rewrite /Gthunk.
    iIntros "Hupdate Hthunk".
    iApply (thunk_consequence with "Hthunk [Hupdate]").
    iIntros (v) "HR Htc Hv".
    iFrame "HR".
    iApply ("Hupdate" with "Htc").
    iAssumption.
  Qed.

  Lemma Gthunk_pay k E p g t n φ :
    ↑ThunkPayment t ⊆ E →
    TC k -∗ Gthunk p g t n φ ={E}=∗ Gthunk p g t (n-k) φ.
  Proof using.
    rewrite /Gthunk.
    iIntros (?) "Htc Hthunk".
    by iMod (thunk_pay with "Hthunk Htc").
  Qed.

  Lemma create_spec p g n φ f :
    let token := own_gens_below_bound p (Some g) in
    TC_invariant -∗
    {{{ TC 3 ∗ isAction f n token φ }}}
      « create f »
    {{{ t, RET #t ; Gthunk p g t n φ }}}.
  Proof.
    iIntros "#HtickInv" (Φ) "!# H Post".
    by wp_apply (thunk_create with "HtickInv H").
  Qed.

  Lemma force_spec p g bound t φ :
    lies_below g bound →
    let token := own_gens_below_bound p bound in
    TC_invariant -∗
    {{{ TC 11 ∗ Gthunk p g t 0 φ ∗ token }}}
    « force #t »
    {{{ v, RET «v» ; ThunkVal t v ∗ □ φ v ∗ token }}}.
  Proof using.
    rewrite /Gthunk.
    intros Hg. iIntros "#HtickInv" (Φ) "!# (TC & H & Htoken) Post".
    rewrite /own_gens_below_bound.
    rewrite (carve_out_gens_below_gen _ _ Hg).
    iDestruct (na_own_union with "Htoken") as "[Htoken1 Htoken2]".
    { set_solver. }
    (* Both tokens are required here. *)
    wp_apply (thunk_force with "HtickInv [$TC $H $Htoken2 $Htoken1]").
    { eauto using gen_ns_subseteq_interval. }
    (* Conclude. *)
    iIntros (v) "(#Hv & #Hval & Htoken1 & Htoken2)".
    iApply "Post". iFrame "Hv Hval".
    iDestruct (na_own_union with "[$Htoken2 $Htoken1]") as "Htoken".
    { set_solver. }
    iFrame "Htoken".
  Qed.

End Gthunks.
