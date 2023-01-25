From iris_time Require Import TimeCredits.
Open Scope nat_scope.

(* This file offers a short theory of natural integer "generations".
   Generations can serve as indices for thunks; they form the basis
   of a discipline whose aim is to prevent the construction of cyclic
   thunks. *)

(* -------------------------------------------------------------------------- *)

(* A generation is a natural integer. *)

Definition generation := nat.

Implicit Type g : generation.

(* -------------------------------------------------------------------------- *)

(* A bound [b] is an optional generation.
   The bound [Some g] encodes the interval [0, g).
   The bound [None] encodes the infinite set [0, +∞). *)

Implicit Type b : option generation.

(* -------------------------------------------------------------------------- *)

(* [lies_below g b] determines whether [g] is less than [b]. *)

Definition lies_below g b : Prop :=
  match b with
  | None => True
  | Some g' => g < g'
  end.

(* [g] lies below its successor. *)

Lemma lies_below_succ g' g :
  g' ≤ g →
  lies_below g' (Some (g + 1)).
Proof.
  simpl. lia.
Qed.

#[global] Hint Resolve lies_below_succ : thunks.

(* Transitivity. *)

Lemma leq_lies_below g' g b :
  g' ≤ g →
  lies_below g b →
  lies_below g' b.
Proof.
  destruct b; simpl; lia.
Qed.

#[global] Hint Resolve leq_lies_below : thunks.

(* -------------------------------------------------------------------------- *)

(* To each generation, corresponds a namespace. *)

Definition gen_ns g : namespace :=
  nroot .@ "gthunk" .@ g.

(* -------------------------------------------------------------------------- *)

(* [gens_below_gen g] is the union of the namespaces of all generations
   in the interval [0, g). *)

Fixpoint gens_below_gen g : coPset :=
  match g with
  | O => ∅
  | S g' => gens_below_gen g' ∪ ↑(gen_ns g')
  end.

(* -------------------------------------------------------------------------- *)

(* [gens_below_bound b] is the union of the namespaces of all
   generations in the interval [0, b). *)


Definition gens_below_bound b : coPset :=
  match b with
  | None => ⊤
  | Some g => gens_below_gen g
  end.

(* -------------------------------------------------------------------------- *)

(* If [g ≤ g'] holds, then the namespace associated with [g'] is disjoint
   with the union of namespaces [gens_below_gen g]. *)

Lemma gen_ns_disj_gens_below_gen g g' :
  g ≤ g' →
  ↑gen_ns g' ## gens_below_gen g.
Proof.
  revert g'; induction g; cbn; intros g'.
  - set_solver.
  - intros Hg'. rewrite disjoint_union_r. split.
    + eapply IHg. lia.
    + unfold gen_ns. assert (g ≠ g') by lia. solve_ndisj.
Qed.

(* -------------------------------------------------------------------------- *)

(* [gens_below_gen] is monotonic. *)

Lemma gens_below_gen_mono g g' :
  g ≤ g' →
  gens_below_gen g ⊆ gens_below_gen g'.
Proof.
  revert g; induction g'; intros g Hg; cbn.
  - assert (g = 0) by lia; by subst g.
  - destruct (decide (g = S g')).
    + subst g. cbn. done.
    + specialize (IHg' g ltac:(lia)). set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* [gens_below_bound] is monotonic. *)

Lemma gens_below_bound_mono g b :
  lies_below g b →
  gens_below_gen g ⊆ gens_below_bound b.
Proof.
  intros Hg.
  destruct b.
  + apply gens_below_gen_mono. cbn in Hg. lia.
  + cbn. set_solver.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [g < g'] holds, then the namespace associated with [g] is contained
   in the union of namespaces [gens_below_gen g']. *)

Lemma gen_ns_subseteq_gens_below_gen g g' :
  g < g' →
  ↑gen_ns g ⊆ gens_below_gen g'.
Proof.
  intros Hg.
  assert (HH: ↑gen_ns g ⊆ gens_below_gen (S g)).
  { cbn. set_solver. }
  transitivity (gens_below_gen (S g)); auto.
  by apply gens_below_gen_mono.
Qed.

(* -------------------------------------------------------------------------- *)

(* If [lies_below g b] holds, then the namespace associated with [g] is
   contained in the union of namespaces [gens_below_bound b]. *)

Lemma gen_ns_subseteq_gens_below_bound g b :
  lies_below g b →
  ↑gen_ns g ⊆ gens_below_bound b.
Proof.
  intros. destruct b.
  { eauto using gen_ns_subseteq_gens_below_gen. }
  { cbn. set_solver. }
Qed.

(* -------------------------------------------------------------------------- *)

(* A splitting lemma that follows from [gens_below_bound_mono]. *)

Lemma carve_out_gens_below_gen g b :
  lies_below g b →
  gens_below_bound b =
  gens_below_gen g ∪ (gens_below_bound b ∖ gens_below_gen g).
Proof.
  intros Hg. apply union_difference_L. apply gens_below_bound_mono. auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* An inclusion lemma that follows from [gen_ns_subseteq_gens_below_bound].
   If [g] lies below [b] then the namespace associated with [g] is in
   the union of the namespaces associated with the interval [g, b). *)

Lemma gen_ns_subseteq_interval g b :
  lies_below g b →
  ↑gen_ns g ⊆ gens_below_bound b ∖ gens_below_gen g.
Proof.
  intros Hg.
  apply subseteq_difference_r.
  { eauto using gen_ns_disj_gens_below_gen. }
  { eauto using gen_ns_subseteq_gens_below_bound. }
Qed.
