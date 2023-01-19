From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time Require Import TimeCredits Auth_max_nat Thunks.
From iris_time Require Import ThunksCode.

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

Local Definition lies_below g bound : Prop :=
  match bound with
  | None => True
  | Some g' => g < g'
  end.

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

  Implicit Type p : na_inv_pool_name.
  Implicit Type t : loc.
  Implicit Type n m k : nat.
  Implicit Type f : val.

  Definition own_gens_below_bound p bound :=
    na_own p (gens_below_bound bound).

  Local Lemma own_gens_below_alloc :
    ⊢ |==> ∃ p, own_gens_below_bound p None.
  Proof using. iApply na_alloc. Qed.

  (* TODO parameterize with R *)
  Definition Gthunk p g γ t n φ : iProp :=
    Thunk p (gen_ns g) γ t n
            (own_gens_below_bound p (Some g)) φ.

  Global Instance Gthunk_persistent p g γ t n φ :
    Persistent (Gthunk p g γ t n φ).
  Proof using. exact _. Qed.

  Lemma Gthunk_weaken p g γ t n₁ n₂ φ :
    (n₁ ≤ n₂)%nat →
    Gthunk p g γ t n₁ φ -∗
    Gthunk p g γ t n₂ φ.
  Proof using. iIntros (?) "H". by iApply Thunk_weaken. Qed.

  Lemma Gthunk_consequence p g γ t n m φ ψ :
    (∀ v, TC m -∗ φ v ={⊤}=∗ □ ψ v) -∗
    Gthunk p g γ t  n    φ  ={∅}=∗
    Gthunk p g γ t (n+m) ψ.
  Proof using.
    iIntros "H1 H2".
    iApply (Thunk_consequence with "[H1] H2").
    iIntros (v) "Htc HR Hv".
    iFrame "HR".
    iApply ("H1" with "Htc").
    iAssumption.
  Qed.

  Lemma Gthunk_pay E p g γ t n k φ :
    ↑thunkPayN t ⊆ E →
    TC k -∗ Gthunk p g γ t n φ ={E}=∗ Gthunk p g γ t (n-k) φ.
  Proof using. iIntros (?) "H1 H2". by iMod (Thunk_pay with "H1 H2"). Qed.

  Lemma create_spec p g n φ f :
    TC_invariant -∗
    {{{ TC 3 ∗ ( TC n -∗ own_gens_below_bound p (Some g) -∗
                 ∀ ψ, (∀ v, own_gens_below_bound p (Some g) -∗ □ φ v -∗ ψ «v»%V) -∗
                 WP «f #()» {{ ψ }} ) }}}
    « create f »
    {{{ γ t, RET #t ; Gthunk p g γ t n φ }}}.
  Proof using.
    iIntros "#HtickInv" (Φ) "!# H Post".
    by wp_apply (Thunks.create_spec with "HtickInv H").
  Qed.

  Lemma force_spec p g bound γ t φ :
    lies_below g bound →
    TC_invariant -∗
    {{{ TC 11 ∗ Gthunk p g γ t 0 φ ∗ own_gens_below_bound p bound }}}
    « force #t »
    {{{ v, RET «v» ; ThunkVal γ v ∗ □ φ v ∗ own_gens_below_bound p bound }}}.
  Proof using.
    intros Hg. iIntros "#HtickInv" (Φ) "!# (TC & H & Hgens) HΦ".
    rewrite /own_gens_below_bound.
    rewrite (carve_out_gens_below_gen _ _ Hg).
    iDestruct (na_own_union with "Hgens") as "[Hgens Hthunk]".
    { set_solver. }
    wp_apply (Thunks.force_spec _ p (gen_ns g) with "HtickInv [$TC $H $Hthunk $Hgens]").
    { eauto using gen_ns_subseteq_interval. }
    iIntros (?) "(? & ? & Hthunk & Hgens)". iApply "HΦ". iFrame.
    iDestruct (na_own_union with "[$Hgens $Hthunk]") as "?". set_solver. done.
  Qed.

End Gthunks.
