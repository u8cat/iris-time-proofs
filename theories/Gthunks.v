From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time Require Import TimeCredits Auth_max_nat Thunks.
From iris_time Require Import ThunksCode.

Definition genid := nat.

Definition gen_ns (id : genid) : namespace :=
  nroot .@ "gthunk" .@ id.

(* auxiliary definition *)
Fixpoint gens_upto' (id : genid) : coPset :=
  match id with
  | O => ∅
  | S id' => gens_upto' id' ∪ ↑(gen_ns id')
  end.

(* A set of generations.
   If the bound is [Some id], this corresponds to the set [0, id);
   If the bound is [None], then this corresponds to [0, +oo). *)
Definition gens_upto (bound : option genid) : coPset :=
  match bound with
  | None => ⊤
  | Some id => gens_upto' id
  end.

(* Compare an identifier with a bound. In other words, this checks whether the
   generation [id] is in the set [gens_upto bound]. *)
Definition is_upto (id : genid) (bound : option genid) : Prop :=
  match bound with
  | None => True
  | Some id' => id < id'
  end.

Lemma gen_ns_disj_upto' (n n' : genid) :
  n ≤ n' →
  ↑gen_ns n' ## gens_upto' n.
Proof.
  revert n'; induction n; cbn; intros n'.
  - set_solver.
  - intros Hn'. rewrite disjoint_union_r. split.
    + eapply IHn. lia.
    + unfold gen_ns. assert (n ≠ n') by lia. solve_ndisj.
Qed.

Lemma gens_upto'_mono (id id' : genid) :
  id ≤ id' →
  gens_upto' id ⊆ gens_upto' id'.
Proof.
  revert id; induction id'; intros id Hid; cbn.
  - assert (id = 0) by lia; by subst id.
  - destruct (decide (id = S id')).
    + subst id. cbn. done.
    + specialize (IHid' id ltac:(lia)). set_solver.
Qed.

Lemma gen_ns_sub_upto (id id' : genid) :
  id < id' →
  ↑gen_ns id ⊆ gens_upto' id'.
Proof.
  intros Hid.
  assert (HH: ↑gen_ns id ⊆ gens_upto' (S id)).
  { cbn. set_solver. }
  transitivity (gens_upto' (S id)); auto.
  by apply gens_upto'_mono.
Qed.

Section Gthunks.

  Notation valO := (valO heap_lang).
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γ *)
  Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
  Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
  Context `{na_invG Σ}.

  Implicit Type p : na_inv_pool_name.
  Implicit Type id : genid.
  Implicit Type γ : gname.
  Implicit Type t : loc.
  Implicit Type n m k : nat.
  Implicit Type f : val.

  Definition own_gens_upto p (bound : option genid) :=
    na_own p (gens_upto bound).

  Lemma own_gens_upto_alloc : ⊢ |==> ∃ p, own_gens_upto p None.
  Proof using. iApply na_alloc. Qed.

  (* TODO parameterize with R *)
  Definition Gthunk p id γ t n φ : iProp Σ :=
    Thunk p (gen_ns id) γ t n
            (own_gens_upto p (Some id)) φ.

  Instance Gthunk_persistent p id γ t n φ :
    Persistent (Gthunk p id γ t n φ).
  Proof using. exact _. Qed.

  Lemma Gthunk_weaken p id γ t n₁ n₂ φ :
    (n₁ ≤ n₂)%nat →
    Gthunk p id γ t n₁ φ -∗
    Gthunk p id γ t n₂ φ.
  Proof using. iIntros (?) "H". by iApply Thunk_weaken. Qed.

  Lemma Gthunk_consequence p id γ t n m φ ψ :
    (∀ v, TC m -∗ φ v ={⊤}=∗ □ ψ v) -∗
    Gthunk p id γ t  n    φ  ={∅}=∗
    Gthunk p id γ t (n+m) ψ.
  Proof using.
    iIntros "H1 H2".
    iApply (Thunk_consequence with "[H1] H2").
    iIntros (v) "Htc HR Hv".
    iFrame "HR".
    iApply ("H1" with "Htc").
    iAssumption.
  Qed.

  Lemma Gthunk_pay E p id γ t n k φ :
    ↑thunkPayN t ⊆ E →
    TC k -∗ Gthunk p id γ t n φ ={E}=∗ Gthunk p id γ t (n-k) φ.
  Proof using. iIntros (?) "H1 H2". by iMod (Thunk_pay with "H1 H2"). Qed.

  Lemma create_spec p id n φ f :
    TC_invariant -∗
    {{{ TC 3 ∗ ( TC n -∗ own_gens_upto p (Some id) -∗
                 ∀ ψ, (∀ v, own_gens_upto p (Some id) -∗ □ φ v -∗ ψ «v»%V) -∗
                 WP «f #()» {{ ψ }} ) }}}
    « create f »
    {{{ γ t, RET #t ; Gthunk p id γ t n φ }}}.
  Proof using.
    iIntros "#HtickInv" (Φ) "!# H Post".
    by wp_apply (Thunks.create_spec with "HtickInv H").
  Qed.

  Lemma force_spec p id bound γ t φ :
    is_upto id bound →
    TC_invariant -∗
    {{{ TC 11 ∗ Gthunk p id γ t 0 φ ∗ own_gens_upto p bound }}}
    « force #t »
    {{{ v, RET «v» ; ThunkVal γ v ∗ □ φ v ∗ own_gens_upto p bound }}}.
  Proof using.
    intros Hid. iIntros "#HtickInv" (Φ) "!# (TC & H & Hgens) HΦ".
    rewrite /own_gens_upto.
    assert (gens_upto bound = gens_upto' id ∪ (gens_upto bound ∖ gens_upto' id)) as Hsplit_gens.
    { apply union_difference_L. destruct bound.
      + apply gens_upto'_mono. cbn in Hid. lia.
      + cbn. set_solver. }
    rewrite Hsplit_gens. iDestruct (na_own_union with "Hgens") as "[Hgens Hthunk]".
    { set_solver. }
    assert (↑gen_ns id ⊆ gens_upto bound ∖ gens_upto' id) as Hthunk.
    { apply subseteq_difference_r. by apply gen_ns_disj_upto'. destruct bound.
      + by apply gen_ns_sub_upto.
      + cbn. set_solver. }
    wp_apply (Thunks.force_spec _ p (gen_ns id) with "HtickInv [$TC $H $Hthunk $Hgens]").
      by auto.
    iIntros (?) "(? & ? & Hthunk & Hgens)". iApply "HΦ". iFrame.
    iDestruct (na_own_union with "[$Hgens $Hthunk]") as "?". set_solver. done.
  Qed.

End Gthunks.
