From stdpp Require Import list.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import Base TimeCredits Untranslate.
From iris_time.thunks Require Import LazyCode Generations ThunksBase HThunks.
From iris_time.iqueue Require Import Code.

Section IQueue.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Context (p : na_inv_pool_name).

Lemma lazy_spec g n φ e :
  TC_invariant -∗
  {{{ TC 4 ∗ isAction (λ: <>, e) n (HToken p (Some g)) φ }}}
    « lazy e »
  {{{ t, RET «#t» ; HThunk p g t n φ }}}.
Proof.
  iIntros "#Hc !#" (Φ) "[Htc Haction] Post".
  rewrite translate_lazy_expr.
  wp_tick_closure.
  untranslate.
  wp_apply (hthunk_create p g with "[$] [$Htc Haction]"); eauto.
  rewrite -lock //.
Qed.

(******)

Inductive is_tree : nat → val → list val → Prop :=
| is_tree_leaf v :
  is_tree 0 v [v]
| is_tree_node n v1 v2 vs1 vs2 :
  is_tree n v1 vs1 →
  is_tree n v2 vs2 →
  is_tree (S n) (v1, v2)%V (vs1 ++ vs2).

Hint Constructors is_tree : core.

Lemma is_tree_not_empty level v :
  ¬ is_tree level v [].
Proof.
  revert v; induction level; cbn; intros v; inversion 1; subst.
  match goal with H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [-> ->] end.
  naive_solver.
Qed.

Lemma is_tree_length n v vs :
  is_tree n v vs →
  length vs = 2 ^ n.
Proof.
  revert v vs; induction n; intros v vs; inversion 1; subst.
  { reflexivity. }
  { rewrite app_length. rewrite (IHn v1 vs1) // (IHn v2 vs2) //.
    rewrite Nat.pow_succ_r'. lia. }
Qed.

Lemma is_tree_no_tail level v vs vs' :
  length vs = 2 ^ level →
  is_tree level v (vs ++ vs') →
  vs' = [].
Proof.
  intros Hlen Ht.
  pose proof (is_tree_length level v (vs ++ vs') ltac:(eassumption)) as HH.
  rewrite app_length in HH. apply nil_length_inv. lia.
Qed.

Local Ltac is_tree_inv :=
  match goal with
  | H : is_tree 0 _ _ |- _ => inversion H; subst; clear H
  | H : is_tree (S _) _ _ |- _ => inversion H; subst; clear H
  | H : is_tree _ _ [] |- _ => apply is_tree_not_empty in H; done
  | H : is_tree ?l _ (?vs ++ _), H' : length ?vs = 2 ^ ?l |- _ =>
      pose proof (is_tree_no_tail _ _ _ _ H' H); subst; simplify_list_eq
  end.

Inductive is_digit01 : nat → val → list val → Prop :=
| is_digit01_ZERO level :
  is_digit01 level ZEROV []
| is_digit01_ONEa level v vs :
  is_tree level v vs →
  is_digit01 level (ONEaV v) vs.

Hint Constructors is_digit01 : core.

Local Ltac is_digit01_inv :=
  match goal with
  | H : is_digit01 _ ZEROV _ |- _ => inversion H; subst; clear H
  | H : is_digit01 _ (ONEaV _) _ |- _ => inversion H; subst; clear H
  end.

Inductive is_digit12 : nat → val → list val → Prop :=
| is_digit12_ONEb level v vs :
  is_tree level v vs →
  is_digit12 level (ONEbV v) vs
| is_digit12_TWO level v1 v2 vs1 vs2 :
  is_tree level v1 vs1 →
  is_tree level v2 vs2 →
  is_digit12 level (TWOV v1 v2) (vs1 ++ vs2).

Hint Constructors is_digit12 : core.

Local Ltac is_digit12_inv :=
  match goal with
  | H : is_digit12 _ (ONEbV _) _ |- _ => inversion H; subst; clear H
  | H : is_digit12 _ (TWOV _ _) _ |- _ => inversion H; subst; clear H
  end.

Inductive digit01_len : val → nat → Prop :=
| digit01_len_ZERO : digit01_len ZEROV 0
| digit01_len_ONEa v : digit01_len (ONEaV v) 1.

Hint Constructors digit01_len : core.

Local Ltac digit01_len :=
  match goal with
  | H : digit01_len ZEROV _ |- _ => inversion H; subst; clear H
  | H : digit01_len (ONEaV _) _ |- _ => inversion H; subst; clear H
  end.

Inductive digit12_len : val → nat → Prop :=
| digit12_len_ONEb v : digit12_len (ONEbV v) 1
| digit12_len_TWO v1 v2 : digit12_len (TWOV v1 v2) 2.

Hint Constructors digit12_len : core.

Local Ltac digit12_len :=
  match goal with
  | H : digit12_len (ONEbV _) _ |- _ => inversion H; subst; clear H
  | H : digit12_len (TWOV _ _) _ |- _ => inversion H; subst; clear H
  end.

Local Ltac list_inv :=
  match goal with
  | H : _ ++ _ = [] |- _ => apply app_eq_nil in H as [? ?]; subst
  | H : [] = _ ++ _ |- _ => symmetry in H; apply app_eq_nil in H as [? ?]; subst
  end.

Local Ltac inv :=
  repeat first [
    is_tree_inv | is_digit01_inv | is_digit12_inv
    | digit01_len | digit12_len | list_inv ].

Definition K := 150.

Fixpoint is_queue (h : height) (level : nat) (q : val) (vs : list val) : iProp Σ :=
  match h with
  | 0 =>
      ∃ d, ⌜q = SHALLOWV d⌝ ∗ ⌜is_digit01 level d vs⌝
  | S h' =>
      (∃ d, ⌜q = SHALLOWV d⌝ ∗ ⌜is_digit01 level d vs⌝) ∨
      (∃ f (m:loc) r fvs mvs rvs lenf lenr,
         HThunk p h m (K * (lenf - lenr))
           (λ q', is_queue h' (S level) q' mvs) ∗
         ⌜q = DEEPV f (#m) r⌝ ∗
         ⌜is_digit12 level f fvs⌝ ∗
         ⌜is_digit01 level r rvs⌝ ∗
         ⌜digit12_len f lenf⌝ ∗
         ⌜digit01_len r lenr⌝ ∗
         ⌜vs = fvs ++ mvs ++ rvs⌝)
  end.

Lemma is_queue_eq g level q vs :
  is_queue g level q vs ⊣⊢
  (∃ d, ⌜q = SHALLOWV d⌝ ∗ ⌜is_digit01 level d vs⌝) ∨
  (∃ g', ⌜g = S g'⌝ ∗
     ∃ f (m:loc) r fvs mvs rvs lenf lenr,
       HThunk p g m (K * (lenf - lenr))
         (λ q', is_queue g' (S level) q' mvs) ∗
       ⌜q = DEEPV f (#m) r⌝ ∗
       ⌜is_digit12 level f fvs⌝ ∗
       ⌜is_digit01 level r rvs⌝ ∗
       ⌜digit12_len f lenf⌝ ∗
       ⌜digit01_len r lenr⌝ ∗
       ⌜vs = fvs ++ mvs ++ rvs⌝).
Proof.
  iSplit.
  { destruct g; first by eauto.
    iIntros "[?|?]"; rewrite -/is_queue; first by eauto.
    iRight. iExists g; iSplit; eauto. }
  { iIntros "[Hbase|Hsucc]".
    { destruct g; eauto. iLeft; eauto. }
    iDestruct "Hsucc" as "(%&%Hg&?)". subst g.
    iRight; eauto. }
Qed.

Definition iqueue (q : val) (vs : list val) : iProp Σ :=
  ∃ g, is_queue g 0 q vs.

Instance is_queue_persistent g lvl q vs :
  Persistent (is_queue g lvl q vs).
Proof. revert lvl q vs; induction g; intros; apply _. Qed.

Instance iqueue_persistent q vs : Persistent (iqueue q vs).
Proof. apply _. Qed.

Local Ltac deconstruct_iqueue :=
  iDestruct "Hqueue" as "(%g & Hqueue)".

Local Ltac deconstruct_is_queue :=
  iDestruct (is_queue_eq with "Hqueue") as "[HqueueS|HqueueD]";
  [ iDestruct "HqueueS" as "(%d & -> & %Hd)"
  | iDestruct "HqueueD"
    as "(% & % & (%f & %m & %r & %fvs & %mvs & %rvs & %lenf & %lenr
                       & #Hthunk & -> & %Hf & %Hr & %Hlenf & %Hlenr & %))";
    try (exfalso; lia); rewrite -/is_queue; subst ].

Local Ltac construct_is_queue_shallow :=
  iApply is_queue_eq; iLeft; iPureIntro.

Local Ltac construct_is_queue_deep :=
  iApply is_queue_eq; iRight; iExists _; iSplit; first done;
  iExists _,_,_,_,_,_,_,_; iSplit; [ | iPureIntro ].

Lemma is_queue_covariant_in_g g g' level q vs :
  g ≤ g' →
  is_queue g level q vs ={⊤}=∗
  is_queue g' level q vs.
Proof.
  iIntros (Hg) "Hqueue".
  iInduction g as [|g] "IH" forall (g' Hg q vs level).
  { iApply is_queue_eq; iLeft; eauto. }
  destruct g' as [| g' ]; first lia.
  deconstruct_is_queue.
  { iApply is_queue_eq; iLeft; eauto. }
  symmetry in H4. simplify_eq. rename g into g''.
  iDestruct (hthunk_covariant_in_h _ _ (S g') with "Hthunk") as "#Hthunk'";
    first lia.
  iMod (hthunk_consequence _ _ _ _ 0 _ (λ q', is_queue g' (S level) q' mvs)
    with "[] Hthunk'") as "Hthunk''".
  { iIntros (v) "_ #Hqueue".
    by iMod ("IH" $! g' with "[] Hqueue") as "#?";
    first (iPureIntro; lia). }
  iModIntro. rewrite Nat.add_0_r.
  construct_is_queue_deep; first iApply "Hthunk''"; split_and!; eauto.
Qed.

Lemma empty_spec : ⊢ iqueue empty [].
Proof. iExists 0, ZEROV; eauto. Qed.

Lemma is_empty_is_queue_spec g q level vs :
  TC_invariant -∗
  is_queue g level q vs -∗
  {{{ TC 20 }}}
    «is_empty q»
  {{{ (b:bool), RET #b ;
      ⌜if b then vs = [] else
        ∃ xs ys, vs = xs ++ ys ∧ length xs = 2 ^ level⌝ }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_is_queue.
  { inversion Hd; subst; inv;
      wp_tick_lam; repeat wp_tick_match.
    - by iApply "Post".
    - iApply ("Post" $! false); iPureIntro. exists vs, [].
      rewrite app_nil_r. split; eauto using is_tree_length. }
  { inversion Hf; subst; clear Hf; inv;
      wp_tick_lam; repeat wp_tick_match; wp_tick_proj;
      repeat (wp_tick_let; repeat wp_tick_proj);
      iApply ("Post" $! false); iPureIntro.
    - exists fvs, (mvs ++ rvs). split; eauto using is_tree_length.
    - exists vs1, (vs2 ++ mvs ++ rvs). rewrite -app_assoc.
      split; eauto using is_tree_length. }
Qed.

Lemma is_empty_spec q vs :
  TC_invariant -∗
  iqueue q vs -∗
  {{{ TC 20 }}}
    «is_empty q»
  {{{ RET #(bool_decide (vs = [])); True }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_iqueue.
  iApply (is_empty_is_queue_spec with "[$] [$] [$]").
  iIntros "!>" ([|]) "%HH"; subst.
  - by iApply "Post".
  - destruct HH as (?&?&->&HH). cbn in HH.
    rewrite bool_decide_eq_false_2; first by iApply "Post".
    by intros [-> ->]%app_eq_nil.
Qed.

Definition B := 200.

Lemma snoc_is_queue_spec g level q y ys vs :
  is_tree level y ys →
  TC_invariant -∗
  is_queue g level q vs -∗
  {{{ TC (B + 50) }}}
    «snoc q y»
  {{{ q', RET «q'»;
      is_queue (S g) level q' (vs ++ ys) }}}.
Proof.
  intros Hy. iIntros "#Hc #Hqueue".
  pose SNOC x y := snoc x y. rewrite -/(SNOC _ _).
  iLöb as "IH" forall (g level q y ys vs Hy) "Hqueue".
  iIntros "!#" (Φ) "Htc Post". rewrite {2}/SNOC.
  iDestruct (TC_plus with "Htc") as "[HtcB Htc]".
  deconstruct_is_queue.
  (* SHALLOW case *)
  { inversion Hd; subst; inv.
    { (* case 1 : SHALLOW ZERO -> SHALLOW (ONEa y) *)
      wp_tick_lam. wp_tick_let. repeat wp_tick_match. repeat wp_tick_inj.
      iApply ("Post" $! (SHALLOWV (ONEaV y))).
      construct_is_queue_shallow; eauto. }
    { (* case 2 : SHALLOW (ONEa x) -> DEEP (TWO (x, y), lazy empty, ZERO) *)
      wp_tick_lam. wp_tick_let. repeat wp_tick_match. repeat wp_tick_inj.
      untranslate.
      push_subst.
      divide_credit "Htc" 32 8.
      wp_apply (lazy_spec (S g) (2*K) (λ q', is_queue g (S level) q' [])
                 with "[$] [Htc']").
      { divide_credit "Htc'" 4 4. iFrame "Htc''".
        iIntros "? ?" (?) "H". iRevert "Htc'"; iIntros "Htc'".
        wp_tick_lam. repeat wp_tick_inj.
        iApply ("H" $! (SHALLOWV ZEROV) with "[$]"). iModIntro.
        iApply is_queue_eq; iLeft; eauto. }
      iIntros (t) "Hthunk".
      repeat (wp_tick_pair; repeat wp_tick_inj).
      iApply ("Post" $! (DEEPV (TWOV v y) (#t) ZEROV)).
      construct_is_queue_deep. 2: split_and!; eauto. iApply "Hthunk".
      rewrite !app_nil_r//. } }
  (* DEEP case *)
  { inversion Hr; subst; inv.
    { (* case 3 : DEEP (f, m, ZERO) -> DEEP (f, m, ONEa y) *)
      wp_tick_lam. wp_tick_let. repeat wp_tick_match. wp_tick_proj.
      repeat (wp_tick_let; repeat wp_tick_proj). wp_tick_match.
      wp_tick_inj. repeat wp_tick_pair.
      rewrite Nat.sub_0_r.
      assert (lenf >= 1) by (inversion Hlenf; lia).
      iMod (hthunk_pay with "Hthunk HtcB") as "Hthunk'"; first solve_ndisj.
      iDestruct (hthunk_increase_debt _ _ _ _ (K * (lenf - 1)) with "Hthunk'")
        as "Hthunk'".
      { unfold K, B; lia. }
      iMod (hthunk_consequence _ _ _ _ 0 _ (λ q', is_queue (S g') (S level) q' mvs)
              with "[] Hthunk'") as "Hthunk'".
      { iIntros (v) "_ #Hq".
        iMod (is_queue_covariant_in_g _ (S g') with "Hq") as "#?";
          [lia | eauto]. }
      iDestruct (hthunk_covariant_in_h _ _ (S (S g')) with "Hthunk'") as "Hthunk'";
        first lia.
      wp_tick_inj. rewrite Nat.add_0_r.
      iApply ("Post" $! (DEEPV f (#m) (ONEaV y))).
      construct_is_queue_deep; first iApply "Hthunk'"; split_and!; eauto.
      rewrite app_nil_r app_assoc //. }
    { (* case 4 : DEEP (f, m, ONEa x) ->
                  DEEP (f, lazy (snoc (force m) (x, y)), ZERO) *)
      wp_tick_lam. wp_tick_let. repeat wp_tick_match. wp_tick_proj.
      repeat (wp_tick_let; repeat wp_tick_proj).
      wp_tick_match. wp_tick_inj.
      rewrite untranslate_litv. untranslate. push_subst.
      divide_credit "Htc" 20 8.
      wp_apply (lazy_spec (S (S g')) (K * lenf)
                          (λ q', is_queue (S g') (S level) q' (mvs ++ rvs ++ ys))
                  with "[$] [HtcB Htc']").
      { divide_credit "Htc'" 4 4. iFrame "Htc''".
        iIntros "Htok Htc" (ψ) "Hψ". iRevert "Htc'"; iIntros "Htc'".
        wp_tick_lam. wp_tick_pair.
        rewrite untranslate_litv !untranslate_val untranslate_app.
        assert (1 <= lenf). { inversion Hlenf; eauto. }
        rewrite (_: K * lenf = K + K * (lenf - 1)); last (unfold K; lia).
        iDestruct (TC_plus with "Htc") as "[HtcK Htc]".
        iMod (hthunk_pay with "Hthunk Htc") as "Hthunk'"; first solve_ndisj.
        rewrite Nat.sub_diag.
        rewrite {2}/K; divide_credit "HtcK" 139 11.
        wp_apply (hthunk_force with "[$] [$Htok $HtcK' $Hthunk']").
        { unfold lies_below; lia. }
        iIntros (q') "(#Hq' & ? & Htok)". untranslate.
        divide_credit "HtcK" 89 50.
        untranslate. rewrite /SNOC.
        wp_apply ("IH" $! _ _ q' with "[%] Hq' [HtcB HtcK']");
          first by eauto.
        { iApply TC_plus. iFrame. }
        iClear "IH Hq'". iIntros (q'') "#Hq''".
        by iApply ("Hψ" with "Htok"). }
      iIntros (t) "#Hthunk'". repeat wp_tick_pair. wp_tick_inj.
      iApply ("Post" $! (DEEPV f #t ZEROV)).
      construct_is_queue_deep; last split_and!; [| eauto..].
      { rewrite Nat.sub_0_r. eauto. }
      rewrite app_nil_r -!app_assoc //. } }
Qed.

Lemma snoc_spec q vs y :
  TC_invariant -∗
  iqueue q vs -∗
  {{{ TC (B + 50) }}}
    «snoc q y»
  {{{ q', RET «q'»; iqueue q' (vs ++ [y]) }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_iqueue.
  iApply (snoc_is_queue_spec with "[$] Hqueue Htc"); eauto.
  iIntros "!>" (q') "Hqueue'". iApply ("Post" $! q').
  iExists _; eauto.
Qed.

Lemma head_is_queue_spec g level q ys vs :
  length ys = 2 ^ level →
  TC_invariant -∗
  is_queue g level q (ys ++ vs) -∗
  {{{ TC 25 }}}
    «head q»
  {{{ y, RET «y»; ⌜is_tree level y ys⌝ }}}.
Proof.
  intros Hys. iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_is_queue.
  (* SHALLOW *)
  { inversion Hd; subst; inv.
    { cbn in Hys; pose proof (pow2_pos level); lia. }
    { wp_tick_lam. repeat wp_tick_match. by iApply "Post". } }
  (* DEEP *)
  inversion Hf; subst; clear Hf; inv.
  { (* DEEP ONEb *)
    assert (ys = fvs ∧ vs = mvs ++ rvs) as [-> ->].
    { apply app_inj_1; eauto. rewrite (is_tree_length level v fvs) //. }
    wp_tick_lam. wp_tick_match. wp_tick_proj.
    repeat (wp_tick_let; repeat wp_tick_proj).
    wp_tick_match. by iApply "Post". }
  { (* DEEP TWO *)
    assert (ys = vs1 ∧ vs = vs2 ++ mvs ++ rvs) as [-> ->].
    { apply app_inj_1; last by rewrite app_assoc.
      rewrite (is_tree_length level v1 vs1) //. }
    wp_tick_lam. wp_tick_match. wp_tick_proj.
    repeat (wp_tick_let; repeat wp_tick_proj).
    wp_tick_match. wp_tick_proj. wp_tick_let.
    wp_tick_proj. wp_tick_let. by iApply "Post". }
Qed.

Lemma head_spec q v vs :
  TC_invariant -∗
  iqueue q (v :: vs) -∗
  {{{ TC 25 }}}
    «head q»
  {{{ RET «v»; True }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_iqueue. rewrite (_: v :: vs = [v] ++ vs) //.
  wp_apply (head_is_queue_spec with "[$] Hqueue [$]"); first done.
  iIntros (? ?). inv. by iApply "Post".
Qed.

Lemma tail_is_queue_spec g level q vs :
  2 ^ level ≤ length vs →
  TC_invariant -∗
  is_queue g level q vs -∗
  {{{ TC (B + 100) ∗ HToken p (Some (S g)) }}}
    «tail q»
  {{{ q', RET «q'» ;
      is_queue g level q' (drop (2 ^ level) vs) ∗
      HToken p (Some (S g)) }}}.
Proof.
  intros Hlevel. iIntros "#Hc #Hqueue".
  pose TAIL x := tail x. rewrite -/(TAIL _).
  iLöb as "IH" forall (g level q vs Hlevel) "Hqueue".
  iIntros "!#" (Φ) "[Htc Htok] Post". rewrite {2}/TAIL.
  iDestruct (TC_plus with "Htc") as "[HtcB Htc]".
  deconstruct_is_queue.
  (* SHALLOW case *)
  { inversion Hd; subst; inv.
    { (* SHALLOW ZERO case: impossible *)
      cbn in Hlevel; pose proof (pow2_pos level); lia. }
    { (* SHALLOW (ONEa _) case *)
      wp_tick_lam. repeat wp_tick_match. repeat wp_tick_inj.
      iApply ("Post" $! (SHALLOWV ZEROV)). iFrame "Htok".
      rewrite drop_ge; last by rewrite (is_tree_length level v) //.
      construct_is_queue_shallow; eauto. } }
  (* DEEP case *)
  { inversion Hf; subst; clear Hf; inv.
    (* DEEP (ONEbV _, m, r) case *)
    { wp_tick_lam. wp_tick_match. wp_tick_proj.
      repeat (wp_tick_let; repeat wp_tick_proj).
      wp_tick_match. rewrite untranslate_litv. untranslate.
      assert (lenr <= 1) by (inversion Hlenr; subst; lia).
      rewrite (_: B = K * (1 - lenr) + (B - K * (1 - lenr)));
        last (unfold B,K; lia).
      iDestruct (TC_plus with "HtcB") as "[HtcK HtcBK]".
      iMod (hthunk_pay with "Hthunk HtcK") as "Hthunk'"; first solve_ndisj.
      rewrite Nat.sub_diag.
      divide_credit "Htc" 70 11.
      wp_apply (hthunk_force with "[$] [$Htc' $Htok $Hthunk']");
        first (unfold lies_below; cbn; lia).
      iIntros (q') "(#Hqueue' & ? & Htok)".
      wp_tick_let. untranslate.
      divide_credit "Htc" 48 20.
      wp_apply (is_empty_is_queue_spec with "[$] Hqueue' [$]").
      iIntros ([|] Hempty).
      { (* is_empty q *)
        subst mvs. wp_tick_if. wp_tick_inj.
        iApply ("Post" $! (SHALLOWV r)). iFrame "Htok".
        construct_is_queue_shallow; cbn. eexists _; split; eauto.
        rewrite drop_app_alt // (is_tree_length level v) //. }
      { (* ¬ is_empty q *)
        destruct Hempty as (mvs1 & mvs2 & -> & Hlen).
        wp_tick_if. untranslate.
        divide_credit "Htc" 22 25.
        wp_apply (head_is_queue_spec with "[$] Hqueue' [$]"); first done.
        iIntros (t1 Ht1). inv. wp_tick_let. do 2 (wp_tick_proj; wp_tick_let).
        rewrite untranslate_litv. untranslate. push_subst.
        rewrite -untranslate_val. (* argh *)
        divide_credit "Htc" 8 6.
        divide_credit "Htc'" 2 4.
        wp_apply (lazy_spec (S g') (K * (2 - lenr))
                            (λ q', is_queue g' (S level) q' mvs2)
                   with "[$] [$Htc'' HtcBK Htc']").
        { iIntros "Htok Htc" (ψ) "Hψ". wp_tick_lam. untranslate.
          iDestruct (TC_plus with "[$Htc $HtcBK]") as "Htc".
          assert (B >= K) by (unfold K,B; lia).
          rewrite (_: K * (2 - lenr) + (B - K * (1 - lenr)) = K + B); last nia.
          iDestruct (TC_plus with "Htc") as "[HtcK HtcB]".
          rewrite /TAIL.
          iApply ("IH" with "[] Hqueue' [$Htok HtcK HtcB]").
          { iPureIntro. rewrite app_length Hlen. lia. }
          { rewrite (_: K * (1 - lenr) + (B - K * (1 - lenr)) = B); last nia.
            iApply TC_plus. iFrame "HtcB".
            unfold K; by divide_credit "HtcK" 100 50. }
          iIntros "!>" (q'') "[#Hqueue'' Htok]".
          rewrite drop_app_alt //. iApply ("Hψ" with "Htok Hqueue''"). }
        iIntros (t) "Hthunk'". wp_tick_pair. wp_tick_inj. repeat wp_tick_pair.
        wp_tick_inj. iApply ("Post" $! (DEEPV (TWOV v1 v2) #t r)).
        iFrame "Htok".
        rewrite drop_app_alt; last by (symmetry; eauto using is_tree_length).
        construct_is_queue_deep; first iFrame "Hthunk'"; split_and!; eauto.
        rewrite !app_assoc //. } }
    (* DEEP (TWO (_, y), m, r) case *)
    { wp_tick_lam. wp_tick_match. wp_tick_proj.
      repeat (wp_tick_let; repeat wp_tick_proj).
      wp_tick_match. wp_tick_proj. wp_tick_let. wp_tick_proj.
      wp_tick_let. wp_tick_inj. repeat wp_tick_pair.
      iMod (hthunk_pay K with "Hthunk [HtcB]") as "Hthunk'"; first solve_ndisj.
      { unfold B, K. by divide_credit "HtcB" 50 150. }
      rewrite (_: K * (2 - lenr) - K = K * (1 - lenr)); last nia.
      wp_tick_inj.
      iApply ("Post" $! (DEEPV (ONEbV v2) #m r)). iFrame "Htok".
      construct_is_queue_deep; first iFrame "Hthunk'"; split_and!; eauto.
      rewrite -app_assoc drop_app_alt// (is_tree_length level v1) //. } }
Qed.

Notation token := (HToken p None).

Lemma tail_spec q v vs :
  TC_invariant -∗
  iqueue q (v :: vs) -∗
  {{{ TC (B + 100) ∗ token }}}
    «tail q»
  {{{ q', RET «q'»; iqueue q' vs ∗ token }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "[Htc Htok] Post".
  deconstruct_iqueue.
  rewrite /HToken (carve_out_gens_below_gen (S g) None) //.
  iDestruct (na_own_union with "Htok") as "[Htok Htok_rest]".
  by apply disjoint_difference_r1.
  iApply (tail_is_queue_spec with "[$] [$] [$Htc $Htok]").
  { cbn. lia. }
  iIntros "!>" (q') "[#Hqueue_tail Htok]". iApply ("Post" $! q').
  iSplitR. { iExists _. iFrame "Hqueue_tail". }
  rewrite na_own_union; first by iFrame. by apply disjoint_difference_r1.
Qed.

End IQueue.
