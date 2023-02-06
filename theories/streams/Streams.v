From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time.thunks Require Import ThunksCode LazyCode ThunksBase.
From iris_time.thunks Require Import Generations HThunks.
From iris_time.streams Require Import StreamsCode.
Open Scope nat_scope.

(* This file contains specifications and proofs for operations on streams. *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section Proofs.

  Notation valO := (valO heap_lang).
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γt *)
  Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
  Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
  Context `{na_invG Σ}.
  Notation iProp := (iProp Σ).
  Open Scope nat_scope.

  (* A debit is a natural integer. The predicate [Stream] is indexed
     with a list of debits. *)
  Definition debit := nat.
  Definition debits := list debit.

  (* We write [t] for a thunk and [c] for a stream cell. *)
  Implicit Type t : loc.
  Implicit Type c : val.
  Implicit Type x y z : val.
  Implicit Type xs ys zs : list val.
  Implicit Type d : debit.
  Implicit Type ds : debits.
  Implicit Type h : height.
  Implicit Type E F : coPset.

  (* Everything in this section is indexed with a non-atomic pool [p]. *)
  Variable p : na_inv_pool_name.

(* -------------------------------------------------------------------------- *)

  (* Because thunks are indexed with heights, streams must be height-indexed
     as well. (Attempting to work with thunks of undetermined height cannot
     work: forcing a thunk of undetermined height requires the strong token
     [HToken p None], and this token is never made available to a suspended
     computation. So, if a thunk [t] has undetermined height, then one cannot
     construct a thunk [t'] that forces [t].) *)

  (* In a stream of height [h], every thunk has height [h]. (This really means
     height at most [h], since [HThunk] is covariant in [h].) Thus, the token
     [token h] allows forcing the whole stream. *)

  (* For now, we work with finite streams only. *)

  (* [Stream h t ds xs] means that [t] is a stream of height [h] whose
     debits and elements are given by the lists [ds] and [xs]. Because a
     stream of [n] elements involves [n+1] suspensions, if the length of
     the list [xs] is [n] then the length of the list [ds] must be [n+1]. *)

  (* That said, the equality [length ds = length xs + 1] remains implicit,
     and is actually not implied by [Stream h t ds xs], because it can
     be exposed only by forcing the whole stream. *)

  (* The following definition can be ignored; it is reformulated below in
     a more readable way. *)

  Fixpoint Stream h t ds xs : iProp :=
    match ds with
    | []    =>
        False
    | d :: ds =>
        HThunk p h t d (λ c,
          match xs with
          | []      =>       ⌜c = NILV⌝ ∗ ⌜ ds = [] ⌝
          | x :: xs => ∃ t', ⌜c = CONSV x #t'⌝ ∗ Stream h t' ds xs
          end)
    end%I.

  (* The assertion [StreamCell h c ds xs] describes a stream cell [c] that has
     been obtained by forcing a stream. If the stream has no elements then [c]
     must be the value [NILV] and [ds] must be empty. If the stream elements
     are [x :: xs] then [c] must be the value [CONSV (x, t)], where [t] is a
     stream of the remaining elements [xs]. *)

  (* In this assertion, we expect [length ds = length xs]. Indeed, the front
     thunk has been forced already, so its cost is not described by [ds]. *)

  Definition StreamCell h c ds xs : iProp :=
    match xs with
    | []      =>      ⌜c = NILV⌝ ∗ ⌜ ds = [] ⌝
    | x :: xs => ∃ t, ⌜c = CONSV x #t⌝ ∗ Stream h t ds xs
    end.

  (* The assertion [Stream h t ds xs] implies that [ds] is nonempty. *)

  (* The assertion [Stream h t (d :: ds) xs] states that [t] is a thunk of
     height [h] and debit [d]. Forcing this thunk producing a cell [c] such
     that [StreamCell h c ds xs] holds. *)

  Lemma unfold_stream h t ds xs :
    Stream h t ds xs =
      match ds with
      | []      => False%I
      | d :: ds => HThunk p h t d (λ c, StreamCell h c ds xs)
      end.
  Proof.
    destruct ds; reflexivity.
  Qed.

(* -------------------------------------------------------------------------- *)

(* Local tactics. *)

  (* Unfold the definition of [Stream]. *)
  Ltac unfold_stream :=
    rewrite unfold_stream.

  (* Deconstruct a hypothesis "Hstream": [Stream h t (d :: ds) xs],
     introducing hypothesis "Hthunk": [HThunk ...]. *)
  Local Ltac deconstruct_stream :=
    iDestruct "Hstream" as "#Hthunk".

  (* Prove [Stream ...] by using the hypothesis H: [HThunk ...]. *)
  Local Ltac construct_stream H :=
    unfold_stream; iFrame H.

  (* Deconstruct a hypothesis "Hc" when the cell is known to be nil. *)
  Local Ltac deconstruct_nil_cell :=
    iDestruct "Hc" as "(-> & %)".

  (* Deconstruct a hypothesis "Hc" when the cell is known to be cons. *)
  Local Ltac deconstruct_cons_cell t Hstream :=
    let ipat := eval cbv in ( "(-> & #" ++ Hstream ++ ")")%string in
    iDestruct "Hc" as (t) ipat.

  Local Lemma transport_list_eq_nil ds1 ds2 :
    length ds1 = length ds2 → ds1 = [] → ds2 = [].
  Proof.
    destruct ds1; destruct ds2; simpl; congruence.
  Qed.

  (* Prove [StreamCell ...] when the cell is nil. *)
  Local Ltac construct_nil_cell :=
    iPureIntro; eauto using transport_list_eq_nil.

  Local Ltac pure_conjunct :=
    iSplitR; [ solve [ eauto ] |].

  (* Prove [StreamCell ...] when the cell is cons. *)
  Local Ltac construct_cons_cell :=
    iExists _; pure_conjunct; eauto.

  (* Introduce a Texan triple. *)
  Local Ltac construct_texan_triple ipat :=
    iIntros "#?"; (* introduce TC_invariant *)
    iIntros (Φ) "!>";
    iIntros ipat;
    iIntros "Post".

(* -------------------------------------------------------------------------- *)

(* Basic properties. *)

  (* [Stream] is persistent. *)

  Global Instance stream_persistent :
    ∀ ds xs h t,
    Persistent (Stream h t ds xs).
  Proof.
    induction ds; destruct xs; exact _.
  Qed.

  (* [StreamCell] is persistent. *)

  Global Instance streamcell_persistent h c ds xs :
    Persistent (StreamCell h c ds xs).
  Proof.
    destruct xs; exact _.
  Qed.

  (* The list [ds] cannot be empty. *)

  Lemma unfold_stream_contradictory h t xs :
    Stream h t [] xs = False%I.
  Proof.
    reflexivity.
  Qed.

  (* So, [length ds] must be positive. *)

  Lemma stream_nonzero_length :
    ∀ ds xs h t,
    Stream h t ds xs -∗
    ⌜length ds > 0⌝.
  Proof.
    destruct ds; intros; simpl.
    { eauto. }
    { iIntros "_". iPureIntro. lia. }
  Qed.

  (* In [StreamCell h c ds xs], if [ds] is empty then this must be a nil
     cell. *)

  Lemma streamcell_nil_cell :
    ∀ xs h c,
    StreamCell h c [] xs -∗
    ⌜xs = []⌝.
  Proof.
    destruct xs; intros; iIntros "Hc".
    { eauto. }
    { deconstruct_cons_cell t' "Hstream".
      iPoseProof (stream_nonzero_length with "Hstream") as "%".
      simpl in *. lia. }
  Qed.

  Local Ltac streamcell_nil_cell :=
    iPoseProof (streamcell_nil_cell with "Hc") as "%";
    match goal with h: ?xs = [] |- _ => subst xs end;
    deconstruct_nil_cell.

  (* In [StreamCell h c ds xs], if [ds] is nonempty then this must be a cons
     cell. *)

  Lemma streamcell_cons_cell :
    ∀ ds xs h c,
    length ds > 0 →
    StreamCell h c ds xs -∗
    ⌜xs ≠ []⌝.
  Proof.
    destruct xs; intros; iIntros "Hc".
    { deconstruct_nil_cell. subst ds. simpl in *. lia. }
    { iPureIntro. congruence. }
  Qed.

  (* Like [Thunk], [Stream] is covariant in the height [h]. *)

  Lemma stream_covariant :
    ∀ ds h1 h2 t xs E,
    h1 ≤ h2 →
    Stream h1 t ds xs ={E}=∗
    Stream h2 t ds xs.
  Proof.
    induction ds as [| d ds ]; intros; iIntros "Hstream".
    { rewrite unfold_stream_contradictory.
      iDestruct "Hstream" as "%". tauto. }
    unfold_stream. deconstruct_stream.
    (* Apply the consequence rule to adjust the postcondition of this thunk. *)
    iMod (hthunk_consequence _ _ _ _ 0 with "[] Hthunk") as "Hthunk'";
      last first.
    { rewrite Nat.add_0_r. iModIntro.
      iPoseProof (hthunk_covariant_in_h with "Hthunk'") as "#Hthunk''".
      { eassumption. }
      construct_stream "Hthunk''". }
    iClear "Hthunk".
    (* Then, reason by cases on [xs], and use the induction hypothesis. *)
    iIntros (c) "_ #Hc".
    destruct xs as [| x xs ].
    { deconstruct_nil_cell. construct_nil_cell. }
    { deconstruct_cons_cell t' "Hstream".
      construct_cons_cell.
      iMod (IHds with "Hstream") as "#?"; [ eassumption |].
      eauto with iFrame. }
  Qed.

  (* Likewise, [StreamCell] is covariant in [h]. *)

  Lemma streamcell_covariant :
    ∀ ds h1 h2 c xs E,
    h1 ≤ h2 →
    StreamCell h1 c ds xs ={E}=∗
    StreamCell h2 c ds xs.
  Proof.
    intros. iIntros "#Hc".
    (* Reason by cases on [xs] and use the previous lemma. *)
    (* A few lines of proof are duplicated; never mind. *)
    destruct xs as [| x xs ].
    { deconstruct_nil_cell. construct_nil_cell. }
    { deconstruct_cons_cell t' "Hstream".
      construct_cons_cell.
      iMod (stream_covariant with "Hstream") as "#?"; [ eassumption |].
      eauto with iFrame. }
  Qed.

(* -------------------------------------------------------------------------- *)

  (* Forcing a stream. *)

  Lemma stream_force h t ds xs b :
    lies_below h b →
    let token := HToken p b in
    Stream h t (0 :: ds) xs -∗
    TC_invariant -∗
    {{{ TC 11 ∗ token }}}
      « force #t »
    {{{ c, RET «c» ; ThunkVal t c ∗ StreamCell h c ds xs ∗ token }}}.
  Proof.
    intros.
    iIntros "#Hstream".
    construct_texan_triple "(Htc & Htoken)".
    unfold_stream. deconstruct_stream.
    wp_apply (hthunk_force with "[$] [$Htc $Hthunk $Htoken]");
      first eauto with thunks.
    iIntros (c) "(Hc & #Hval & Htoken)". iApply "Post". eauto.
  Qed.

  (* Forcing an already-forced stream. *)

  Lemma stream_force_forced h t d ds xs c b :
    lies_below h b →
    let token := HToken p b in
    Stream h t (d :: ds) xs -∗
    ThunkVal t c -∗
    TC_invariant -∗
    {{{ TC 11 ∗ token }}}
      « force #t »
    {{{ RET «c» ; token }}}.
  Proof.
    intros.
    iIntros "#Hstream #Hval".
    construct_texan_triple "(Htc & Htoken)".
    unfold_stream. deconstruct_stream.
    wp_apply (hthunk_force_forced with "[$] [$Htc $Hthunk $Hval $Htoken]");
      first eauto with thunks.
    eauto.
  Qed.

  (* The combination of [pay] and [force]. *)

  Lemma stream_pay_force h t d ds xs b :
    lies_below h b →
    let token := HToken p b in
    Stream h t (d :: ds) xs -∗
    TC_invariant -∗
    {{{ TC (11 + d) ∗ token }}}
      « force #t »
    {{{ c, RET «c» ; ThunkVal t c ∗ StreamCell h c ds xs ∗ token }}}.
  Proof.
    intros.
    iIntros "#Hstream".
    construct_texan_triple "(Htc & Htoken)".
    unfold_stream. deconstruct_stream.
    wp_apply (hthunk_pay_force with "[$] [$Hthunk $Htc $Htoken]");
      first eauto with thunks.
    iIntros (c) "(Hval & #Hc & Htoken)". iApply "Post". eauto.
  Qed.

(* -------------------------------------------------------------------------- *)

  (* Subtyping on sequences of debits. *)

  (* The assertion [subdebits slack ds1 ds2 rest] means that if we are willing
     to pay [slack] time credits, then we can transform [ds1] into [ds2], both
     by paying and by moving debts forward in the stream; and, at the end, we
     have [rest] leftover time credits *inside* the final thunk. *)

  Inductive subdebits : nat → debits → debits → nat → Prop :=
  | subdebits_nil slack rest :
      rest <= slack →
      subdebits slack [] [] rest
  | subdebits_cons slack d1 ds1 d2 ds2 rest :
      (* The slack is conceptually added to the first element of the
         right-hand sequence, helping overcome its shortcomings. *)
      (* The debit on the left [d1] must be less than the debit on the
         right [d2] when provided with the extra slack. *)
      d1 <= slack + d2 →
      (* The remaining amount of slack is propagated. *)
      subdebits (slack + d2 - d1) ds1 ds2 rest →
      subdebits slack (d1 :: ds1) (d2 :: ds2) rest.

  Lemma subdebits_covariant_in_slack slack slack' ds1 ds2 rest :
    subdebits slack ds1 ds2 rest →
    slack ≤ slack' →
    subdebits slack' ds1 ds2 rest.
  Proof.
    intros Hsub. revert slack'; induction Hsub;
      intros; constructor; eauto with lia.
  Qed.

  Lemma subdebits_contravariant_in_rest slack ds1 ds2 rest rest' :
    subdebits slack ds1 ds2 rest →
    rest' ≤ rest →
    subdebits slack ds1 ds2 rest'.
  Proof.
    intros Hsub. revert rest'; induction Hsub;
      intros; constructor; eauto with lia.
  Qed.

  Lemma subdebits_reflexive slack ds slack' :
    slack' ≤ slack →
    subdebits slack ds ds slack'.
  Proof.
    revert slack' slack; induction ds as [| d ds ]; intros;
      constructor; eauto with lia.
  Qed.

  Lemma subdebits_transitive :
    ∀ slack1 ds1 ds2 rest1,
    subdebits slack1 ds1 ds2 rest1 →
    ∀ ds3 slack2 slack rest2 rest,
    subdebits slack2 ds2 ds3 rest2 →
    slack1 + slack2 ≤ slack →
    rest ≤ rest1 + rest2 →
    subdebits slack ds1 ds3 rest.
  Proof.
    induction 1; inversion 1; intros; subst;
      constructor; eauto with lia.
  Qed.

  Lemma subdebits_app slack ds1 ds2 rest ds1' ds2' rest' :
    subdebits slack ds1 ds2 rest →
    subdebits rest ds1' ds2' rest' →
    subdebits slack (ds1 ++ ds1') (ds2 ++ ds2') rest'.
  Proof.
    intros Hsub. revert ds1' ds2' rest'.
    induction Hsub; intros ds1' ds2' rest' Hsub'; cbn.
    { eauto using subdebits_covariant_in_slack. }
    constructor; eauto with lia.
  Qed.

  Lemma subdebits_length :
    ∀ ds1 ds2 slack rest,
    subdebits slack ds1 ds2 rest →
    length ds1 = length ds2.
  Proof.
    intros *; induction 1; simpl; intuition eauto with lia.
  Qed.

  Lemma subdebits_repeat slack a b n :
    a ≤ b →
    subdebits slack (repeat a n) (repeat b n) (slack + (b - a) * n).
  Proof.
    revert slack; induction n as [| n ]; intros slack ?; cbn.
    { rewrite Nat.mul_0_r Nat.add_0_r. by constructor. }
    { constructor; first lia.
      eapply subdebits_contravariant_in_rest; eauto with lia. }
  Qed.

  Fixpoint sum ds :=
    match ds with
    | [] => 0
    | d :: ds => d + sum ds
    end.

  Lemma subdebits_alternate_characterization_1 :
    ∀ slack ds1 ds2 rest,
    subdebits slack ds1 ds2 rest →
    ∀ k,
    sum (take k ds1) ≤ slack + sum (take k ds2).
  Proof.
    induction 1;
    intros k;
    repeat rewrite take_nil; simpl in *; try lia.
    destruct k as [| k ]; simpl; [ lia |].
    specialize IHsubdebits with k.
    lia.
  Qed.

  Lemma subdebits_alternate_characterization_2 :
    ∀ ds1 ds2 slack,
    length ds1 = length ds2 →
    (∀ k, sum (take k ds1) ≤ slack + sum (take k ds2)) →
    subdebits slack ds1 ds2 0.
  Proof.
    induction ds1 as [| d1 ds1 ]; destruct ds2 as [| d2 ds2 ];
    simpl;
    intros slack Hlen Hsum;
    try lia.
    { constructor. lia. }
    { constructor.
      { specialize Hsum with 1. simpl in Hsum. lia. }
      { eapply IHds1; [ congruence |].
        intros k.
        specialize Hsum with (S k). simpl in Hsum. lia. }
    }
  Qed.

  Lemma subdebits_alternate_characterization ds1 ds2 slack :
    subdebits slack ds1 ds2 0 ↔
    length ds1 = length ds2 ∧
    ∀ k, sum (take k ds1) ≤ slack + sum (take k ds2).
  Proof.
    intuition eauto using subdebits_alternate_characterization_1,
      subdebits_alternate_characterization_2, subdebits_length.
  Qed.

  Local Lemma streamcell_nil h c ds1 ds2 :
    length ds1 = length ds2 →
    StreamCell h c ds1 [] -∗
    StreamCell h c ds2 [].
  Proof.
    intros. iIntros "Hc".
    deconstruct_nil_cell.
    construct_nil_cell.
  Qed.

  Local Ltac mv H' H :=
    iClear H; iRename H' into H.

  Local Lemma stream_cell_forward_debt_aux slack h c ds1 ds2 xs E :
    length ds1 = length ds2 →
    (
      ∀ xs h t,
      Stream h t ds1 xs -∗ TC slack ={E}=∗ Stream h t ds2 xs
    ) →
    StreamCell h c ds1 xs -∗
    TC slack ={E}=∗
    □ StreamCell h c ds2 xs.
  Proof.
    intros Hlen IH.
    iIntros "#Hc Hslack".
    destruct xs as [| x xs ].
    (* Case: the list is empty. *)
    { iModIntro.
      iApply (streamcell_nil with "Hc").
      eauto. }
    (* Case: the list is nonempty. *)
    { deconstruct_cons_cell t' "Hstream".
      (* Exploit the induction hypothesis. *)
      iMod (IH with "Hstream Hslack") as "#Hstream'"; iModIntro.
      construct_cons_cell. }
  Qed.

  Lemma stream_forward_debt :
    ∀ ds1 ds2 slack xs h t E,
    subdebits slack ds1 ds2 0 →
    ↑ThunkPayment ⊆ E →
    Stream h t ds1 xs -∗
    TC slack ={E}=∗
    Stream h t ds2 xs.
  Proof.
    intros * Hsub; revert xs h t E; induction Hsub;
    try rewrite unfold_stream_contradictory;
    try solve [ tauto | eauto 3 ];
    intros xs h t E ?.
    iIntros "#Hstream Hslack".
    unfold_stream. deconstruct_stream.
    unfold_stream.
    assert (length ds1 = length ds2) by eauto using subdebits_length.
    (* Two cases arise. If [d1] is less than [d2], then we want to use the
       consequence rule to increase the apparent debt of the first thunk and
       gain more slack that can be used to pay subsequent thunks. On the other
       hand, if [d1] is greater than [d2], then we have some slack that we
       want to use to pay the first thunk and decrease its apparent debt. *)
    assert (d1 ≤ d2 ∨ d2 ≤ d1) as [|] by lia.

    (* Case: [d1 ≤ d2 ≤ slack + d2]. *)
    {
      (* Apply the consequence rule. *)
      rewrite (_ : d2 = d1 + (d2 - d1)); last lia.
      iMod (hthunk_consequence with "[Hslack] Hthunk") as "$"; last done.
      (* We get more slack! *)
      iIntros (c) "Hmore_slack #Hc".
      iCombine "Hslack Hmore_slack" as "Hslack".
      rewrite (_ : slack + (d2 - d1) = slack + d2 - d1); last lia.
      (* We now have to reason about the stream cell. *)
      (* The result follows from the previous lemma and
         from the induction hypothesis. *)
      iMod (stream_cell_forward_debt_aux with "Hc Hslack") as "$"; eauto 2.
    }

    (* Case: [d2 ≤ d1 ≤ slack + d2]. *)
    {
      (* Pay on the front thunk. *)
      rewrite (_ : slack = (d1 - d2) + (slack + d2 - d1)); last lia.
      iDestruct "Hslack" as "(Hpayment & Hslack)".
      iMod (hthunk_pay with "Hthunk Hpayment") as "Hthunk'"; first assumption.
      mv "Hthunk'" "Hthunk".
      rewrite (_ : d1 - (d1 - d2) = d2); last lia.
      (* The front thunk now has the desired debt. *)
      (* We must now apply the consequence rule in order to adjust the
         postcondition of the front thunk. *)
      rewrite {3} (_ : d2 = d2 + 0); last lia.
      iMod (hthunk_consequence with "[Hslack] Hthunk") as "$"; last done.
      (* In this case, we do not get more slack. *)
      iIntros (c) "_ #Hc".
      (* We now have to reason about the stream cell. *)
      (* The result follows from the previous lemma and
         from the induction hypothesis. *)
      iMod (stream_cell_forward_debt_aux with "Hc Hslack") as "$"; eauto 2.
    }

  Qed.

  Lemma stream_cell_forward_debt slack h c ds1 ds2 xs E :
    subdebits slack ds1 ds2 0 →
    ↑ThunkPayment ⊆ E →
    StreamCell h c ds1 xs -∗
    TC slack ={E}=∗
    StreamCell h c ds2 xs.
  Proof.
    iIntros (Hsub Hmask) "#Hc Hslack".
    iMod (stream_cell_forward_debt_aux with "Hc Hslack") as "#$"; last done.
    { eauto using subdebits_length. }
    { eauto using stream_forward_debt. }
  Qed.

  Local Ltac construct_action :=
    iIntros "Htoken Htc" (ψ) "Post".

  (* Evaluating [lazy e], where the expression [e] consumes [k] time credits
     and must produce a stream cell, costs 5 credits now and returns a stream
     whose front cell has k debits. *)

  (* We could prove a slightly more precise spec, stating that the cost is
     4 credits now and that the front cell has [k+1] debits. The simpler
     specification seems preferable and is just as useful in practice. *)

  (* The expression [e] receives the token [HToken p (Some h)] and must return
     it. When [h] is greater than 0, this is synonymous with [token (h-1)].
     When [h] is zero, this token does not allow forcing any thunk. Thus, the
     new thunk is allowed earlier to force thunks at lower heights, but
     not thunks at the same height as itself or higher. *)

  Definition isLazyCell k h ds xs e : iProp :=
    TC k -∗ HToken p (Some h) -∗
    ∀ ψ, (∀ c, StreamCell h c ds xs -∗ HToken p (Some h) -∗ ψ «c»%V) -∗
    WP «e» {{ ψ }}.

  Lemma lazy_spec h e ds xs k :
    TC_invariant -∗
    {{{ TC 5 ∗ isLazyCell k h ds xs e }}}
      « lazy e »
    {{{ t, RET #t ; Stream h t (k :: ds) xs }}}.
  Proof.
    intros.
    construct_texan_triple "(Htc & He)".
    (* The tick translation of [lazy e] involves two ticks. *)
    rewrite translate_lazy_expr.
    (* We pay one credit for the second tick, which is executed first. *)
    wp_tick_closure.
    (* Then, we recognize an application of [create]. *)
    untranslate.
    (* We pay 3 credits for [create], and keep one credit. *)
    iDestruct "Htc" as "(H1 & H3)".
    wp_apply (hthunk_create p h with "[$] [$H3 H1 He]"); last first.
    { iIntros (t) "#Hthunk". iApply "Post". construct_stream "Hthunk". }
    (* We now examine the cost of this action. *)
    construct_action.
    (* We have wisely stored one credit, which pays for the call to the
       constant function that returns [c]. *)
    wp_tick_lam. iClear "H1".
    (* There remain [k] credits, which allow executing [e]. *)
    (* We have the required token. *)
    iApply ("He" with "Htc Htoken").
    iIntros (c) "#Hc Htoken".
    iApply ("Post" with "Htoken"). iFrame "Hc".
  Qed.

  Lemma lazy_val_spec h c ds xs :
    StreamCell h c ds xs -∗
    TC_invariant -∗
    {{{ TC 5 }}}
      « lazy c »
    {{{ t, RET #t ; Stream h t (0 :: ds) xs }}}.
  Proof.
    iIntros "#Hc".
    construct_texan_triple "Htc".
    (* The tick translation of [lazy e] involves two ticks. *)
    rewrite translate_lazy_expr.
    (* We pay one credit for the second tick, which is executed first. *)
    wp_tick_closure.
    (* Then, we recognize an application of [create]. *)
    untranslate.
    (* We pay 3 credits for [create], and keep one credit. *)
    iDestruct "Htc" as "(H1 & H3)".
    wp_apply (hthunk_create with "[$] [$H3 H1]"); last first.
    { iIntros (t) "#Hthunk". iApply "Post". construct_stream "Hthunk". }
    (* We now examine the cost of this action. *)
    construct_action.
    (* We have wisely stored one credit, which pays for the call to the
       constant function that returns [c]. *)
    wp_tick_lam.
    (* Done. *)
    iApply ("Post" with "Htoken"). iFrame "Hc".
  Qed.

  Lemma NIL_spec h :
    TC_invariant -∗
    {{{ TC 1 }}} « NIL » {{{ c, RET « c »; StreamCell h c [] [] }}}.
  Proof.
    construct_texan_triple "Htc".
    rewrite /NIL. wp_tick_inj.
    rewrite untranslate_litv. untranslate.
    iApply "Post".
    eauto.
  Qed.

  Lemma CONS_spec h t ds x xs :
    Stream h t ds xs -∗
    TC_invariant -∗
    {{{ TC 2 }}}
      « CONS x #t »
    {{{ c, RET « c »; StreamCell h c ds (x :: xs) }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "Htc".
    (* TODO These back and forth translations are really painful: *)
    rewrite -untranslate_injr -untranslate_pair.
    wp_tick_pair.
    wp_tick_inj.
    rewrite untranslate_litv. untranslate.
    iApply "Post".
    construct_cons_cell.
  Qed.

  Lemma nil_spec h :
    TC_invariant -∗
    {{{ TC 6 }}}
      « nil »
    {{{ t, RET #t ; Stream h t (0 :: []) [] }}}.
  Proof.
    construct_texan_triple "Htc".
    iDestruct "Htc" as "(H1 & H5)".
    wp_apply (lazy_spec _ _ [] [] 0 with "[$] [$H5 H1]"); eauto 2.
    (* TODO make this a lemma: *)
    rewrite /isLazyCell.
    iIntros "_ Htoken" (ψ) "Post".
    iApply (NIL_spec with "[$] [$H1]").
    iNext.
    iIntros (c) "Hc".
    iApply ("Post" with "Hc Htoken").
  Qed.

  Lemma cons_spec h t ds x xs :
    Stream h t ds xs -∗
    TC_invariant -∗
    {{{ TC 8 }}}
      « cons x #t »
    {{{ t', RET #t' ; Stream h t' (2 :: ds) (x :: xs) }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "Htc".
    wp_tick_lam. wp_tick_let.
    push_subst.
    wp_apply (lazy_spec with "[$] [$Htc]"); last first.
    { iIntros (t') "Hstream'". iApply "Post". iFrame. }
    { (* TODO make this a lemma: *)
      rewrite /isLazyCell.
      iIntros "Htc Htoken" (ψ) "Post".
      iApply (CONS_spec with "[$] [$] [$]").
      iNext.
      iIntros (c) "Hc".
      iApply ("Post" with "Hc Htoken"). }
  Qed.

  Lemma extract_spec h t ds x xs b :
    lies_below h b →
    let token := HToken p b in
    Stream h t (0 :: ds) (x :: xs) -∗
    TC_invariant -∗
    {{{ TC 22 ∗ token }}}
      « extract #t »
    {{{ t', RET («x», #t'); Stream h t' ds xs ∗ token }}}.
  Proof.
    intros.
    iIntros "#Hstream".
    construct_texan_triple "(Htc & Htoken)".
    wp_tick_lam.
    (* Force the stream [t]. *)
    divide_credit "Htc" 10 11.
    wp_apply (stream_force with "[#] [$] [$Htc' $Htoken]");
      first eauto with thunks;
      first done.
    iClear "Hstream".
    iIntros (c) "(_ & #Hc & Htoken)".
    deconstruct_cons_cell t' "Hstream'".
    (* Match on the resulting cell. The second branch must be taken. *)
    wp_tick_match. do 2 (wp_tick_proj ; wp_tick_let).
    (* Construct a pair. *)
    wp_tick_pair.
    (* Conclude. *)
    iApply "Post". iFrame "Htoken". eauto.
  Qed.

  Fixpoint ListV xs : val :=
    match xs with
    | []    =>  NILV
    | x::xs =>  CONSV x (ListV xs)
    end.

  Definition isList l xs : iProp :=
    ⌜l = ListV xs⌝.

  Lemma rev_append_spec_aux h :
    ∀ xs c ds ys ,
    StreamCell h c ds ys -∗
    TC_invariant -∗
    {{{ TC (6 + 19 * length xs) }}}
      « rev_append (ListV xs) c »
    {{{ c', RET «c'» ;
        StreamCell h c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    induction xs as [|x xs]; intros c ds ys;
    iIntros "#Hc";
    construct_texan_triple "Htc".

    (* Case: the list is empty. *)
    { simpl.
      wp_tick_lam. wp_tick_let. wp_tick_match.
      iApply "Post". iFrame "Hc". }

    (* Case: the list is nonempty. *)
    {
      rewrite (_ : 6 + 19 * length (_ :: xs) = (6 + 19 * length xs) + 19);
        last (cbn; lia).
      iDestruct "Htc" as "[Hrest Htc]".
      (* Step. *)
      wp_tick_lam. wp_tick_let. wp_tick_match.
      do 2 (wp_tick_proj ; wp_tick_let).
      push_subst.
      (* The next redex is [lazy c]. *)
      divide_credit "Htc" 2 5.
      wp_apply (lazy_val_spec with "[$Hc] [$] [$Htc']").
      (* Continue stepping. *)
      iIntros (t) "#Hthunk".
      wp_tick_pair. wp_tick_inj.
      rewrite untranslate_litv. untranslate.
      wp_apply (IHxs _ (0 :: ds) (x :: ys) with "[] [$] [$Hrest]").
      { construct_cons_cell. }
      { iIntros (c') "#Hc'". iApply "Post".
        by rewrite /= app_comm_cons repeat_cons -assoc -assoc /=. }
    }
  Qed.

  Lemma rev_append_spec h l xs c ds ys :
    isList l xs -∗
    StreamCell h c ds ys -∗
    TC_invariant -∗
    {{{ TC (6 + 19 * length xs) }}}
      « rev_append l c »
    {{{ c', RET «c'» ;
        StreamCell h c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    iIntros "%Hxs #Hc". subst.
    construct_texan_triple "Htc".
    wp_apply (rev_append_spec_aux with "[$] [$] [$]").
    eauto.
  Qed.

  Lemma NILV_spec h :
    ⊢ StreamCell h NILV [] [].
  Proof.
    iIntros. simpl. eauto.
  Qed.

  Lemma rev_spec h l xs :
    isList l xs -∗
    TC_invariant -∗
    {{{ TC 13 }}}
      « rev l »
    {{{ t, RET «#t» ;
        Stream h t ((19 * length xs) :: repeat 0 (length xs)) (List.rev xs) }}}.
  Proof.
    iIntros "#Hl".
    construct_texan_triple "Htc".
    (* We pay 1 credit here. *)
    wp_tick_lam. push_subst.
    (* [lazy (...)] costs 5 credits. *)
    divide_credit "Htc" 7 5.
    wp_apply (lazy_spec with "[$] [$Htc' Htc] Post").
    (* Examine the body of this suspension. *)
    rewrite /isLazyCell.
    iIntros "Htc' Htoken" (ψ) "Post".
    (* Evaluate NIL, consuming 1 credit. *)
    wp_tick_inj.
    (* The call [rev_append l NILV] consumes the remaining credits. *)
    rewrite untranslate_litv. untranslate.
    wp_apply (rev_append_spec with "[$Hl] [] [$] [Htc Htc']").
    { iApply NILV_spec. }
    { rewrite TC_plus. iFrame. }
    rewrite !app_nil_r.
    iIntros (c') "Hc'".
    iApply ("Post" with "Hc' Htoken").
  Qed.

  Definition A := 30.
  Definition B := 11.

  Fixpoint debit_append ds1 ds2 :=
    match ds1, ds2 with
    | [], _
    | _, [] =>
        (* These cases cannot occur. *)
        ds1 ++ ds2
    | [d1], d2 :: ds2 =>
        (A + d1 + B + d2) :: ds2
    | d1 :: ds1, _ =>
        (A + d1) :: debit_append ds1 ds2
    end.

  Lemma debit_append_step d1 ds1 d2 ds2 :
    length ds1 > 0 →
    debit_append (d1 :: ds1) (d2 :: ds2) =
    (A + d1) :: debit_append ds1 (d2 :: ds2).
  Proof.
    intro Hlen1.
    destruct ds1 as [| d1' ds1' ]; [ simpl in Hlen1; lia |].
    reflexivity.
  Qed.

  Lemma debit_append_join_middle ds1 d1 d2 ds2 :
    debit_append (ds1 ++ [d1]) (d2 :: ds2) =
    map (λ d, A + d) ds1 ++ (A + d1 + B + d2) :: ds2.
  Proof.
    revert d1 d2 ds2. induction ds1 as [| d ds1 ]; intros d1 d2 ds2; auto.
    rewrite (_: (d :: ds1) ++ [d1] = d :: (ds1 ++ [d1])) //.
    rewrite debit_append_step. 2: rewrite app_length /=; lia.
    rewrite IHds1 //.
  Qed.

  Lemma debits_induction P :
    (∀ d, P [d]) →
    (∀ d ds, length ds > 0 → P ds → P (d :: ds)) ->
    ∀ ds, length ds > 0 → P ds.
  Proof.
    intros Hbase Hstep.
    induction ds as [| d ds ]; [ simpl; lia | intros _ ].
    destruct ds as [| d' ds ].
    { apply Hbase. }
    { apply Hstep; [ simpl; lia |].
      apply IHds; simpl; lia. }
  Qed.

  Lemma length_debit_append :
    ∀ ds1,
    length ds1 > 0 →
    ∀ d2 ds2,
    length (debit_append ds1 (d2 :: ds2)) = length ds1 + length ds2.
  Proof.
    (* Reason by induction on [ds1]. *)
    intros ds1 Hlen1. pattern ds1.
    eapply debits_induction; [ | | exact Hlen1 ]; clear ds1 Hlen1.

    (* Case: [ds1] is a singleton list. *)
    { intros d1 d2 ds2. reflexivity. }

    (* Case: [ds1] not a singleton list. *)
    { intros d1 ds1 Hlen1 IH d2 ds2.
      rewrite debit_append_step; last exact Hlen1.
      simpl length. rewrite IH. lia. }
  Qed.

  Lemma translate_case e0 e1 e2 :
    « Case e0 e1 e2 » =
    Case (tick $ « e0 »)
          (tick_case_branch (Lam <> « e1 »))
          (tick_case_branch (Lam <> « e2 »)).
    Proof. reflexivity. Qed.

  Lemma append_spec h t1 t2 ds1 ds2 xs1 xs2 :
    Stream h t1 ds1 xs1 -∗
    Stream h t2 ds2 xs2 -∗
    TC_invariant -∗
    {{{ TC 8 }}}
      « append #t1 #t2 »
    {{{ t, RET «#t» ;
        Stream (h + 1) t (debit_append ds1 ds2) (xs1 ++ xs2) }}}.
  Proof.
    (* First, extract length information. *)
    iIntros "#Hstream1 #Hstream2".
    iPoseProof (stream_nonzero_length with "Hstream1") as "%Hlen1".
    (* The list [ds2] must be nonempty; rename it [d2 :: ds2]. *)
    iPoseProof (stream_nonzero_length with "Hstream2") as "%Hlen2".
    destruct ds2 as [| d2 ds2 ]; [ simpl in Hlen2; lia | clear Hlen2 ].
    (* Move the hypotheses back into the goal. *)
    iStopProof.
    revert d2 ds2 t1 t2 h xs1 xs2.
    (* Reason by induction on [ds1]. *)
    pattern ds1.
    eapply debits_induction; [| | assumption ]; clear dependent ds1.

    (* Case: [ds1] is a singleton list. *)
    {
      intros d1 d2 ds2 t1 t2 h xs1 xs2.
      iIntros "(#Hstream1 & #Hstream2)".
      construct_texan_triple "Htc".
      (* Step. We pay 3 credits here. *)
      wp_tick_lam. wp_tick_let. push_subst.
      (* [lazy (...)] costs 5 credits. *)
      wp_apply (lazy_spec with "[$] [$Htc]"); last first.
      { iIntros (t) "Hstream". iApply "Post". iFrame "Hstream". }
      (* Now, examine the body of the suspension. *)
      rewrite /isLazyCell.
      iIntros "Htc Htoken" (ψ) "Post".
      (* The code forces [t1], enters the first branch, then forces [t2]. *)
      (* Force [t1]. *)
      (* TODO The goal does have the desired shape, namely
              « force #t1 » in an evaluation context,
              but the tactic wp_apply does not recognize this. *)
      rewrite translate_case.
      unfold A; divide_credit "Htc" (19 + (B + d2)) (11 + d1).
      wp_apply (stream_pay_force with "[#] [$] [$Htc' $Htoken]").
      { eauto with thunks. }
      { iFrame "Hstream1". }
      iIntros (c) "(_ & #Hc & Htoken)".
      (* The list [xs1] must be empty. *)
      streamcell_nil_cell.
      rewrite app_nil_l.
      (* Enter the first branch, consuming 3 credits. *)
      wp_tick_match.
      (* Allow a ghost update after forcing [t2]. *)
      iApply wp_fupd.
      (* Force [t2]. *)
      rewrite (untranslate_litv t2). untranslate.
      divide_credit "Htc" 16 (B + d2).
      wp_apply (stream_pay_force with "[#] [$] [$Htc' $Htoken]").
      { eauto with thunks. }
      { iFrame "Hstream2". }
      iIntros (c) "(_ & #Hc & Htoken)".
      (* Promote the first cell of the second list from level [g] to [g+1]. *)
      iMod (streamcell_covariant _ h (h+1) with "Hc") as "#Hc'"; first lia.
      (* Conclude. *)
      iApply ("Post" with "Hc' Htoken").
    }

    (* Case: [ds1] is not a singleton list. *)
    {
      intros d1 ds1 ? IH d2 ds2 t1 t2 h xs1 xs2.
      (* Simplify the goal. *)
      rewrite debit_append_step; last eassumption.
      (* We are in business. *)
      iIntros "(#Hstream1 & #Hstream2)".
      construct_texan_triple "Htc".
      (* Step. We pay 3 credits here. *)
      wp_tick_lam. wp_tick_let. push_subst.
      (* [lazy (...)] costs 5 credits. *)
      wp_apply (lazy_spec with "[$] [$Htc]"); last first.
      { iIntros (t) "Hstream". iApply "Post". iFrame "Hstream". }
      (* Now, examine the body of the suspension. *)
      rewrite /isLazyCell.
      iIntros "Htc Htoken" (ψ) "Post".
      (* The code forces [t1], enters the second branch, and returns a CONS
         cell. *)
      (* Force [t1]. *)
      rewrite translate_case.
      unfold A; divide_credit "Htc" (19) (11 + d1).
      wp_apply (stream_pay_force with "[#] [$] [$Htc' $Htoken]").
      { eauto with thunks. }
      { iFrame "Hstream1". }
      iIntros (c) "(_ & #Hc & Htoken)".
      iClear (t1) "Hstream1".
      (* The list [xs1] must be nonempty: rename it [x1 :: xs1]. *)
      iPoseProof (streamcell_cons_cell with "Hc") as "%Hneq"; eauto 2.
      destruct xs1 as [| x1 xs1 ]; [ congruence | clear Hneq ].
      deconstruct_cons_cell t1 "Hstream1".
      (* Enter the first second, consuming 3 credits. *)
      wp_tick_match.
      do 2 (wp_tick_proj ; wp_tick_let).
      (* Untranslate with care. TODO *)
      rewrite (untranslate_litv t1) (untranslate_litv t2).
      rewrite !untranslate_val !untranslate_app.
      (* Use the induction hypothesis. *)
      divide_credit "Htc" 2 8.
      wp_apply (IH with "[#] [$] [$Htc']"); [ eauto |].
      iClear (t1 t2) "Hstream1 Hstream2".
      iIntros (t') "#Hstream'".
      untranslate.
      (* Build a CONS cell. *)
      wp_apply (CONS_spec with "[$Hstream'] [$] [$Htc]").
      iIntros (c) "#Hc".
      (* Conclude. *)
      iApply ("Post" with "Hc Htoken").
    }
  Qed.

  (* TODO create a layer where the parameter [h] disappears, if possible *)
  (* what about the parameter [p]? *)
  Definition Stream' t ds xs : iProp :=
    ∃ h, Stream h t ds xs.

End Proofs.
