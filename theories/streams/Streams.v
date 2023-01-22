From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits ThunksCode ThunksBase Gthunks.
Open Scope nat_scope.

Section Stream.

Notation NIL := (InjL (LitV LitUnit)).
Notation CONS v vs := (InjR (v%V, vs%V)).
Notation NILV := (InjLV (LitV LitUnit)).
Notation CONSV v vs := (InjRV (v, vs)%V).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' ( x , xs ) => e2 'end'" :=
  (Match e0
    <>%bind (* => *) e1
    xs%bind (* => *) (Lam x%bind (Lam xs%bind e2%E (Snd xs%bind)) (Fst xs%bind))
                     (* this is let: x := Fst xs in let: xs := Snd xs in e2 *)
  )
  (e0, e1, x, xs, e2 at level 200, only parsing) : expr_scope.

Definition lazy e := (create (Lam <>%bind e))%E.

Lemma subst_lazy x v e :
  subst x v (lazy e) = lazy (subst x v e).
Proof.
  reflexivity.
Qed.

Opaque lazy.

(*
type 'a stream =
  'a cell Lazy.t

and 'a cell =
  | Nil
  | Cons of 'a * 'a stream
*)

Definition nil : expr := (* : stream *)
  lazy NIL.

Definition cons : val := (* : val → stream → stream *)
  λ: "x" "xs",
    lazy (CONS "x" "xs").

Definition extract : val := (* : stream → val × stream *)
  λ: "xs",
    match: force "xs" with
      NIL              => #() (* this case must not happen *)
    | CONS ("x", "xs") => ("x", "xs")
    end.

Definition rev_append : val := (* : list → cell → cell *)
  rec: "rev_append" "xs" "ys" :=
    match: "xs" with
      NIL              => "ys"
    | CONS ("x", "xs") => "rev_append" "xs" (CONS "x" (lazy "ys"))
    end.

Definition rev : val := (* : list → stream *)
  λ: "xs",
    lazy (rev_append "xs" NIL).

Definition append : val := (* : stream → stream → stream *)
  rec: "append" "xs" "ys" :=
    lazy (
      match: force "xs" with
        NIL              => force "ys"
      | CONS ("x", "xs") => CONS "x" ("append" "xs" "ys")
      end
    ).

Section StreamProofs.

  Notation valO := (valO heap_lang).
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γt *)
  Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
  Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
  Context `{na_invG Σ}.
  Notation iProp := (iProp Σ).
  Open Scope nat_scope.

  (* This lemma cannot be used in a rewriting database; that would
     lead to divergence. *)
  Lemma untranslate_litv t :
    #t = «#t»%V.
  Proof. reflexivity. Qed.

  (* This lemma is limited to an expression of the form «e» so as to
     guarantee that it is used only outside the translation brackets,
     never inside them. Indeed, translation brackets must never be
     nested. *)
  Lemma untranslate_subst_litv x t e :
    subst x #t «e» = subst x «#t»%V «e».
  Proof.
    reflexivity.
  Qed.

  Lemma untranslate_pairv v1 v2 :
    («v1», «v2»)%V  = « (v1, v2) »%V.
  Proof. reflexivity. Qed.

  Lemma untranslate_pair e1 e2 :
    (tick «e1», «e2»)%E  = « (e1, e2) »%E.
  Proof. reflexivity. Qed.

  Lemma untranslate_injlv v :
    (InjLV «v»)%V = «InjLV v»%V.
  Proof. reflexivity. Qed.

  Lemma untranslate_injrv v :
    (InjRV «v»)%V = «InjRV v»%V.
  Proof. reflexivity. Qed.

  Lemma untranslate_injl e :
    (InjL (tick «e»))%E = «InjL e»%E.
  Proof. reflexivity. Qed.

  Lemma untranslate_injr e :
    (InjR (tick «e»))%E = «InjR e»%E.
  Proof. reflexivity. Qed.

  Lemma untranslate_lambda f x e :
    RecV f x (translation e) =
    translationV (RecV f x e).
  Proof. reflexivity. Qed.

  Lemma untranslate_app e1 e2 :
    (tick «e1» «e2»)%E = «e1 e2»%E.
  Proof. reflexivity. Qed.

  Lemma untranslate_val v :
    Val (translationV v) =
    translation (Val v).
  Proof. reflexivity. Qed.

  Hint Rewrite
    untranslate_pairv
    untranslate_pair
    untranslate_injlv
    untranslate_injrv
    untranslate_injl
    untranslate_injr
    untranslate_lambda
    untranslate_app
    untranslate_val
  : untranslate.

  Ltac untranslate :=
    autorewrite with untranslate.

  Hint Rewrite
    untranslate_subst_litv
    subst_lazy
  : push_subst.

  Hint Rewrite
    <- translation_subst
  : push_subst.

  Ltac push_subst :=
    repeat progress (autorewrite with push_subst; simpl subst).
    (* TODO not quite right, see above *)

  (* [divide H] destructs the Iris hypothesis [H] and names the two
     hypotheses thus obtained [H] and [H']. This is typically useful
     when [H] is a hypothesis of the form [TC (n1 + n2)]. *)

  Ltac divide H :=
    let ipat := eval cbv in ( "(" ++ H ++ "&" ++ H ++ "')")%string in
    iDestruct H as ipat.

  (* [pay_out_of H] destructs the Iris hypothesis [H], which must be
     of the form [TC k], into two hypotheses [TC (k - ?cost)] and
     [TC ?cost], where [?cost] is a fresh metavariable. The proof
     obligation [?cost <= k] is scheduled last, so it can be proved
     after [?cost] has been instantiated. *)

  Ltac pay_out_of H :=
    match goal with
    |- context[environments.Esnoc _ (INamed H) (TC ?k)] =>
      let cost := fresh "cost" in
      evar (cost : nat);
      let Hcost := fresh "Hcost" in
      assert (Hcost: cost ≤ k); first last; [
      rewrite [in TC k] (_ : k = (k - cost) + cost); [
      unfold cost; clear Hcost; divide H | lia ]
      |]
    end.

  Definition debit := nat.
  Definition debits := list debit.

  Implicit Type t : loc.
  Implicit Type c l : val.
  Implicit Type x y z : val.
  Implicit Type xs ys zs : list val.
  Implicit Type d : debit.
  Implicit Type ds : debits.
  Implicit Type g : generation.
  Implicit Type E F : coPset.

  Variable p : na_inv_pool_name.

  (* TODO re-think the inequality g' ≤ g *)
  (* we want every thunk in the stream to have level g' ≤ g *)
  Fixpoint isStream g t ds xs : iProp :=
    match ds with
    | []    =>
        False
    | d :: ds =>
        ⌜ length ds = length xs ⌝ ∗
        Gthunk p g t d (λ c,
          match xs with
          | []      =>          ⌜c = NILV⌝ ∗ ⌜ ds = [] ⌝
          | x :: xs => ∃ g' t', ⌜c = CONSV x #t'⌝ ∗ ⌜g' ≤ g⌝ ∗
                                isStream g' t' ds xs
          end)
    end%I.

  Definition isStreamCell g c ds xs : iProp :=
    match xs with
    | []      =>          ⌜c = NILV⌝ ∗ ⌜ ds = [] ⌝
    | x :: xs => ∃ g' t', ⌜c = CONSV x #t'⌝ ∗ ⌜g' ≤ g⌝ ∗
                          isStream g' t' ds xs
    end.

  Lemma unfold_isStream g t ds xs :
    isStream g t ds xs =
    match ds with
    | []    =>
        False
    | d :: ds =>
        ⌜ length ds = length xs ⌝ ∗
        Gthunk p g t d (λ c, isStreamCell g c ds xs)
    end%I.
  Proof.
    destruct ds; reflexivity.
  Qed.

  Ltac unfold_isStream :=
    rewrite unfold_isStream.

  Local Ltac deconstruct_stream :=
    iDestruct "Hstream" as "(%Heq & #Hthunk)".

  Lemma unfold_isStream_contradictory g t xs :
    isStream g t [] xs = False%I.
  Proof.
    reflexivity.
  Qed.

  Global Instance isStream_persistent :
    ∀ ds xs g t,
    Persistent (isStream g t ds xs).
  Proof.
    induction ds; destruct xs; exact _.
  Qed.

  Global Instance isStreamCell_persistent g c ds xs :
    Persistent (isStreamCell g c ds xs).
  Proof.
    destruct xs; exact _.
  Qed.

  Lemma isStream_length :
    ∀ ds xs g t,
    isStream g t ds xs -∗
    ⌜(length ds = 1 + length xs)%nat⌝.
  Proof.
    destruct ds; destruct xs; intros; simpl; eauto 2;
    iIntros "Hstream";
    deconstruct_stream;
    iPureIntro; lia.
  Qed.

  Local Ltac deconstruct_stream_cell :=
    iDestruct "Hc" as (g' t') "(-> & %Hg'g & Hstream)".

  Local Ltac pure_conjunct :=
    iSplitR; [ solve [ eauto ] |].

  Local Ltac construct_stream_cell :=
    iExists _, _; do 2 pure_conjunct; eauto.

  Lemma isStreamCell_length :
    ∀ ds xs g c,
    isStreamCell g c ds xs -∗
    ⌜(length ds = length xs)%nat⌝.
  Proof.
    destruct xs; intros; simpl.
    { iIntros "(_ & %Hds)". subst ds. eauto. }
    { iIntros "Hc".
      deconstruct_stream_cell.
      iApply isStream_length. eauto. }
  Qed.

  (* Forcing a stream. *)

  Notation token g :=
    (own_gens_below_bound p (Some (g + 1))).

  Local Ltac construct_texan_triple ipat :=
    iIntros "#?"; (* introduce TC_invariant *)
    iIntros (Φ) "!>";
    iIntros ipat;
    iIntros "Post".

  Lemma stream_force g t ds xs :
    isStream g t (0 :: ds) xs -∗
    TC_invariant -∗
    {{{ TC 11 ∗ token g }}}
      « force #t »
    {{{ c, RET «c» ; ThunkVal t c ∗ isStreamCell g c ds xs ∗ token g }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "(Htc & Htoken)".
    unfold_isStream. deconstruct_stream.
    wp_apply (force_spec with "[#] [$Htc $Hthunk $Htoken]"); eauto with thunks.
    iIntros (c) "(Hval & #Hc & Htoken)". iApply "Post". eauto.
  Qed.

  (* Subtyping on sequences of debits. *)

  Fixpoint subdebits slack ds1 ds2 :=
    match ds1, ds2 with
    | [], [] =>
        True
    | d1 :: ds1, d2 :: ds2 =>
        (* The slack is conceptually added to the first element of the
           right-hand sequence, helping overcome its shortcomings. *)
        let d2 := slack + d2 in
        (* [d1] must be less than [d2]. *)
        d1 <= d2 ∧
        (* If some slack remains, then it is propagated. *)
        let slack := d2 - d1 in
        subdebits slack ds1 ds2
    | [], _ :: _
    | _ :: _, [] =>
        (* Nonsensical cases. *)
        False
    end.

  Lemma subdebits_length :
    ∀ ds1 ds2 slack,
    subdebits slack ds1 ds2 →
    length ds1 = length ds2.
  Proof.
    induction ds1; destruct ds2; simpl; intuition eauto with lia.
  Qed.

  Fixpoint sum ds :=
    match ds with
    | [] => 0
    | d :: ds => d + sum ds
    end.

  Lemma subdebits_alternate_characterization_1 :
    ∀ ds1 ds2 slack,
    subdebits slack ds1 ds2 →
    ∀ k,
    sum (take k ds1) ≤ slack + sum (take k ds2).
  Proof.
    induction ds1 as [| d1 ds1 ]; destruct ds2 as [| d2 ds2 ];
    intros slack Hsub k;
    repeat rewrite take_nil; simpl in *; try lia.
    destruct Hsub as (? & Hsub).
    destruct k as [| k ]; simpl; [ lia |].
    generalize (IHds1 _ _ Hsub k); intro.
    lia.
  Qed.

  Lemma subdebits_alternate_characterization_2 :
    ∀ ds1 ds2 slack,
    length ds1 = length ds2 →
    (∀ k, sum (take k ds1) ≤ slack + sum (take k ds2)) →
    subdebits slack ds1 ds2.
  Proof.
    induction ds1 as [| d1 ds1 ]; destruct ds2 as [| d2 ds2 ];
    simpl;
    intros slack Hlen Hsum;
    try lia.
    split.
    { specialize Hsum with 1. simpl in Hsum. lia. }
    { eapply IHds1; [ congruence |].
      intros k.
      specialize Hsum with (S k). simpl in Hsum. lia. }
  Qed.

  Lemma subdebits_alternate_characterization ds1 ds2 slack :
    subdebits slack ds1 ds2 ↔
    length ds1 = length ds2 ∧
    ∀ k, sum (take k ds1) ≤ slack + sum (take k ds2).
  Proof.
    intuition eauto using subdebits_alternate_characterization_1,
      subdebits_alternate_characterization_2, subdebits_length.
  Qed.

  Lemma subdebits_reflexive ds :
    ∀ slack,
    subdebits slack ds ds.
  Proof.
    induction ds; simpl; eauto with lia.
  Qed.

  Lemma subdebits_covariant_in_slack :
    ∀ ds1 ds2 slack1 slack2,
    subdebits slack1 ds1 ds2 →
    slack1 ≤ slack2 →
    subdebits slack2 ds1 ds2.
  Proof.
    induction ds1; destruct ds2; simpl;
    intuition eauto with lia.
  Qed.

  Lemma subdebits_transitive :
    ∀ ds1 ds2 ds3 slack1 slack2 slack,
    subdebits slack1 ds1 ds2 →
    subdebits slack2 ds2 ds3 →
    slack1 + slack2 ≤ slack →
    subdebits slack ds1 ds3.
  Proof.
    induction ds1; destruct ds2; destruct ds3; simpl;
    intuition eauto with lia.
  Qed.

  Local Lemma transport_list_eq_nil ds1 ds2 :
    length ds1 = length ds2 →
    ds1 = [] →
    ds2 = [].
  Proof.
    destruct ds1; destruct ds2; simpl; congruence.
  Qed.

  Local Lemma isStreamCell_nil g c ds1 ds2 :
    length ds1 = length ds2 →
    isStreamCell g c ds1 [] -∗
    isStreamCell g c ds2 [].
  Proof.
    unfold isStreamCell.
    iIntros (?) "(%Hc & %Hds1)".
    eauto using transport_list_eq_nil.
  Qed.

  Local Ltac mv H' H :=
    iClear H; iRename H' into H.

  Local Lemma stream_cell_forward_debt_aux slack g c ds1 ds2 xs E :
    length ds1 = length ds2 →
    (
      ∀ xs g t,
      isStream g t ds1 xs -∗ TC slack ={E}=∗ isStream g t ds2 xs
    ) →
    isStreamCell g c ds1 xs -∗
    TC slack ={E}=∗
    □ isStreamCell g c ds2 xs.
  Proof.
    intros Hlen IH.
    iIntros "#Hc Hslack".
    destruct xs as [| x xs ].
    (* Case: the list is empty. *)
    { iModIntro.
      iApply (isStreamCell_nil with "Hc").
      eauto. }
    (* Case: the list is nonempty. *)
    { deconstruct_stream_cell.
      (* Exploit the induction hypothesis. *)
      iMod (IH with "Hstream Hslack") as "#Hstream'"; iModIntro.
      construct_stream_cell. }
  Qed.

  Lemma stream_forward_debt :
    ∀ ds1 ds2 slack xs g t E,
    subdebits slack ds1 ds2 →
    ↑ThunkPayment t ⊆ E →
    isStream g t ds1 xs -∗
    TC slack ={E}=∗
    isStream g t ds2 xs.
  Proof.
    induction ds1 as [| d1 ds1 ]; destruct ds2 as [| d2 ds2 ];
    simpl subdebits;
    try rewrite unfold_isStream_contradictory;
    try solve [ tauto | eauto 3 ].
    intros slack xs g t E (? & Hsub) ?.
    iIntros "#Hstream Hslack".
    do 2 unfold_isStream.
    iDestruct "Hstream" as "(%Hlength & #Hthunk)".
    assert (length ds1 = length ds2) by eauto using subdebits_length.
    iAssert (⌜ length ds2 = length xs ⌝)%I as "Hll".
    { iPureIntro. congruence. }
    iFrame "Hll". iClear "Hll".
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
      iMod (Gthunk_consequence with "[Hslack] Hthunk") as "$"; last done.
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
      iMod (Gthunk_pay with "Hpayment Hthunk") as "Hthunk'"; first assumption.
      mv "Hthunk'" "Hthunk".
      rewrite (_ : d1 - (d1 - d2) = d2); last lia.
      (* The front thunk now has the desired debt. *)
      (* We must now apply the consequence rule in order to adjust the
         postcondition of the front thunk. *)
      rewrite {3} (_ : d2 = d2 + 0); last lia.
      iMod (Gthunk_consequence with "[Hslack] Hthunk") as "$"; last done.
      (* In this case, we do not get more slack. *)
      iIntros (c) "_ #Hc".
      (* We now have to reason about the stream cell. *)
      (* The result follows from the previous lemma and
         from the induction hypothesis. *)
      iMod (stream_cell_forward_debt_aux with "Hc Hslack") as "$"; eauto 2.
    }

  Qed.

  Lemma stream_cell_forward_debt slack g c ds1 ds2 xs E :
    subdebits slack ds1 ds2 →
    (∀ t, ↑ThunkPayment t ⊆ E) →
    isStreamCell g c ds1 xs -∗
    TC slack ={E}=∗
    isStreamCell g c ds2 xs.
  Proof.
    iIntros (Hsub Hmask) "#Hc Hslack".
    iMod (stream_cell_forward_debt_aux with "Hc Hslack") as "#$"; last done.
    { eauto using subdebits_length. }
    { eauto using stream_forward_debt. }
  Qed.

  Local Ltac note_length_equality H :=
    first [
      iPoseProof (isStreamCell_length with H) as "%"
    | iPoseProof (isStream_length with H) as "%"
    ].

  Local Ltac construct_stream H :=
    unfold_isStream; pure_conjunct; iFrame H.

  Local Ltac construct_action :=
    iIntros "Htoken Htc" (ψ) "Post".

  (* The tick translation of [lazy e] involves two ticks. *)

  Lemma translate_lazy_expr e :
    « lazy e » = tick « create » (tick (Lam <> «e»)).
  Proof.
    reflexivity.
  Qed.

  Lemma translate_lazy_val c :
    « lazy c » = tick «create»%V (tick (Lam <> « c »%V)).
  Proof.
    reflexivity.
  Qed.

  (* Evaluating [lazy e], where the expression [e] consumes [k] time credits
     and must produce a stream cell, costs 5 credits now and returns a stream
     whose front cell has k debits. *)

  (* We could prove a slightly more precise spec, stating that the cost is
     4 credits now and that the front cell has [k+1] debits. The simpler
     specification seems preferable and is just as useful in practice. *)

  (* The expression [e] receives the token [token (g-1)] and must return it.
     Thus, it is allowed earlier to force thunks in previous generations, but
     not thunks in the same generation as itself or in newer generations. *)

  Definition isLazyCell k g ds xs e : iProp :=
    TC k -∗ token (g-1) -∗
    ∀ ψ, (∀ c, isStreamCell g c ds xs -∗ token (g-1) -∗ ψ «c»%V) -∗
    WP «e» {{ ψ }}.

  Lemma lazy_spec g e ds xs k :
    g > 0 →
    length ds = length xs →
    TC_invariant -∗
    {{{ TC 5 ∗ isLazyCell k g ds xs e }}}
      « lazy e »
    {{{ t, RET #t ; isStream g t (k :: ds) xs }}}.
  Proof.
    iIntros (Hg Hlen).
    construct_texan_triple "(Htc & He)".
    (* The tick translation of [lazy e] involves two ticks. *)
    rewrite translate_lazy_expr.
    (* We pay one credit for the second tick, which is executed first. *)
    wp_tick_closure.
    (* Then, we recognize an application of [create]. *)
    untranslate.
    (* We pay 3 credits for [create], and keep one credit. *)
    iDestruct "Htc" as "(H1 & H3)".
    wp_apply (create_spec with "[$] [$H3 H1 He]"); last first.
    { iIntros (t) "#Hthunk". iApply "Post". construct_stream "Hthunk". }
    (* We now examine the cost of this action. *)
    construct_action.
    (* We have wisely stored one credit, which pays for the call to the
       constant function that returns [c]. *)
    wp_tick_lam. iClear "H1".
    (* There remain [k] credits, which allow executing [e]. *)
    (* We have the required token. *)
    rewrite   [in Some _] (_ : g = (g - 1) + 1)%nat; last lia.
    iApply ("He" with "Htc Htoken").
    rewrite - [in Some _] (_ : g = (g - 1) + 1)%nat; last lia.
    iIntros (c) "#Hc Htoken".
    iApply ("Post" with "Htoken"). iFrame "Hc".
  Qed.

  Lemma lazy_val_spec g c ds xs :
    length ds = length xs →
    isStreamCell g c ds xs -∗
    TC_invariant -∗
    {{{ TC 5 }}}
      « lazy c »
    {{{ t, RET #t ; isStream g t (0 :: ds) xs }}}.
  Proof.
    iIntros (Hlen) "#Hc".
    construct_texan_triple "Htc".
    (* The tick translation of [lazy e] involves two ticks. *)
    rewrite translate_lazy_expr.
    (* We pay one credit for the second tick, which is executed first. *)
    wp_tick_closure.
    (* Then, we recognize an application of [create]. *)
    untranslate.
    (* We pay 3 credits for [create], and keep one credit. *)
    iDestruct "Htc" as "(H1 & H3)".
    wp_apply (create_spec with "[$] [$H3 H1]"); last first.
    { iIntros (t) "#Hthunk". iApply "Post". construct_stream "Hthunk". }
    (* We now examine the cost of this action. *)
    construct_action.
    (* We have wisely stored one credit, which pays for the call to the
       constant function that returns [c]. *)
    wp_tick_lam.
    (* Done. *)
    iApply ("Post" with "Htoken"). iFrame "Hc".
  Qed.

  Lemma NIL_spec g :
    TC_invariant -∗
    {{{ TC 1 }}} « NIL » {{{ c, RET « c »; isStreamCell g c [] [] }}}.
  Proof.
    construct_texan_triple "Htc".
    wp_tick_inj.
    rewrite untranslate_litv. untranslate.
    iApply "Post".
    eauto.
  Qed.

  Lemma CONS_spec g t ds x xs :
    isStream g t ds xs -∗
    TC_invariant -∗
    {{{ TC 2 }}}
      « CONS x #t »
    {{{ c, RET « c »; isStreamCell g c ds (x :: xs) }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "Htc".
    (* TODO These back and forth translations are really painful: *)
    rewrite -untranslate_injr -untranslate_pair.
    wp_tick_pair.
    wp_tick_inj.
    rewrite untranslate_litv. untranslate.
    iApply "Post".
    construct_stream_cell.
  Qed.

  Lemma nil_spec g :
    g > 0 →
    TC_invariant -∗
    {{{ TC 6 }}}
      « nil »
    {{{ t, RET #t ; isStream g t (0 :: []) [] }}}.
  Proof.
    intros Hg.
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

  Lemma cons_spec g t ds x xs :
    g > 0 →
    isStream g t ds xs -∗
    TC_invariant -∗
    {{{ TC 8 }}}
      « cons x #t »
    {{{ t', RET #t' ; isStream g t' (2 :: ds) (x :: xs) }}}.
  Proof.
    intros Hg.
    iIntros "#Hstream".
    construct_texan_triple "Htc".
    note_length_equality "Hstream".
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
    { eauto. }
    { eauto. }
  Qed.

  Lemma extract_spec g t ds x xs :
    isStream g t (0 :: ds) (x :: xs) -∗
    TC_invariant -∗
    {{{ TC 22 ∗ token g }}}
      « extract #t »
    {{{ g' t', RET («x», #t');
        (* ⌜g' ≤ g⌝ TODO *)
        isStream g' t' ds xs ∗ token g }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "(Htc & Htoken)".
    wp_tick_lam.
    (* Force the stream [t]. *)
    pay_out_of "Htc".
    wp_apply (stream_force with "[#] [$] [$Htc' $Htoken]"); [ done |].
    2: lia.
    iClear "Hstream".
    iIntros (c) "(_ & #Hc & Htoken)".
    deconstruct_stream_cell.
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

  Lemma rev_append_spec_aux g :
    ∀ xs c ds ys ,
    isStreamCell g c ds ys -∗
    TC_invariant -∗
    {{{ TC (6 + 19 * length xs) }}}
      « rev_append (ListV xs) c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
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
      note_length_equality "Hc".
      rewrite (_ : 6 + 19 * length (_ :: xs) = (6 + 19 * length xs) + 19);
        last (cbn; lia).
      iDestruct "Htc" as "[Hrest Htc]".
      (* Step. *)
      wp_tick_lam. wp_tick_let. wp_tick_match.
      do 2 (wp_tick_proj ; wp_tick_let).
      push_subst.
      (* The next redex is [lazy c]. *)
      pay_out_of "Htc".
      wp_apply (lazy_val_spec with "[$Hc] [$] [$Htc']").
      { eassumption. }
      2: lia.
      (* Continue stepping. *)
      iIntros (t) "#Hthunk".
      wp_tick_pair. wp_tick_inj.
      rewrite untranslate_litv. untranslate.
      wp_apply (IHxs _ (0 :: ds) (x :: ys) with "[] [$] [$Hrest]").
      { construct_stream_cell. }
      { iIntros (c') "#Hc'". iApply "Post".
        by rewrite /= app_comm_cons repeat_cons -assoc -assoc /=. }
    }
  Qed.

  Lemma rev_append_spec g l xs c ds ys :
    isList l xs -∗
    isStreamCell g c ds ys -∗
    TC_invariant -∗
    {{{ TC (6 + 19 * length xs) }}}
      « rev_append l c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    iIntros "%Hxs #Hc". subst.
    construct_texan_triple "Htc".
    wp_apply (rev_append_spec_aux with "[$] [$] [$]").
    eauto.
  Qed.

  Lemma NILV_spec g :
    ⊢ isStreamCell g NILV [] [].
  Proof.
    iIntros. simpl. eauto.
  Qed.

  Lemma rev_spec g l xs ds ys :
    g > 0 →
    isList l xs -∗
    TC_invariant -∗
    {{{ TC (13 + 19 * length xs) }}}
      « rev l »
    {{{ t, RET «#t» ;
        isStream g t (repeat 0 (1 + length xs)) (List.rev xs) }}}.
  Proof.
    intros Hg.
    simpl repeat.
    iIntros "#Hl".
    construct_texan_triple "Htc".
    (* We pay 1 credit here. *)
    wp_tick_lam. push_subst.
    (* [lazy (...)] costs 5 credits. *)
    pay_out_of "Htc".
    wp_apply (lazy_spec with "[$] [$Htc' Htc]"); last first.
    { iIntros (t) "Hstream".
      iApply "Post". iFrame "Hstream". }
    (* Side conditions. *)
    2: rewrite repeat_length rev_length //.
    2: exact Hg.
    2: lia.
    (* Examine the body of this suspension. *)
    rewrite /isLazyCell.
    iIntros "_ Htoken" (ψ) "Post".
    (* Evaluate NIL, consuming 1 credit. *)
    wp_tick_inj.
    (* The call [rev_append l NILV] consumes the remaining credits. *)
    rewrite untranslate_litv. untranslate.
    wp_apply (rev_append_spec with "[$Hl] [] [$] [$Htc]").
    { iApply NILV_spec. }
    rewrite !app_nil_r.
    iIntros (c') "Hc'".
    iApply ("Post" with "Hc' Htoken").
  Qed.

  Definition A := 11.
  Definition B := 11.
  Opaque A. Opaque B.

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

(* TODO
  Definition debit_append ds1 ds2 :=
    let ds1 := map (λ d, A + d) ds1 in
    match List.rev ds1, ds2 with
    | [], _
    | _, [] =>
        (* This cannot happen. The two lists must be nonempty. *)
        ds1 ++ ds2
    | d1 :: ds1, d2 :: ds2 =>
        List.rev ds1 ++ [d1 + B + d2] ++ ds2
    end.
 *)

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

  Lemma append_spec g t1 t2 ds1 ds2 xs1 xs2 :
    isStream g t1 ds1 xs1 -∗
    isStream g t2 ds2 xs2 -∗
    TC_invariant -∗
    {{{ TC 8 }}}
      « append #t1 #t2 »
    {{{ t, RET «#t» ;
        isStream (g + 1) t (debit_append ds1 ds2) (xs1 ++ xs2) }}}.
  Proof.
    (* First, extract length information. *)
    iIntros "#Hstream1 #Hstream2".
    note_length_equality "Hstream1".
    note_length_equality "Hstream2".
    assert (Hlen1: length ds1 > 0) by lia.
    (* Move the hypotheses back into the goal. *)
    iStopProof.
    repeat match goal with h: length _ = _ |- _ => revert h end.
    revert ds2 t1 t2 g xs1 xs2.
    (* Reason by induction on [ds1]. *)
    pattern ds1.
    eapply debits_induction; [| | exact Hlen1 ]; clear ds1 Hlen1.

    (* Case: [ds1] is a singleton list. *)
    {
      intros d1 ds2 t1 t2 g xs1 xs2.
      intros Hlen1 Hlen2.
      (* The list [xs1] must be empty. *)
      assert (xs1 = []); [| subst xs1; clear Hlen1 ].
      { destruct xs1; [ eauto |]. simpl in Hlen1. lia. }
      rewrite app_nil_l.
      (* The list [ds2] must be nonempty; rename it [d2 :: ds2]. *)
      destruct ds2 as [| d2 ds2 ]; [ simpl in Hlen2; lia |].
      assert (Hlen: length ds2 = length xs2);
        [ simpl in Hlen2; lia | clear Hlen2 ].
      rename Hlen into Hlen2.
      (* We are in business. *)
      iIntros "(#Hstream1 & #Hstream2)".
      construct_texan_triple "Htc".
      (* Step. We pay 3 credits here. *)
      wp_tick_lam. wp_tick_let. push_subst.
      (* [lazy (...)] costs 5 credits. *)
      pay_out_of "Htc".
      wp_apply (lazy_spec with "[$] [$Htc']"); last first.
      { iIntros (t) "Hstream". iApply "Post". iFrame "Hstream". }
      2: eauto.
      2: lia.
      2: lia.
      clear cost.
      (* Now, examine the body of the suspension. *)
      rewrite /isLazyCell.
      rewrite (_ : g + 1 - 1 = g); last lia.
      iIntros "Htc Htoken" (ψ) "Post".
      (* The code forces [t1], enters the first branch, then forces [t2]. *)
      (* TODO The goal does have the desired shape, namely
              « force #t1 » in an evaluation context,
              but the tactic wp_apply does not recognize this. *)
      rewrite translate_case.
      pay_out_of "Htc".
      wp_apply (stream_force with "[#] [$] [$Htc' $Htoken]").
      admit.
    }

    (* Case: [ds1] is not a singleton list. *)
    {
      intros d1 ds1 ? IH ds2 t1 t2 g xs1 xs2.
      intros Hlen1 Hlen2.
      (* The list [xs1] must be nonempty: rename it [x1 :: xs1]. *)
      destruct xs1 as [| x1 xs1 ]; [ simpl in Hlen1; lia |].
      (* Simplify some hypotheses. *)
      assert (Hlen: length ds1 = 1 + length xs1);
        [ simpl in Hlen1; lia |
          clear Hlen1; rename Hlen into Hlen1 ].
      (* The list [ds2] must be nonempty; rename it [d2 :: ds2]. *)
      destruct ds2 as [| d2 ds2 ]; [ simpl in Hlen2; lia |].
      assert (Hlen: length ds2 = length xs2);
        [ simpl in Hlen2; lia | clear Hlen2 ].
      rename Hlen into Hlen2.
      (* Simplify the goal. *)
      rewrite debit_append_step; last eassumption.
      (* We are in business. *)
      iIntros "(#Hstream1 & #Hstream2)".
      construct_texan_triple "Htc".
      (* Step. We pay 3 credits here. *)
      wp_tick_lam. wp_tick_let. push_subst.
      (* [lazy (...)] costs 5 credits. *)
      pay_out_of "Htc".
      wp_apply (lazy_spec with "[$] [$Htc']"); last first.
      { iIntros (t) "Hstream". iApply "Post". iFrame "Hstream". }
      2: simpl; rewrite length_debit_append ?app_length; lia.
      2: lia.
      2: lia.
      clear cost.
      (* Now, examine the body of the suspension. *)
      rewrite /isLazyCell.
      rewrite (_ : g + 1 - 1 = g); last lia.
      iIntros "Htc Htoken" (ψ) "Post".

  Abort.

  (* TODO create a layer where the parameter [g] disappears, if possible *)
  (* what about the parameter [p]? *)
  Definition isStream' t ds xs : iProp :=
    ∃ g, isStream g t ds xs.

End StreamProofs.

End Stream.
