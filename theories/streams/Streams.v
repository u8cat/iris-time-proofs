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

  Lemma untranslate_litv t :
    #t = «#t»%V.
  Proof. reflexivity. Qed.

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

  Local Ltac note_length_equality :=
    first [
      iPoseProof (isStreamCell_length with "Hc") as "%"
    | iPoseProof (isStream_length with "Hstream") as "%"
    ].

  Local Ltac construct_stream H :=
    unfold_isStream; pure_conjunct; iFrame H.

  Local Ltac construct_action :=
    iIntros "Htoken Htc" (ψ) "Post".

  (* Evaluating [lazy e], where the expression [e] consumes [k] time credits
     and must produce a stream cell, costs 4 credits now and returns a stream
     whose front cell has k+1 debits. *)

  Lemma lazy_spec g e ds xs k :
    length ds = length xs →
    {{{ TC k }}} «e» {{{ c, RET «c» ; isStreamCell g c ds xs }}} -∗
    TC_invariant -∗
    {{{ TC 4 }}}
      « lazy e »
    {{{ t, RET #t ; isStream g t ((1 + k) :: ds) xs }}}.
  Proof.
    iIntros (Hlen) "#He".
    construct_texan_triple "Htc".
    (* The tick translation of [lazy e] involves two ticks. *)
    rewrite (_ : « lazy e » = tick « create » (tick (Lam <> «e»)) );
      last reflexivity.
    (* We pay one credit for the second tick, which is executed first. *)
    wp_tick_closure.
    (* Then, we recognize an application of [create]. *)
    untranslate.
    (* We pay 3 credits for it. *)
    wp_apply (create_spec with "[$] [$Htc]"); last first.
    { iIntros (t) "#Hthunk". iApply "Post". construct_stream "Hthunk". }
    (* We now examine the cost of this action. *)
    construct_action.
    (* We pay one credit to call the constant function that returns [c]. *)
    wp_tick_lam.
    (* There remain [k] credits, which allow executing [e]. *)
    wp_apply ("He" with "Htc").
    iIntros (c) "#Hc".
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
    TC_invariant -∗
    {{{ TC 4 }}}
      « nil »
    {{{ t, RET #t ; isStream g t (2 :: []) [] }}}.
  Proof.
    construct_texan_triple "Htc".
    wp_apply (lazy_spec _ _ [] [] 1 with "[#] [$] [$Htc]"); eauto 2.
    iApply (NIL_spec with "[$]").
  Qed.

  Lemma cons_spec g t ds x xs :
    isStream g t ds xs -∗
    TC_invariant -∗
    {{{ TC 7 }}}
      « cons x #t »
    {{{ t', RET #t' ; isStream g t' (3 :: ds) (x :: xs) }}}.
  Proof.
    iIntros "#Hstream".
    construct_texan_triple "Htc".
    note_length_equality.
    wp_tick_lam. wp_tick_let.
    rewrite untranslate_litv. untranslate.
    (* TODO make this a lemma? *)
    rewrite (_ : tick « create » (tick (Lam <> « CONS x #t »)) =
                 « lazy (CONS x #t) » ); last reflexivity.
    wp_apply (lazy_spec with "[#] [$] [$Htc]"); last first.
    { iIntros (t') "Hstream'".
      iApply "Post". iFrame. }
    { iApply (CONS_spec with "[$] [$]"). }
    { eauto. }
  Qed.

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
      rewrite (_ : k = (k - cost) + cost); [
      unfold cost; clear Hcost; divide H | lia ]
      |]
    end.

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
    unfold_isStream. deconstruct_stream. (* TODO group? *)
    wp_tick_lam.
    (* Force the thunk [t]. *)
    pay_out_of "Htc".
    wp_apply (force_spec with "[$] [$Htc' $Hthunk $Htoken]").
    { eauto with thunks. }
    iIntros (c) "(_ & #Hc & Htoken)".
    deconstruct_stream_cell.
    (* Match on the resulting cell. The second branch must be taken. *)
    wp_tick_match. do 2 (wp_tick_proj ; wp_tick_let).
    (* Construct a pair. *)
    wp_tick_pair.
    (* Conclude. *)
    iApply "Post". iFrame "Htoken". eauto.
    (* Side conditions. *)
    lia.
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
    {{{ TC (6 + 28 * length xs) }}}
      « rev_append (ListV xs) c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    induction xs as [|x xs]; intros c ds ys;
    iIntros "#Hc";
    construct_texan_triple "Htc".

    (* Case: the list is empty. *)
    { wp_tick_lam. wp_tick_let. wp_tick_match. iApply "Post". iFrame "Hc". }

    (* Case: the list is nonempty. *)
    {
      note_length_equality.
      rewrite (_ : 6 + 28 * length (_ :: xs) = (6 + 28 * length xs) + 3 + 25);
        last (cbn; lia).
      iDestruct "Htc" as "[[Htc_ind Htc_create] Htc]".
      wp_tick_lam. wp_tick_let. wp_tick_match.
      do 2 (wp_tick_proj ; wp_tick_let).
      wp_tick_closure.
      rewrite (_ : tick «create»%V _  = « create (λ: <>, c)%V »);
        last by (unlock).
      iDestruct "Htc" as "[Htc_force Htc]".
      wp_apply (create_spec p g _
        (λ c, isStreamCell g c ds ys)
        with "[$] [$Htc_create Htc_force Hc]").
      { unfold isAction.
        iIntros "Htok _" (* TODO why do we drop credit? *) (Ψ) "HΨ".
        wp_tick_lam.
        iApply ("HΨ" with "Htok"). eauto. }
      {
        iIntros (t) "#Hthunk".
        wp_tick_pair. wp_tick_inj.
        rewrite untranslate_litv.
        untranslate.
        wp_apply (IHxs _ (0 :: ds) (x :: ys) with "[] [$] [$Htc_ind]").
        { iExists g, t. do 2 (iSplitR ; first done).
          rewrite unfold_isStream.
          iSplitR; eauto. }
        { iIntros (c') "#Hc'". iApply "Post".
          by rewrite /= app_comm_cons repeat_cons -assoc -assoc /=. }
      }
    }
  Qed.

  Lemma rev_append_spec g l xs c ds ys :
    TC_invariant -∗
    {{{ TC (6 + 28 * length xs) ∗ isList l xs ∗ isStreamCell g c ds ys }}}
      « rev_append l c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    iIntros "#?" (Φ) "!> (Htc & -> & #Hc) Post".
    wp_apply (rev_append_spec_aux with "[$] [$] [$]").
    eauto.
  Qed.

  (* TODO create a layer where the parameter [g] disappears, if possible *)
  (* what about the parameter [p]? *)
  Definition isStream' t ds xs : iProp :=
    ∃ g, isStream g t ds xs.

End StreamProofs.

End Stream.
