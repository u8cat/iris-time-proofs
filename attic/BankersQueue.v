From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits ThunksCode ThunksBase Gthunks.
Open Scope nat_scope.

Section Stream.

Notation NIL := (InjL (LitV LitUnit)) (only parsing).
Notation CONS v vs := (InjR (v%V, vs%V)) (only parsing).
Notation NILV := (InjLV (LitV LitUnit)) (only parsing).
Notation CONSV v vs := (InjRV (v, vs)%V) (only parsing).
Notation "'match:' e0 'with' 'NIL' => e1 | 'CONS' ( x , xs ) => e2 'end'" :=
  (Match e0
    <>%bind (* => *) e1
    xs%bind (* => *) (Lam x%bind (Lam xs%bind e2%E (Snd xs%bind)) (Fst xs%bind))
                     (* this is let: x := Fst xs in let: xs := Snd xs in e2 *)
  )
  (e0, e1, x, xs, e2 at level 200, only parsing) : expr_scope.

Notation lazy e := (create (Lam <>%bind e))%E.

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
      NIL              => #()
    | CONS ("x", "xs") => ("x", "xs")
    end.

Definition rev_append_list_to_cell : val := (* : list → cell → cell *)
  rec: "rev_append" "xs" "ys" :=
    match: "xs" with
      NIL              => "ys"
    | CONS ("x", "xs") => "rev_append" "xs" (CONS "x" (lazy "ys"))
    end.

Definition rev : val := (* : list → stream *)
  λ: "xs",
    lazy (rev_append_list_to_cell "xs" NIL).

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

  Implicit Type t : loc.
  Implicit Type c l : val.
  Implicit Type x y z : val.
  Implicit Type xs ys zs : list val.
  Implicit Type d : nat.
  Implicit Type ds : list nat.
  Implicit Type g : nat.
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

  Lemma isStreamCell_length :
    ∀ ds xs g c,
    isStreamCell g c ds xs -∗
    ⌜(length ds = length xs)%nat⌝.
  Proof.
    destruct xs; intros; simpl.
    { iIntros "(_ & %Hds)". subst ds. eauto. }
    { iIntros "Hcell".
      iDestruct "Hcell" as (g' t') "(-> & %Hg'g & Hstream)". (* TODO share *)
      iApply isStream_length. eauto. }
  Qed.

  (* TODO rename *)
  Definition isStream' t ds xs : iProp :=
    ∃ g, isStream g t ds xs.

  Notation token g :=
    (own_gens_below_bound p (Some (g + 1))).

  Lemma cons_spec g t ds x xs :
    TC_invariant -∗
    {{{ TC 7 ∗ isStream g t ds xs }}}
      « cons x #t »
    {{{ t', RET #t' ; isStream g t' (3 :: ds) (x :: xs) }}}.
  Proof.
    iIntros "#?" (Φ) "!> [Htc #Hstream] Post".
    rewrite [in TC 7](_ : 7 = 3 + 4); last lia.
    iDestruct "Htc" as "[Htc_create ?]".
    wp_tick_lam. wp_tick_let. wp_tick_closure.
    rewrite untranslate_litv. untranslate.
    wp_apply (create_spec p g with "[$] [$Htc_create Hstream]") ; last first.
    { iIntros (t') "Htthunk'". iApply "Post". simpl.
      iSplitR.
      { iApply isStream_length. eauto. }
      { eauto. }
    }
    { iIntros "Htoken Htc" (Ψ) "Post".
      wp_tick_lam. wp_tick_pair. wp_tick_inj.
      rewrite untranslate_litv. untranslate.
      iApply ("Post" with "[$]"). auto 6 with iFrame. }
  Qed.

  Lemma extract_spec g t ds x xs :
    TC_invariant -∗
    {{{ TC 22 ∗ isStream g t (0 :: ds) (x :: xs) ∗ token g }}}
      « extract #t »
    {{{ g' t', RET («x», #t');
        (* ⌜g' ≤ g⌝ TODO *)
        isStream g' t' ds xs ∗ token g }}}.
  Proof.
    iIntros "#?" (Φ) "!> (Htc & Hstream & Htoken) Post".
    rewrite (_ : 22 = 11 + 11) ; last lia.
    iDestruct "Htc" as "[Htc_force ?]".
    unfold_isStream.
    deconstruct_stream.
    wp_tick_lam.
    wp_apply (force_spec with "[$] [$Htc_force $Hthunk $Htoken]").
    { eauto with thunks. }
    iIntros (c) "(_ & #Hc & Htoken)".
    iDestruct "Hc" as (g' t') "(-> & #Hg'g & #Hstream)".
    wp_tick_match. do 2 (wp_tick_proj ; wp_tick_let). wp_tick_pair.
    iApply "Post". iFrame "Htoken". eauto.
  Qed.

  Fixpoint ListV xs : val :=
    match xs with
    | []    =>  NILV
    | x::xs =>  CONSV x (ListV xs)
    end.

  Definition isList l xs : iProp :=
    ⌜l = ListV xs⌝.

  Lemma rev_append_list_to_cell_spec_aux g xs :
    ∀ c ds ys ,
    TC_invariant -∗
    isStreamCell g c ds ys -∗
    {{{ TC (6 + 28 * length xs) }}}
      « rev_append_list_to_cell (ListV xs) c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    induction xs as [|x xs]; intros c ds ys;
    iIntros "#? #Hc" (Φ) "!> Htc Post".

    (* Case: empty list. *)
    { wp_tick_lam. wp_tick_let. wp_tick_match. by iApply "Post". }

    (* Case: nonempty list. *)
    {
      iAssert (⌜ length ds = length ys ⌝)%I as "%Hlengths".
      { iApply isStreamCell_length. eauto. }

      rewrite (_ : 6 + 28 * length (_::xs) = (6 + 28 * length xs) + 3 + 25); last (cbn;lia).
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
        wp_apply (IHxs _ (0 :: ds) (x :: ys) with "[$] [] [$Htc_ind]").
        { iExists g, t. do 2 (iSplitR ; first done).
          rewrite unfold_isStream.
          iSplitR; eauto. }
        { iIntros (c') "#Hc'". iApply "Post".
          by rewrite /= app_comm_cons repeat_cons -assoc -assoc /=. }
      }
    }
  Qed.

  Lemma rev_append_list_to_cell_spec g l xs c ds ys :
    TC_invariant -∗
    {{{ TC (6 + 28 * length xs) ∗ isList l xs ∗ isStreamCell g c ds ys }}}
      « rev_append_list_to_cell l c »
    {{{ c', RET «c'» ;
        isStreamCell g c' (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    iIntros "#?" (Φ) "!> (Htc & -> & #Hc) Post".
    wp_apply (rev_append_list_to_cell_spec_aux with "[$] [$] [$]").
    eauto.
  Qed.

End StreamProofs.

End Stream.
