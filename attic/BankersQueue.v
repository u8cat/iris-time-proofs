From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits ThunksCode Thunks.
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

  Implicit Type t : loc.
  Implicit Type c l : val.
  Implicit Type x y z : val.
  Implicit Type xs ys zs : list val.
  Implicit Type d : nat.
  Implicit Type ds : list nat.
  Implicit Type g : nat.
  Implicit Type p : na_inv_pool_name.
  Implicit Type E F : coPset.

(*
  Fixpoint isStream t ds xs : iProp Σ :=
    match ds with
    | []       => False
    | d0 :: ds => ∃ p γv, Thunks.Thunk p t γv d0 emp (λ c, isStreamCell c ds xs)
    end%I
  with isStreamCell c xs ds :=
    match xs with
    | []      => ⌜c = NILV ∧ ds = []⌝
    | x :: xs => ∃ t, ⌜c = CONSV x #t⌝ ∗ isStream t ds xs
    end%I.
*)
(*
  Fixpoint isStream p E t ds xs : iProp Σ :=
    match ds, xs with
    | d::[], []    =>  ∃ γv F, ⌜F ⊆ E⌝ ∗ ⌜set_infinite (E ∖ F)⌝
                         ∗ Thunks.Thunk p t γv d (na_own p (E ∖ F)) (λ c,
                             ⌜c = NILV⌝)
    | d::ds, x::xs =>  ∃ γv F, ⌜F ⊆ E⌝ ∗ ⌜set_infinite (E ∖ F)⌝
                         ∗ Thunks.Thunk p t γv d (na_own p (E ∖ F)) (λ c,
                             ∃ t, ⌜c = CONSV x #t⌝ ∗ isStream p E t ds xs)
    | _,     _     =>  False
    end%I.
*)
(*
  Fixpoint isStream p E t ds xs : iProp Σ :=
    match ds, xs with
    | d::[], [] =>
                        ∃ γv F,
                            ⌜F ⊆ E⌝ ∗ ⌜set_infinite (E ∖ F)⌝
                          ∗ Thunks.Thunk p t γv d (na_own p (E ∖ F)) (λ c,
                              ⌜c = NILV⌝)
    | d::((_::_) as ds), x::xs =>
                        ∃ γv F,
                            ⌜F ⊆ E⌝ ∗ ⌜set_infinite (E ∖ F)⌝
                          ∗ Thunks.Thunk p t γv d (na_own p (E ∖ F)) (λ c,
                              ∃ t, ⌜c = CONSV x #t⌝ ∗ isStream p E t ds xs)
    | _, _ =>  False
    end%I.
*)

  Fixpoint streamGenN g :=
    match g with
    | 0    => nroot .@ "stream"
    | S g' => streamGenN g' .@ 1
    end.

  (* TODO: p variable de section *)
  (* TODO: utiliser la feature d’Iris pour associer un γ à une adresse physique
     cf gen_heap.v ("metadata")
     il faut adapter wp_alloc dans heap_lang/lifting.v pour qu’il ne jette plus le meta_token
     et adapter/étendre la tactique correspondante.

  Search meta_token.
  Search meta.
     isThunk_ t ... := ∃ γ, meta t ⊤ γ ∗ isThunk γ t ...
     isThunkVal idem
  *)
  (* TODO: API des thunks:
     - cacher le [γ] des thunks (nouvelle API)
     - prouver spec de [force] avec [ThunkVal] au lieu de [Thunk ∗ R]
     - prouver que [ThunkVal v1 ∗ ThunkVal v2 -∗ ⌜v1 = v2⌝ (trivial avec la def)
   *)

  Fixpoint isStream p g t ds xs : iProp Σ := (
    match ds with
    | []    =>  False
    | d::ds =>
        ∃ γt,
(*           ⌜length ds = length xs⌝ *)
          Thunks.Thunk p (streamGenN g .@ 0) γt t d (na_own p (⊤ ∖ ↑streamGenN g))
            (λ c,
              match xs with
              | []    =>           ⌜c = NILV⌝
              | x::xs =>  ∃ g' t', ⌜c = CONSV x #t'⌝ ∗ ⌜g' ≤ g⌝ ∗ isStream p g' t' ds xs
              end)
    end
  )%I.
(*
  Definition isStreamCell p E c ds xs :=
    match ds, xs with
    | [],           []    =>      ⌜c = NILV⌝
    | (_::_ as ds), x::xs => ∃ t, ⌜c = CONSV x #t⌝ ∗ isStream p E t ds xs
    | _,            _     => False
    end%I.
*)
  Definition isStreamCell p g c ds xs :=
    match xs with
    | []    =>          ⌜c = NILV (*∧ ds = []*)⌝
    | x::xs => ∃ g' t', ⌜c = CONSV x #t'⌝ ∗ ⌜g' ≤ g⌝ ∗ isStream p g' t' ds xs
    end%I.

  Lemma isStream_fold p g t ds xs :
    isStream p g t ds xs =
    (match ds with
    | []    =>  False
    | d::ds =>
        ∃ γt,
          Thunks.Thunk p (streamGenN g .@ 0) γt t d (na_own p (⊤ ∖ ↑streamGenN g))
            (λ c, isStreamCell p g c ds xs)
    end)%I.
  Proof. destruct ds ; reflexivity. Qed.

  Lemma isStream_fold' p g t d ds xs :
    isStream p g t (d::ds) xs =
    (∃ γt,
      Thunks.Thunk p (streamGenN g .@ 0) γt t d (na_own p (⊤ ∖ ↑streamGenN g))
        (λ c, isStreamCell p g c ds xs))%I.
  Proof. reflexivity. Qed.

  Global Instance isStream_persistent p g t ds xs :
    Persistent (isStream p g t ds xs).
  Proof.
    revert g ds ; induction xs ; destruct ds ; exact _.
  Qed.

  Global Instance isStreamCell_persistent p g c ds xs :
    Persistent (isStreamCell p g c ds xs).
  Proof.
    destruct xs ; exact _.
  Qed.

  Lemma isStream_lengths p g t ds xs :
    isStream p g t ds xs -∗ ⌜(length ds = 1 + length xs)%nat⌝.
  Abort.

  Definition isStream' p t ds xs : iProp Σ :=
    ∃ g, isStream p g t ds xs.

  Notation ThunkVal γt v := (own γt (Cinr $ to_agree v%V)).
  Notation coStreamGenN g := (⊤ ∖ ↑streamGenN g%nat).

  Lemma extract_spec p g t ds x xs :
    TC_invariant -∗
    {{{ TC 22 ∗ isStream p g t (0::ds) (x::xs) ∗ na_own p (coStreamGenN (g+1)) }}}
    « extract #t »
    {{{ g' t', RET («x», #t') ; (*⌜g' ≤ g⌝ ∗*) isStream p g' t' ds xs ∗ na_own p (coStreamGenN (g+1)) }}}.
  Proof.
    iIntros "#?" (Φ) "!> (Htc & Ht & Htok) Post".
    rewrite (_ : 22 = 11 + 11) ; last lia. iDestruct "Htc" as "[Htc_force ?]".
    simpl. iDestruct "Ht" as (γt) "Ht".
    wp_tick_lam.
    assert (    na_own p (coStreamGenN (g+1))
                 ⊣⊢ na_own p (coStreamGenN (g+1) ∖ coStreamGenN g)
                  ∗ na_own p (coStreamGenN g)
                  ∗ na_own p (↑(streamGenN g .@ 0)))
      as Eq.
      1:admit.
    setoid_rewrite Eq.
    iDestruct "Htok" as "(Htok_useless & Htok_tail & Htok_t)".
    wp_apply (Thunks.force_spec with "[$] [$Htc_force $Ht $Htok_t $Htok_tail]") ; first done.
    iIntros (c) "(_ & Hc & Htok_t & Htok_tail)" ; iDestruct "Hc" as (g' t') "(-> & #? & #?)".
    wp_tick_match. do 2 (wp_tick_proj ; wp_tick_let). wp_tick_pair.
    iApply "Post". by iFrame "#∗".
  Admitted.

  Lemma cons_spec p g t ds x xs :
    TC_invariant -∗
    {{{ TC 7 ∗ isStream p g t ds xs }}}
    « cons x #t »
    {{{ t2, RET #t2 ; isStream p g t2 (3::ds) (x::xs) }}}.
  Proof.
    iIntros "#?" (Φ) "!> [Htc #Ht] Post".
    rewrite [in TC 7](_ : 7 = 3 + 4) ; last lia. iDestruct "Htc" as "[Htc_create ?]".
    wp_tick_lam. wp_tick_let. wp_tick_closure.
    rewrite (_ : (tick «create»%V _) = « create (λ: <>, InjR (x, #t))%V ») ;
      last by unlock.
    wp_apply (Thunks.create_spec p with "[$] [$Htc_create Ht]") ; last first.
    { iIntros (γt2 t2) "Ht2". iApply "Post". simpl. by auto with iFrame. }
    { iIntros "? ?" (Ψ) "Post". wp_tick_lam. wp_tick_pair. wp_tick_inj.
      rewrite (_ : InjRV («x», #t) = « InjRV (x, #t) »%V) ; last done.
      iApply ("Post" with "[$]"). by auto 10 with iFrame. }
  Qed.

  Fixpoint ListV xs : val :=
    match xs with
    | []    =>  NILV
    | x::xs =>  CONSV x (ListV xs)
    end.
  Definition isList l xs : iProp Σ :=
    ⌜l = ListV xs⌝.

  Lemma rev_append_list_to_cell_spec p g l xs c ds ys :
    TC_invariant -∗
    {{{ TC (6 + 28 * length xs) ∗ isList l xs ∗ isStreamCell p g c ds ys }}}
    « rev_append_list_to_cell l c »
    {{{ c2, RET «c2» ; isStreamCell p g c2 (repeat 0 (length xs) ++ ds) (List.rev xs ++ ys) }}}.
  Proof.
    iIntros "#?" (Φ) "!> (Htc & -> & Hc) Post".
    iInduction (xs) as [|x xs] "IH" forall (c ds ys).
    { wp_tick_lam. wp_tick_let. wp_tick_match. by iApply "Post". }
    {
      rewrite (_ : 6 + 28 * length (_::xs) = (6 + 28 * length xs) + 3 + 25); last (cbn;lia).
      iDestruct "Htc" as "[[Htc_ind Htc_create] Htc]".
      wp_tick_lam. wp_tick_let. wp_tick_match. do 2 (wp_tick_proj ; wp_tick_let).
      wp_tick_closure.
      rewrite (_ : tick «create»%V _  = « create (λ: <>, c)%V ») ;
        last by unlock.
      iDestruct "Htc" as "[Htc_force Htc]".
      wp_apply (Thunks.create_spec p
        (streamGenN g .@ 0) (_) (na_own p (⊤ ∖ ↑streamGenN g))
        (λ c, isStreamCell p g c ds ys)
        with "[$] [$Htc_create Htc_force Hc]").
      { iIntros "_ Htok" (Ψ) "HΨ". wp_tick_lam.
        iApply ("HΨ" with "Htok"). by iDestruct "Hc" as "#$". }
      {
        iIntros (γt t) "Ht".
        wp_tick_pair. wp_tick_inj.
        rewrite (_ : InjRV («x», #t) = « InjRV (x, #t) »%V) ; last done.
        wp_apply ("IH" $! _ (0::ds) (x::ys) with "[$Htc_ind] [Ht]").
        { iExists g, t. do 2 (iSplitR ; first done). by iExists γt. }
        { iIntros (c2) "Hc2". iApply "Post". iClear "#".
          by rewrite /= app_comm_cons repeat_cons -assoc -assoc /=. }
      }
    }
  Qed.

End StreamProofs.

End Stream.
