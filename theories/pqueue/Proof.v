From stdpp Require Import list.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import TimeCredits Thunks Auth_max_nat.
From iris_time.pqueue Require Import Code.

Fixpoint list_val (l : list val) : val :=
  match l with
  | nil => #()
  | x :: l' => (x, list_val l')
  end.

Definition ns (n : nat) : namespace :=
  nroot .@ "pqueue" .@ n.

Fixpoint nset (n : nat) : coPset :=
  match n with
  | 0 => ∅
  | S n' => nset n' ∪ ↑(ns n')
  end.

Lemma ns_nset_disj n n' :
  n ≤ n' →
  ↑ns n' ## nset n.
Proof.
  revert n'; induction n; cbn; intros n'.
  - set_solver.
  - intros Hn'. rewrite disjoint_union_r. split.
    + eapply IHn. lia.
    + unfold ns. assert (n ≠ n') by lia. solve_ndisj.
Qed.

Section PQueue.

Notation valO := (valO heap_lang).
Context `{!timeCreditHeapG Σ}.
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γ *)
Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{na_invG Σ}.

Context (p : na_inv_pool_name).

Lemma rev_aux_spec (l l' : list val) :
  TC_invariant -∗
  {{{ TC (5 + 8 * length l) }}}
    «rev_aux (list_val l) (list_val l')»
  {{{ l'', RET «l''»; ⌜l'' = list_val (reverse l ++ l')⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ".
  iInduction l as [|x l] "IH" forall (l').
  { rewrite /=. wp_tick_rec. wp_tick_let. wp_tick_op.
    wp_tick_if. by iApply "HΦ". }
  { replace (5 + 8 * length (x :: l))%nat
       with (8 + (5 + 8 * length l))%nat by (cbn; lia).
    wp_tick_rec. wp_tick_let. wp_tick_op. wp_tick_if.
    wp_tick_proj. wp_tick_pair. wp_tick_proj.
    iApply ("IH" $! (x :: l') with "TC").
    iIntros "!>" (l'' ->). iApply "HΦ". iPureIntro.
    f_equal. rewrite reverse_cons cons_middle app_assoc //. }
Qed.

Lemma rev_spec (l : list val) :
  TC_invariant -∗
  {{{ TC (6 + 8 * length l) }}}
    «rev (list_val l)»
  {{{ l', RET «l'»; ⌜l' = list_val (reverse l)⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ". wp_tick_rec.
  iApply (rev_aux_spec l [] with "[//] [$TC]").
  iIntros "!>" (l'' ->). rewrite app_nil_r. by iApply "HΦ".
Qed.

Lemma append_spec (l1 l2 : list val) :
  TC_invariant -∗
  {{{ TC (5 + 8 * length l1) }}}
    «append (list_val l1) (list_val l2)»
  {{{ l', RET «l'»; ⌜l' = list_val (l1 ++ l2)⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ".
  iInduction l1 as [|x l1] "IH" forall (Φ).
  { rewrite /=. wp_tick_rec. wp_tick_let. wp_tick_op. wp_tick_if.
    by iApply "HΦ". }
  { replace (5 + 8 * length (x :: l1))%nat
       with (8 + (5 + 8 * length l1))%nat by (cbn; lia).
    wp_tick_rec. wp_tick_let. wp_tick_op. wp_tick_if.
    wp_tick_proj.
    rewrite (_: (S (S (5 + 8 * length l1)))
                = 2 + (5 + 8 * length l1))%nat; [|lia].
    iDestruct "TC" as "[TC1 TC2]".
    wp_apply ("IH" with "TC2"). iIntros (l' ->).
    wp_tick_proj. wp_tick_pair.
    iSpecialize ("HΦ" $! (x, list_val (l1 ++ l2))%V).
    by iApply "HΦ". }
Qed.

Definition thunk_debt (w fl rl : list val) : nat :=
  min (16 * length w) (8 * length fl - 8 * length rl).

Definition is_queue_raw
  (q : val)
  (l w fl rl : list val) : iProp Σ
:=
  ∃ (t : loc) (lenf lenr : nat) (γ : gname) (ns_id : nat),
    ⌜q = (list_val w, #lenf, #t, #lenr, list_val rl)%V
     ∧ lenf = length fl
     ∧ lenr = length rl
     ∧ l = fl ++ reverse rl
     ∧ w `prefix_of` fl⌝ ∗
    Thunk p (ns ns_id) γ t
          (thunk_debt w fl rl)
          (na_own p (nset ns_id))
          (λ fv, ⌜fv = list_val fl⌝).

Definition is_queue (q : val) (l : list val) : iProp Σ :=
  ∃ (w : list val) (fl rl: list val),
    is_queue_raw q l w fl rl ∗
    ⌜length rl ≤ length fl⌝ ∗
    ⌜(w = [] → fl = [])⌝.

Instance is_queue_persistent l q :
  Persistent (is_queue l q).
Proof using. exact _. Qed.

Lemma empty_spec :
  TC_invariant -∗
  {{{ TC 10 }}}
    «empty #()»
  {{{ q, RET «q»; is_queue q nil }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ".
  wp_tick_lam. wp_tick_closure.
  rewrite (_: 8 = 4 + 4) //. iDestruct "TC" as "[TC1 TC]".
  iDestruct "TC1" as "[TC11 TC12]".
  iPoseProof (create_spec _ (ns 0) (thunk_debt nil nil nil)
                          (na_own p (nset 0))
                          (λ flv', ⌜flv' = list_val nil⌝)%I
                          (λ: <>, list_val nil)%V
             with "[//] [$TC12 TC11]") as "S".
  { iIntros "TC Hna" (ψ) "Hψ". wp_tick_lam.
    by iApply ("Hψ" $! #()%V with "Hna"). }
  rewrite -lock. (* XXX *) wp_apply "S". iIntros (γ t) "HT".
  repeat wp_tick_pair. iApply ("HΦ" $! (#(), #0, #t, #0, #())%V).
  iExists _, _, _. iSplit.
  { iExists _, 0, 0, _, 0. iFrame "HT". iPureIntro. by repeat split. }
  done.
Qed.

(* [checkw (w, lenf, f, lenr, r)] restores the invariant that [w] is empty only
   if [f] is empty. *)
Lemma checkw_spec q l w fl rl :
  TC_invariant -∗
  {{{ is_queue_raw q l w fl rl ∗ TC 44 ∗ na_own p ⊤ }}}
    «checkw q»
  {{{ q' w', RET «q'»;
      is_queue_raw q' l w' fl rl ∗ na_own p ⊤
      ∗ ⌜w' = [] → fl = []⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Hna) HΦ".
  iDestruct "Hq" as (t ? ? ? ns_id) "[(-> & -> & -> & -> & %) HT]".
  wp_tick_lam.
  repeat (wp_tick_let; repeat wp_tick_proj).
  destruct w as [|? w'] eqn:Hw.
  { wp_tick_op. wp_tick_if.
    rewrite (_: 15 = 11 + 4) //. iDestruct "TC" as "[TC1 TC]".
    assert ((⊤:coPset) = nset ns_id ∪ (⊤ ∖ nset ns_id)) as Hsplit_top.
    { apply union_difference_L. set_solver. }
    rewrite {1}Hsplit_top. iDestruct (na_own_union with "Hna") as "[HnaT Hna]".
    { set_solver. }
    wp_apply (force_spec with "[//] [$HT $Hna $TC1 $HnaT]").
    { apply subseteq_difference_r. 2: set_solver. by apply ns_nset_disj. }
    iIntros (fv) "(TV & -> & Hna & HnaT)". repeat wp_tick_pair.
    iApply ("HΦ" $! (list_val fl, #(length fl), #t, #(length rl), list_val rl)%V fl).
    iDestruct (na_own_union with "[$HnaT $Hna]") as "Hna". set_solver.
    rewrite -Hsplit_top. iFrame "Hna". iSplit.
    { iExists _, _, _, _, _. iSplit; [done|]. iApply (Thunk_weaken with "HT").
      unfold thunk_debt; lia. }
    done. }
  { wp_tick_op. wp_tick_if. repeat wp_tick_pair.
    iApply ("HΦ" $! (list_val (v::w'), #(length fl), #t, #(length rl), list_val rl)%V w).
    iFrame "Hna". iSplit.
    { iExists _, _, _, _, _. rewrite -Hw. iSplit; [subst w; done|].
      iApply (Thunk_weaken with "HT"). lia. }
    { iPureIntro. intros ->; inversion Hw. } }
Qed.

(* [check (w, lenf, f, lenr, r)] restores the two invariants required by [is_queue]:
   - that [w] is empty only if [f] is empty
   - that [lenr ≤ lenf] *)
Lemma check_spec q l w fl rl :
  length rl ≤ length fl + 1 →
  TC_invariant -∗
  {{{ is_queue_raw q l w fl rl ∗ TC 121 ∗ na_own p ⊤ }}}
    «check q»
  {{{ q' w' fl' rl', RET «q'»;
      is_queue_raw q' l w' fl' rl'
      ∗ ⌜length rl' ≤ length fl'⌝
      ∗ ⌜w' = [] → fl' = []⌝
      ∗ na_own p ⊤ }}}.
Proof using.
  intros Hlen. iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Hna) HΦ".
  iDestruct "Hq" as (t ? ? ? ns_id) "[(-> & -> & -> & -> & %) HT]".
  wp_tick_lam.
  repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_op.
  destruct (decide (length rl ≤ length fl)) as [Hle|Hgt].
  { rewrite bool_decide_eq_true_2; [| lia]. wp_tick_if.
    rewrite (_: 92 = 44 + 48) //. iDestruct "TC" as "[TC1 TC]".
    wp_apply (checkw_spec (list_val w, #(length fl), #t, #(length rl), list_val rl)%V
               with "[//] [$TC1 $Hna]").
    { iExists _, _, _, _, _. iSplit. done. iFrame "HT". }
    iIntros (q' w') "(Hq' & Hna & %)". iApply "HΦ". by iFrame. }
  { rewrite bool_decide_eq_false_2; [| lia]. wp_tick_if.
    rewrite (_: 92 = 11 + 81) //. iDestruct "TC" as "[TC1 TC]".
    rewrite (_: thunk_debt w fl rl = 0).
    2: { rewrite /thunk_debt (_: 8 * length fl - 8 * length rl = 0)%nat; lia. }
    assert ((⊤:coPset) = nset ns_id ∪ (⊤ ∖ nset ns_id)) as Hsplit_top.
    { apply union_difference_L. set_solver. }
    rewrite {1}Hsplit_top. iDestruct (na_own_union with "Hna") as "[HnaT Hna]".
    { set_solver. }
    wp_apply (force_spec with "[//] [$HT $Hna $TC1 $HnaT]").
    { apply subseteq_difference_r. 2: set_solver. by apply ns_nset_disj. }
    iIntros (flv) "(? & -> & Hna & HnaT)". wp_tick_let.
    wp_tick_closure.
    rewrite (_: 78 = 3 + 75) //. iDestruct "TC" as "[TC1 TC]".
    rewrite (_: 75 = S (5 + (6 + 8)) + 55) //. iDestruct "TC" as "[TC2 TC]".
    (* we can assign namespace id 0 to this thunk as it doesn't need to force
       other thunks. *)
    iPoseProof (create_spec _ (ns 0) (16 * length fl)
                            (na_own p (nset 0))
                            (λ flv', ⌜flv' = list_val (fl ++ reverse rl)⌝)%I
                            (λ: <>, append (list_val fl) (rev (list_val rl)))%V
               with "[//] [$TC1 TC2]") as "S".
    { iIntros "TC HnaT" (ψ) "Hψ". wp_tick_lam.
      rewrite (_: 16 * length fl = 8 * length fl + 8 * length fl); [|lia].
      iDestruct "TC" as "[TCa TCr]". iDestruct "TC2" as "[TC2 TCrc]".
      iCombine "TCrc TCr" as "TCr".
      wp_apply (rev_spec with "[//] [TCr]"). iApply (TC_weaken with "TCr"); lia.
      iIntros (rrl) "->".
      iCombine "TC2 TCa" as "TCa".
      wp_apply (append_spec with "[//] [$TCa]").
      iIntros (l') "->". by iApply ("Hψ" with "HnaT"). }
    rewrite -lock. (* XXX *) wp_apply "S".
    iIntros (? t') "#HT'". wp_tick_let. wp_tick_op. repeat wp_tick_pair.
    rewrite (_: 48 = 44 + 4) //. iDestruct "TC" as "[TC1 TC]".
    iDestruct (na_own_union with "[$HnaT $Hna]") as "Hna". set_solver. rewrite -Hsplit_top.
    wp_apply (checkw_spec (list_val fl, #(length fl + length rl), #t', #0, #())%V
                          (fl ++ reverse rl) fl (fl ++ reverse rl) nil
               with "[//] [$TC1 $Hna]").
    { iExists _, (length fl + length rl), 0, _, 0. iSplit. iPureIntro. split.
      - repeat f_equal. lia.
      - rewrite app_length reverse_length app_nil_r. repeat split. by apply prefix_app_r.
      - iApply (Thunk_weaken with "HT'"). rewrite /thunk_debt.
        rewrite app_length reverse_length Nat.sub_0_r. lia. }
    iIntros (q' w') "(Hq' & Hna & %)". iApply "HΦ". iFrame. iPureIntro; split; try done.
    rewrite app_length reverse_length /=. lia. }
Qed.

Lemma push_spec q l x :
  TC_invariant -∗
  {{{ is_queue q l ∗ TC 170 ∗ na_own p ⊤ }}}
    «push q x»
  {{{ q', RET «q'»; is_queue q' (l ++ [x]) ∗ na_own p ⊤ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Hna) HΦ".
  iDestruct "Hq" as (w fl rl) "(Hqr & % & %)".
  iDestruct "Hqr" as (t ? ? ? ns_id) "[(-> & -> & -> & -> & %) HT]".
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_pair. wp_tick_op. repeat wp_tick_pair.
  rewrite (_: 135 = 8 + 127) //. iDestruct "TC" as "[TC1 TC]".
  iDestruct (Thunk_pay with "TC1 HT") as ">#HT'". done.
  rewrite (_: 127 = 121 + 6) //. iDestruct "TC" as "[TC1 TC]".
  wp_apply (check_spec (list_val w, #(length fl), #t, #(length rl + 1), list_val (x::rl))%V
                       (fl ++ reverse rl ++ [x]) w fl (x :: rl)
            with "[//] [$TC1 $Hna]").
  { cbn; lia. }
  { iExists _, (length fl), (length rl + 1), _, _. iSplit. iPureIntro. split.
    - repeat f_equal. lia.
    - repeat split; auto. cbn; lia. rewrite reverse_cons //.
    - iApply (Thunk_weaken with "HT'"). cbn; lia. }
  iIntros (q' w' fl' rl') "(Hq' & % & % & Hna)". iApply "HΦ".
  iFrame "Hna". rewrite app_assoc //. iExists _, _, _. by iFrame "Hq'".
Qed.

Lemma pop_spec q l :
  TC_invariant -∗
  {{{ is_queue q l ∗ TC 250 ∗ na_own p ⊤ }}}
    «pop q»
  {{{ r, RET «r»;
      match l with
      | nil => ⌜r = NONEV⌝
      | x :: l' => ∃ q', ⌜r = SOMEV (x, q')%V⌝ ∗ is_queue q' l'
      end ∗
      na_own p ⊤ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Hna) HΦ".
  iDestruct "Hq" as (w fl rl) "(Hqr & %Hlen & %Hw)".
  iDestruct "Hqr" as (t ? ? ? ns_id) "[(-> & -> & -> & -> & %Hpref) HT]".
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  destruct w as [|x w'] eqn:Hweq.
  { wp_tick_op. wp_tick_if. wp_tick_inj.
    rewrite Hw // (nil_length_inv rl) //.
    2: { rewrite Hw // in Hlen. cbn in Hlen. lia. }
    cbn. iApply ("HΦ" $! (InjLV #())%V). by iFrame "Hna". }
  { destruct fl as [|y fl]. by apply prefix_nil_not in Hpref.
    pose proof (prefix_cons_inv_1 _ _ _ _ Hpref). subst y.
    apply prefix_cons_inv_2 in Hpref.
    wp_tick_op. wp_tick_if. do 2 (wp_tick_proj; wp_tick_let).
    wp_tick_closure.
    rewrite (_: 214 = 3 + 211) //. iDestruct "TC" as "[TC1 TC]".
    rewrite (_: 211 = 29 + 182) //. iDestruct "TC" as "[TC2 TC]".
    (* pick a new namespace id: we need to be able to force the thunk we are
       wrapping, and all the thunks it may then need to force. *)
    iPoseProof (create_spec _ (ns (S ns_id)) (thunk_debt w' fl rl)
                            (na_own p (nset (S ns_id)))
                            (λ flv, ⌜flv = list_val fl⌝)%I
                            (λ: <>, Snd (force #t))%V
               with "[//] [$TC1 TC2]") as "S".
    { iIntros "TC HnaT" (ψ) "Hψ". wp_tick_lam.
      rewrite (_: 28 = 12 + 16) //. iDestruct "TC2" as "[TC1 TC2]".
      iCombine "TC2 TC" as "TC".
      iDestruct (Thunk_pay _ _ _ _ _ _ (thunk_debt (x :: w') (x :: fl) rl)
                           with "[TC] HT") as ">#HTpaid". done.
      { iApply (TC_weaken with "TC"). rewrite /thunk_debt.
        rewrite !(_: ∀ x l, length (x :: l) = S (length l)); [|done..]. lia. }
      rewrite Nat.sub_diag.

      cbn [nset]. iDestruct (na_own_union with "HnaT") as "[HnaT Hna]".
      { symmetry; by apply ns_nset_disj. }

      iDestruct "TC1" as "[TC1 TC2]".
      wp_apply (force_spec with "[//] [$TC2 $HTpaid $Hna $HnaT]"). done.
      iIntros (flv) "(_ & -> & Hna & HnaT)". rewrite /=. wp_tick_proj.
      iApply ("Hψ" with "[Hna HnaT]"). iApply (na_own_union with "[$HnaT $Hna]").
      symmetry; by apply ns_nset_disj. done. }
    rewrite -lock. (* XXX *) wp_apply "S". iIntros (? t') "#HT'".
    wp_tick_let. wp_tick_op. repeat wp_tick_pair.
    rewrite (_: 175 = 121 + 54) //. iDestruct "TC" as "[TC1 TC]".
    wp_apply (check_spec (list_val w', #(S (length fl) - 1), #t', #(length rl), list_val rl)%V
                         (fl ++ reverse rl) w' fl rl
               with "[//] [$TC1 $Hna]").
    { cbn in Hlen; lia. }
    { iExists _, _, _, _, _. iSplit. iPureIntro. repeat split; auto.
      - repeat f_equal. lia.
      - iFrame "HT'". }
    iIntros (q' w'' fl' rl') "(Hq' & % & % & Hna)".
    wp_tick_let. wp_tick_pair. wp_tick_inj.
    cbn [app]. iApply ("HΦ" $! (InjRV (x, q')%V)). iFrame "Hna".
    iExists q'. iSplit; first done. iExists _, _, _. by iFrame. }
Qed.

End PQueue.
