From stdpp Require Import list.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import TimeCredits.
From iris_time.thunks Require Import ThunksBase HThunks.
From iris_time.pqueue Require Import Code.

(* TODO can we reuse Streams.ListV? *)
Fixpoint list_val (l : list val) : val :=
  match l with
  | nil => #()
  | x :: l' => (x, list_val l')
  end.

Section PQueue.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).

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

Definition PSr := 6.
Definition PSR := 8.

Lemma stream_revl (l : list val) :
  TC_invariant -∗
  {{{ TC (PSr + PSR * length l) }}}
    «rev (list_val l)»
  {{{ l', RET «l'»; ⌜l' = list_val (reverse l)⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ". wp_tick_rec.
  iApply (rev_aux_spec l [] with "[//] [$TC]").
  iIntros "!>" (l'' ->). rewrite app_nil_r. by iApply "HΦ".
Qed.

#[global] Opaque PSr.
#[global] Opaque PSR.

Definition PSa := 5.
Definition PSA := 8.

Lemma stream_append (l1 l2 : list val) :
  TC_invariant -∗
  {{{ TC (PSa + PSA * length l1) }}}
    «append (list_val l1) (list_val l2)»
  {{{ l', RET «l'»; ⌜l' = list_val (l1 ++ l2)⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "TC HΦ".
  iInduction l1 as [|x l1] "IH" forall (Φ).
  { rewrite /=. wp_tick_rec. wp_tick_let. wp_tick_op. wp_tick_if.
    by iApply "HΦ". }
  { replace (PSa + PSA * length (x :: l1))%nat
       with (PSA + (PSa + PSA * length l1))%nat by (cbn; lia).
    wp_tick_rec. wp_tick_let. wp_tick_op. wp_tick_if.
    wp_tick_proj.
    rewrite (_: (S (S (PSa + PSA * length l1)))
                = 2 + (PSa + PSA * length l1))%nat; [|lia].
    iDestruct "TC" as "[TC1 TC2]".
    wp_apply ("IH" with "TC2"). iIntros (l' ->).
    wp_tick_proj. wp_tick_pair.
    iSpecialize ("HΦ" $! (x, list_val (l1 ++ l2))%V).
    by iApply "HΦ". }
Qed.

#[global] Opaque PSa.
#[global] Opaque PSA.

Definition K := PSA + PSR.

Definition thunk_debt (w fl rl : list val) : nat :=
  min (2 * K * length w) (K * length fl - K * length rl).

Definition is_queue_raw
  (q : val)
  (l w fl rl : list val) : iProp
:=
  ∃ (t : loc) (lenf lenr : nat) (id : height),
    ⌜q = (list_val w, #lenf, #t, #lenr, list_val rl)%V
     ∧ lenf = length fl
     ∧ lenr = length rl
     ∧ l = fl ++ reverse rl
     ∧ w `prefix_of` fl⌝ ∗
    HThunk p id t (thunk_debt w fl rl)
          (λ fv, ⌜fv = list_val fl⌝).

Definition is_queue (q : val) (l : list val) : iProp :=
  ∃ (w : list val) (fl rl: list val),
    is_queue_raw q l w fl rl ∗
    ⌜length rl ≤ length fl⌝ ∗
    ⌜(w = [] → fl = [])⌝.

Instance is_queue_persistent l q :
  Persistent (is_queue l q).
Proof using. exact _. Qed.

Definition Pe := 10.

Lemma empty_spec :
  TC_invariant -∗
  {{{ TC Pe }}}
    «empty #()»
  {{{ q, RET «q»; is_queue q nil }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "TC HΦ".
  wp_tick_lam. wp_tick_closure.
  rewrite (_: 8 = 4 + 4) //. iDestruct "TC" as "[TC1 TC]".
  iDestruct "TC1" as "[TC11 TC12]".
  iPoseProof (hthunk_create _ 0 (thunk_debt nil nil nil)
                          (λ flv', ⌜flv' = list_val nil⌝)%I
                          (λ: <>, list_val nil)%V
             with "[//] [$TC12 TC11]") as "S".
  { iIntros "Hna TC" (ψ) "Hψ". wp_tick_lam.
    by iApply ("Hψ" $! #()%V with "Hna"). }
  rewrite -lock. (* XXX *) wp_apply "S". iIntros (t) "HT".
  repeat wp_tick_pair. iApply ("HΦ" $! (#(), #0, #t, #0, #())%V).
  iExists _, _, _. iSplit.
  { iExists _, 0, 0, 0. iFrame "HT". iPureIntro. by repeat split. }
  done.
Qed.

#[global] Opaque Pe.

Definition Pchkw := 33 + Tf.

(* [checkw (w, lenf, f, lenr, r)] restores the invariant that [w] is empty only
   if [f] is empty. *)
Lemma checkw_spec q l w fl rl :
  TC_invariant -∗
  {{{ is_queue_raw q l w fl rl ∗ TC Pchkw ∗ HToken p None }}}
    «checkw q»
  {{{ q' w', RET «q'»;
      is_queue_raw q' l w' fl rl ∗ HToken p None
      ∗ ⌜w' = [] → fl = []⌝ }}}.
Proof using.
  iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Htok) HΦ".
  iDestruct "Hq" as (t ? ? h) "[(-> & -> & -> & -> & %) HT]".
  wp_tick_lam.
  repeat (wp_tick_let; repeat wp_tick_proj).
  destruct w as [|? w'] eqn:Hw.
  { wp_tick_op. wp_tick_if.
    divide_credit "TC" 4 Tf.
    wp_apply (hthunk_force with "[//] [$HT $Htok $TC']"). done.
    iIntros (fv) "(-> & TV & Htok)". repeat wp_tick_pair.
    iApply ("HΦ" $! (list_val fl, #(length fl), #t, #(length rl), list_val rl)%V fl).
    iFrame "Htok". iSplit.
    { iExists _, _, _, _. iSplit; [done|]. iApply (hthunk_increase_debt with "HT").
      unfold thunk_debt; lia. }
    done. }
  { wp_tick_op. wp_tick_if. repeat wp_tick_pair.
    iApply ("HΦ" $! (list_val (v::w'), #(length fl), #t, #(length rl), list_val rl)%V w).
    iFrame "Htok". iSplit.
    { iExists _, _, _, _. rewrite -Hw. iSplit; [subst w; done|].
      iApply (hthunk_increase_debt with "HT"). lia. }
    { iPureIntro. intros ->; inversion Hw. } }
Qed.

#[global] Opaque Pchkw.

Definition Pchk := 50 + (Tf + PSr + PSa + Tcr + K + PSR + Pchkw).

(* [check (w, lenf, f, lenr, r)] restores the two invariants required by [is_queue]:
   - that [w] is empty only if [f] is empty
   - that [lenr ≤ lenf] *)
Lemma check_spec q l w fl rl :
  length rl ≤ length fl + 1 →
  TC_invariant -∗
  {{{ is_queue_raw q l w fl rl ∗ TC Pchk ∗ HToken p None }}}
    «check q»
  {{{ q' w' fl' rl', RET «q'»;
      is_queue_raw q' l w' fl' rl'
      ∗ ⌜length rl' ≤ length fl'⌝
      ∗ ⌜w' = [] → fl' = []⌝
      ∗ HToken p None }}}.
Proof.
  intros Hlen. iIntros "#Htickinv !#" (Φ) "(#Hq & TC & Htok) HΦ".
  iDestruct "Hq" as (t ? ? h) "[(-> & -> & -> & -> & %) HT]".
  rewrite /Pchk Nat.add_comm.
  iDestruct "TC" as "[TC' TC]".
  wp_tick_lam.
  repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_op.
  destruct (decide (length rl ≤ length fl)) as [Hle|Hgt].
  { rewrite bool_decide_eq_true_2; [| lia]. wp_tick_if.
    iDestruct "TC'" as "[_ TC']".
    wp_apply (checkw_spec (list_val w, #(length fl), #t, #(length rl), list_val rl)%V
               with "[//] [$TC' $Htok]").
    { iExists _, _, _, _. iSplit. done. iFrame "HT". }
    iIntros (q' w') "(Hq' & Hna & %)". iApply "HΦ". by iFrame. }
  { rewrite bool_decide_eq_false_2; [| lia]. wp_tick_if.
    iDestruct "TC'" as "[[[[[[TCf TCr] TCa] TCcr] TCK] TCR] TCchk]".
    rewrite (_: thunk_debt w fl rl = 0).
    2: { rewrite /thunk_debt (_: K * length fl - K * length rl = 0)%nat; nia. }
    wp_apply (hthunk_force with "[//] [$HT $Htok $TCf]"). done.
    iIntros (flv) "(-> & ? & Htok)". wp_tick_let.
    wp_tick_closure.
    divide_credit "TC" 15 3.
    (* we can assign namespace id 0 to this thunk as it doesn't need to force
       other thunks. *)
    iPoseProof (hthunk_create _ 0 (2 * K * length fl)
                            (λ flv', ⌜flv' = list_val (fl ++ reverse rl)⌝)%I
                            (λ: <>, append (list_val fl) (rev (list_val rl)))%V
               with "[//] [$TCcr TCr TC' TCR TCa]") as "S".
    { iIntros "Htok TC" (ψ) "Hψ". wp_tick_lam.
      rewrite (_: 2 * K * length fl = K * length fl + K * length fl); [|lia].
      iDestruct "TC" as "[TC TCr']". iCombine "TCr TCr'" as "TCr".
      iCombine "TCR TCr" as "TCr".
      wp_apply (stream_revl with "[//] [TCr]").
      { iApply (TC_weaken with "TCr"). unfold K. nia. }
      iIntros (rrl) "->".
      iCombine "TCa TC" as "TC".
      wp_apply (stream_append with "[//] [TC]").
      { iApply (TC_weaken with "TC"). unfold K. nia. }
      iIntros (l') "->". by iApply ("Hψ" with "Htok"). }
    rewrite -lock. (* XXX *) wp_apply "S".
    iIntros (t') "#HT'". wp_tick_let. wp_tick_op. repeat wp_tick_pair.
    wp_apply (checkw_spec (list_val fl, #(length fl + length rl), #t', #0, #())%V
                          (fl ++ reverse rl) fl (fl ++ reverse rl) nil
               with "[//] [$TCchk $Htok]").
    { iExists _, (length fl + length rl), 0, 0. iSplit. iPureIntro. split.
      - repeat f_equal. lia.
      - rewrite app_length length_reverse app_nil_r. repeat split. by apply prefix_app_r.
      - iApply (hthunk_increase_debt with "HT'"). rewrite /thunk_debt.
        rewrite app_length length_reverse Nat.sub_0_r. nia. }
    iIntros (q' w') "(Hq' & Htok & %)". iApply "HΦ". iFrame. iPureIntro; split; try done.
    rewrite app_length length_reverse /=. lia. }
Qed.

#[global] Opaque Pchk.

Definition Ppush := 40 + K + Pchk.

Lemma push_spec q l x :
  TC_invariant -∗
  {{{ is_queue q l ∗ TC Ppush ∗ HToken p None }}}
    «push q x»
  {{{ q', RET «q'»; is_queue q' (l ++ [x]) ∗ HToken p None }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "(#Hq & [[TC TCK] TCchk] & Htok) HΦ".
  iDestruct "Hq" as (w fl rl) "(Hqr & % & %)".
  iDestruct "Hqr" as (t ? ? h) "[(-> & -> & -> & -> & %) HT]".
  iRevert "TC"; iIntros "TC".
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_pair. wp_tick_op. repeat wp_tick_pair.
  iDestruct (hthunk_pay with "HT TCK") as ">#HT'". done.
  wp_apply (check_spec (list_val w, #(length fl), #t, #(length rl + 1), list_val (x::rl))%V
                       (fl ++ reverse rl ++ [x]) w fl (x :: rl)
            with "[//] [$TCchk $Htok]").
  { cbn; lia. }
  { iExists _, (length fl), (length rl + 1), _. iSplit. iPureIntro. split.
    - repeat f_equal. lia.
    - repeat split; auto. cbn; lia. rewrite reverse_cons //.
    - iApply (hthunk_increase_debt with "HT'"). cbn; lia. }
  iIntros (q' w' fl' rl') "(Hq' & % & % & Htok)". iApply "HΦ".
  iFrame "Htok". rewrite app_assoc //. iExists _, _, _. by iFrame "Hq'".
Qed.

#[global] Opaque Ppush.

Definition Ppop := 50 + 2*K + Tcr + Tf + Pchk.

Lemma pop_spec q l :
  TC_invariant -∗
  {{{ is_queue q l ∗ TC Ppop ∗ HToken p None }}}
    «pop q»
  {{{ r, RET «r»;
      match l with
      | nil => ⌜r = NONEV⌝
      | x :: l' => ∃ q', ⌜r = SOMEV (x, q')%V⌝ ∗ is_queue q' l'
      end ∗
      HToken p None }}}.
Proof.
  iIntros "#Htickinv !#" (Φ) "(#Hq & [[[[TC TCK] TCcr] TCf] TCchk] & Htok) HΦ".
  iDestruct "Hq" as (w fl rl) "(Hqr & %Hlen & %Hw)".
  iDestruct "Hqr" as (t ? ? h) "[(-> & -> & -> & -> & %Hpref) HT]".
  iRevert "TC"; iIntros "TC".
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  destruct w as [|x w'] eqn:Hweq.
  { wp_tick_op. wp_tick_if. wp_tick_inj.
    rewrite Hw // (nil_length_inv rl) //.
    2: { rewrite Hw // in Hlen. cbn in Hlen. lia. }
    cbn. iApply ("HΦ" $! (InjLV #())%V). by iFrame "Htok". }
  { destruct fl as [|y fl]. by apply prefix_nil_not in Hpref.
    pose proof (prefix_cons_inv_1 _ _ _ _ Hpref). subst y.
    apply prefix_cons_inv_2 in Hpref.
    wp_tick_op. wp_tick_if. do 2 (wp_tick_proj; wp_tick_let).
    wp_tick_closure.
    divide_credit "TC" 11 3.
    (* increase the hthunk height: we need to be able to force the thunk we are
       wrapping, and all the thunks it may then need to force. *)
    iPoseProof (hthunk_create _ (S h) (thunk_debt w' fl rl)
                            (λ flv, ⌜flv = list_val fl⌝)%I
                            (λ: <>, Snd (ThunksCode.force #t))%V
               with "[//] [$TCcr TCK TCf TC']") as "S".
    { iIntros "Htok TC" (ψ) "Hψ". wp_tick_lam.
      iCombine "TCK TC" as "TC".
      iDestruct (hthunk_pay (thunk_debt (x :: w') (x :: fl) rl)
                            with "HT [TC]") as ">#HTpaid". done.
      { iApply (TC_weaken with "TC"). rewrite /thunk_debt.
        rewrite !(_: ∀ x l, length (x :: l) = S (length l)); [|done..].
        cbn in *. nia. }
      rewrite Nat.sub_diag.
      wp_apply (hthunk_force with "[//] [$TCf $HTpaid $Htok]"). cbn; lia.
      iIntros (flv) "(-> & _ & Htok)". rewrite /=. wp_tick_proj.
      by iApply ("Hψ" with "Htok"). }
    rewrite -lock. (* XXX *) wp_apply "S". iIntros (t') "#HT'".
    wp_tick_let. wp_tick_op. repeat wp_tick_pair.
    wp_apply (check_spec (list_val w', #(S (length fl) - 1), #t', #(length rl), list_val rl)%V
                         (fl ++ reverse rl) w' fl rl
               with "[//] [$TCchk $Htok]").
    { cbn in Hlen; lia. }
    { iExists _, _, _, _. iSplit. iPureIntro. repeat split; auto.
      - repeat f_equal. lia.
      - iFrame "HT'". }
    iIntros (q' w'' fl' rl') "(Hq' & % & % & Htok)".
    wp_tick_let. wp_tick_pair. wp_tick_inj.
    cbn [app]. iApply ("HΦ" $! (InjRV (x, q')%V) with "[$Htok Hq']").
    iExists q'. iSplit; first done. iExists _, _, _. by iFrame. }
Qed.

#[global] Opaque Ppop.

End PQueue.

#[global] Opaque K.

Local Definition public_api := (@push_spec, @pop_spec).
Print Assumptions public_api.
