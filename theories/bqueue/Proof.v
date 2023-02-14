From stdpp Require Import list.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time.heap_lang Require Import notation.
From iris_time Require Import Base TimeCredits Untranslate.
From iris_time.thunks Require Import Generations HThunks.
From iris_time.streams Require Import StreamsCode Streams.
From iris_time.bqueue Require Import Code.

Section BQueue.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γt *)
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (authR $ optionUR $ exclR boolO)}.    (* γforced *)
Context `{na_invG Σ}.
Context (p : na_inv_pool_name).

Local Hint Resolve subdebits_reflexive : core.

Local Definition K :=
  Eval compute in (30 + 11 + 19).

Definition queue_debits (lenf lenr : nat) :=
  repeat K (lenf - lenr) ++ repeat 0 (S (min lenf lenr)).

Lemma queue_debits_cons_front lenf lenr :
  lenr ≤ lenf →
  queue_debits (S lenf) lenr = K :: queue_debits lenf lenr.
Proof.
  intros ?. rewrite /queue_debits.
  rewrite (_: S lenf - lenr = S (lenf - lenr)); last lia.
  rewrite !Nat.min_r; try lia. done.
Qed.

Lemma queue_debits_cons_rear lenf lenr :
  lenr < lenf →
  queue_debits lenf (S lenr) = repeat K (lenf - S lenr) ++ 0 :: repeat 0 (S lenr).
Proof.
  intros ?. rewrite /queue_debits. f_equal.
  rewrite Nat.min_r //; lia.
Qed.

Lemma queue_debits_app_front lenf lenf' lenr :
  lenr ≤ lenf' →
  queue_debits (lenf + lenf') lenr = repeat K lenf ++ queue_debits lenf' lenr.
Proof.
  intros HH. rewrite /queue_debits.
  rewrite (_: lenf + lenf' - lenr = lenf + (lenf' - lenr)); last lia.
  rewrite repeat_app app_assoc. rewrite !Nat.min_r //; lia.
Qed.

Lemma queue_debits_no_front lenf lenr :
  lenf ≤ lenr →
  queue_debits lenf lenr = repeat 0 (S lenf).
Proof.
  intros HH. rewrite /queue_debits.
  rewrite (_: lenf - lenr = 0); last lia.
  rewrite Nat.min_l; last lia. done.
Qed.

Lemma queue_debits_no_rear lenf :
  queue_debits lenf 0 = repeat K lenf ++ [0].
Proof.
  rewrite /queue_debits Nat.sub_0_r Nat.min_r //; last lia.
Qed.

Lemma queue_debits_split_middle lenr lenf :
  lenr < lenf →
  queue_debits lenf lenr = repeat K (lenf - S lenr) ++ K :: repeat 0 (S lenr).
Proof.
  intros. rewrite /queue_debits.
  rewrite (_: lenf - lenr = S (lenf - S lenr)); last lia.
  rewrite repeat_succ_last -app_assoc. f_equal.
  rewrite Nat.min_r//; lia.
Qed.

Definition is_queue_raw
  (q : val) (fl rl : list val) : iProp Σ :=
  ∃ (fs : loc) h,
    ⌜q = (#(length fl), #fs, #(length rl), ListV rl)%V⌝ ∗
    Stream p h fs (queue_debits (length fl) (length rl)) fl.

Definition is_queue (q : val) (l : list val) : iProp Σ :=
  ∃ fl rl,
    is_queue_raw q fl rl ∗
    ⌜l = fl ++ List.rev rl⌝ ∗
    ⌜length rl ≤ length fl⌝.

Instance is_queue_raw_persistent q fl rl :
  Persistent (is_queue_raw q fl rl).
Proof using. apply _. Qed.

Instance is_queue_persistent q l :
  Persistent (is_queue q l).
Proof using. apply _. Qed.

Local Ltac iSplit3 :=
  iSplit; [| iSplit ].

Local Ltac deconstruct_queue :=
  iDestruct "Hqueue" as
    "(%fl & %rl & #Hqueue_raw & %Hl & %Hlen)"; subst.

Local Ltac deconstruct_queue_raw :=
  iDestruct "Hqueue_raw" as
    "(%fs & %h & -> & #Hstream)".

Local Ltac construct_queue_raw :=
  iExists _, _; iSplit; swap 1 2; [ | iPureIntro .. ].

Local Ltac construct_queue fl rl :=
  iExists fl, rl; iSplit3;
  [ construct_queue_raw | iPureIntro .. ].

Local Tactic Notation "construct_queue" uconstr(fl) uconstr(rl) :=
  construct_queue fl rl.

Lemma empty_spec :
  TC_invariant -∗
  {{{ TC 13 }}}
    «empty #()»
  {{{ q, RET «q»; is_queue q [] }}}.
Proof.
  iIntros "#Hickinv !#" (Φ) "Htc HΦ".
  wp_tick_lam. rewrite /NIL. wp_tick_inj.
  divide_credit "Htc" 5 6.
  wp_apply (stream_nil p 1 with "[$] Htc'").
  iIntros (rs) "#Hstream".
  (* pay for the thunk now *)
  divide_credit "Htc" 3 2.
  iMod (stream_forward_debt _ _ [0] with "Hstream Htc'") as "#Hstream'";
    [|solve_ndisj|].
  { repeat constructor; lia. }
  repeat wp_tick_pair.
  iApply ("HΦ" $! (#0, #rs, #0, InjLV #())%V).
  construct_queue [] []; first iApply "Hstream'"; auto.
Qed.

Lemma is_empty_spec q xs :
  TC_invariant -∗
  is_queue q xs -∗
  {{{ TC 42 }}}
    «is_empty q»
  {{{ RET #(bool_decide (xs = [])); True }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  iPoseProof "Hqueue" as "#Hqueue'".
  deconstruct_queue. deconstruct_queue_raw.
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_op. destruct (decide (fl = [])) as [->|].
  { cbn in *. rewrite (nil_length_inv rl); [|lia].
    rewrite !bool_decide_true //. by iApply "Post". }
  { rewrite !bool_decide_false; first by iApply "Post".
    { intros HH; inversion HH.
      by pose proof (nil_length_inv fl ltac:(lia)). }
    { by intros [-> ?]%app_nil. } }
Qed.

Lemma stream_cons x q xs :
  TC_invariant -∗
  is_queue q xs -∗
  {{{ TC 34 }}}
    «cons x q»
  {{{ q', RET «q'» ; is_queue q' (x :: xs) }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_queue. deconstruct_queue_raw.
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  divide_credit "Htc" 4 8.
  wp_apply (stream_cons with "[$] [$] [$]").
  iIntros (t') "#Hstream'".
  (* Increase the debit of the new thunk to match the invariant. *)
  iMod (stream_forward_debt _ _ _ (queue_debits (S (length fl)) (length rl))
    with "Hstream' []") as "#Hstream''"; [|solve_ndisj|iApply zero_TC_now|].
  { rewrite queue_debits_cons_front //. constructor; unfold K; eauto with lia. }
  wp_tick_op. repeat wp_tick_pair.
  iApply ("Post" $! (#(length fl + 1), #t', #(length rl), ListV rl)%V).
  construct_queue (x :: fl) _; first iApply "Hstream''"; cbn; eauto with lia.
  repeat f_equal; lia.
Qed.

Lemma check_spec q fl rl :
  length rl ≤ length fl + 1 →
  TC_invariant -∗
  is_queue_raw q fl rl -∗
  {{{ TC 48 }}}
    «check q»
  {{{ q', RET «q'» ; is_queue q' (fl ++ List.rev rl) }}}.
Proof.
  intros Hlen.
  iIntros "#Hc #Hqueue_raw !#" (Φ) "Htc Post".
  iPoseProof "Hqueue_raw" as "#Hqueue_raw'".
  deconstruct_queue_raw.
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_op.
  destruct (decide (length rl ≤ length fl)) as [|Hlen_rev].
  { rewrite bool_decide_true; [|lia]. wp_tick_if.
    iApply ("Post" $! (#(length fl), #fs, #(length rl), ListV rl)%V).
    construct_queue _ _; eauto. }
  (* interesting case: |rl| = |fl| + 1 *)
  assert (length rl = length fl + 1) as Hlen' by lia. clear Hlen Hlen_rev.
  rewrite bool_decide_false; [|lia]. wp_tick_if. wp_tick_inj.
  untranslate. divide_credit "Htc" 12 13.
  wp_apply (stream_revl with "[] [$] Htc'").
  by iPureIntro; reflexivity.
  iIntros (trev) "#Hstream_rev".
  divide_credit "Htc" 4 8.
  wp_apply (stream_append with "Hstream Hstream_rev [$] [$]").
  iIntros (tapp) "#Hstream_app".
  rewrite queue_debits_no_front; last lia.
  (* distribute the costly debit created by [rev] onto thunks of the front half *)
  iMod (stream_forward_debt _ _ _ (queue_debits (length fl + length rl) 0)
    with "Hstream_app []") as "#Hstream_app'"; [|solve_ndisj|iApply zero_TC_now|].
  { rewrite repeat_succ_last debit_append_join_middle map_repeat Nat.add_0_r.
    rewrite queue_debits_app_front; last lia.
    eapply subdebits_app; [ eapply subdebits_repeat; unfold A,K; lia |].
    rewrite Hlen' Nat.add_1_r queue_debits_cons_front; last lia.
    constructor; [ unfold A,B,K; lia |].
    eapply (subdebits_covariant_in_slack 0); last lia.
    rewrite repeat_succ_last queue_debits_no_rear.
    eapply subdebits_app; last by eauto.
    eapply subdebits_repeat.
    lia. }
    wp_tick_op. repeat wp_tick_pair.
    iApply ("Post" $! (#(length fl + length rl), #tapp, #0, InjLV #())%V).
    construct_queue (fl ++ List.rev rl) [].
    { rewrite app_length rev_length. iApply "Hstream_app'". }
    all: cbn; eauto with lia.
    { repeat f_equal; try reflexivity. rewrite app_length rev_length. lia. }
    { rewrite app_nil_r //. }
Qed.

Lemma snoc q xs x :
  TC_invariant -∗
  is_queue q xs -∗
  {{{ TC 136 }}}
    «snoc q x»
  {{{ q', RET «q'» ; is_queue q' (xs ++ [x]) }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "Htc Post".
  deconstruct_queue. deconstruct_queue_raw.
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_pair. wp_tick_inj. wp_tick_op. repeat wp_tick_pair.
  untranslate.
  rewrite (untranslate_litv (length fl)) (untranslate_litv fs).
  rewrite (untranslate_litv (length rl + 1)%Z).
  untranslate. (* sigh *)
  (* we possibly need to pay for one debit of the front stream in order to
     preserve the invariant *)
  divide_credit "Htc" 48 60.
  iMod (stream_forward_debt _ _ _
   (* ds2:  *) (queue_debits (length fl) (S (length rl)))
   (* rest: *) 0
    with "Hstream Htc'") as "#Hstream'"; [|solve_ndisj|].
  { (* if the rear list is full, we are breaking the invariant anyway and
       [check] will rebalance the queue, so there is nothing to do. *)
    destruct (decide (length fl = length rl)) as [<-|].
    { rewrite !queue_debits_no_front; eauto with lia. }
    (* otherwise, pay for the last non-zero thunk *)
    rewrite queue_debits_split_middle; last lia.
    rewrite queue_debits_cons_rear; last lia.
    eapply subdebits_app; first by eauto.
    unfold K.
    constructor; eauto using subdebits_reflexive with lia.
  }
  wp_apply (check_spec _ fl (x :: rl) with "[$] [] Htc").
  { cbn; lia. }
  { construct_queue_raw; first iApply "Hstream'".
    repeat f_equal; cbn; eauto with lia. }
  { iIntros (q'). rewrite /= app_assoc. iApply "Post". }
Qed.

Notation token :=
  (HToken p None).

Lemma extract q x xs :
  TC_invariant -∗
  is_queue q (x :: xs) -∗
  {{{ TC 165 ∗ token }}}
    «extract q»
  {{{ q', RET («x», «q'»); is_queue q' xs ∗ token }}}.
Proof.
  iIntros "#Hc #Hqueue !#" (Φ) "[Htc Htok] Post".
  deconstruct_queue. deconstruct_queue_raw.
  rewrite /HToken (carve_out_gens_below_gen (h+1) None) //.
  iDestruct (na_own_union with "Htok") as "[Htok Htok_rest]".
  by apply disjoint_difference_r1.
  wp_tick_lam. repeat (wp_tick_let; repeat wp_tick_proj).
  rewrite (untranslate_litv fs). untranslate.
  destruct fl as [|y fl].
  { cbn in * |-. assert (rl = []) by (apply nil_length_inv; lia). subst.
    cbn in Hl; congruence. }
  cbn in Hl, Hlen. inversion Hl; subst; clear Hl. cbn [length].
  (* we need to pay for the first thunk before forcing it *)
  divide_credit "Htc" 85 60.
  iMod (stream_forward_debt _ _ _
    (* ds2:  *) (0 :: queue_debits (length fl) (length rl))
    (* rest: *) 0
    with "Hstream Htc'") as "#Hstream'"; [|solve_ndisj|].
  { (* if the rear list is full, the first thunk has in fact already been paid
       for, so there is nothing to do. *)
    destruct (decide (length rl = S (length fl))).
    { rewrite !queue_debits_no_front; eauto with lia. }
    (* otherwise, pay for the first thunk *)
    rewrite queue_debits_cons_front; last lia.
    constructor; eauto with lia. }
  divide_credit "Htc" 63 22.
  wp_apply (stream_uncons with "[$] [$] [$Htc' Htok]").
  { eauto with thunks. }
  { iFrame "Htok". }
  iIntros (t') "[#Hstream_tail Htok]".
  repeat (wp_tick_let; repeat wp_tick_proj).
  wp_tick_op. repeat wp_tick_pair.
  rewrite (_: (S (length fl) - 1) = length fl)%Z; [|lia].
  rewrite (untranslate_litv (length fl)) (untranslate_litv (length rl)).
  rewrite (untranslate_litv t'). untranslate.
  divide_credit "Htc" 3 48.
  wp_apply (check_spec _ fl rl with "[$] [] [$]").
  { cbn in *; lia. }
  { construct_queue_raw; eauto. }
  iIntros (q') "#Hqueue_tail".
  wp_tick_let. wp_tick_pair. iApply "Post". iFrame "Hqueue_tail".
  rewrite na_own_union; first by iFrame. by apply disjoint_difference_r1.
Qed.

End BQueue.
