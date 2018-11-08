(* TEMPORARY:
 * This file is far from being complete. It only addresses the case when
 * max_tc < max_tr, and soundness is not done yet. Definitions will change.
 * It does provide a (hopefully) workable interface for proving programs with
 * time credits and time receipts, including proof-mode tactics.
 *)

From iris_time.heap_lang Require Import proofmode notation adequacy lang.
From iris.base_logic Require Import invariants.

From iris_time Require Import Auth_nat Auth_mnat Misc Reduction Tactics.
From iris_time Require Export Translation Simulation.

From iris.proofmode Require Import coq_tactics.
Import uPred.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n max_tc max_tr : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.



(*
 * Combined abstract interface for time credits and receipts
 *)

(* Ideally, this would be represented as a record (or a typeclass), but it has
 * to be an Iris proposition (iProp Σ) and not a Coq proposition (Prop). *)
Definition TCTR_interface `{irisG heap_lang Σ, Tick}
  (TC : nat → iProp Σ)
  (max_tr : nat)
  (TR : nat → iProp Σ)
  (TRdup : nat → iProp Σ)
: iProp Σ := (
    ⌜∀ n, Timeless (TC n)⌝
  ∗ (|={⊤}=> TC 0%nat)
  ∗ ⌜∀ m n, TC (m + n)%nat ≡ (TC m ∗ TC n)⌝
  ∗ ⌜∀ n, Timeless (TR n)⌝
  ∗ ⌜∀ n, Timeless (TRdup n)⌝
  ∗ ⌜∀ n, Persistent (TRdup n)⌝
  ∗ (∀ n, TR n ={⊤}=∗ TR n ∗ TRdup n)
  ∗ (|={⊤}=> TR 0%nat)
(*   ∗ (|={⊤}=> TRdup 0%nat) *)
  ∗ ⌜∀ m n, TR (m + n)%nat ≡ (TR m ∗ TR n)⌝
  ∗ ⌜∀ m n, TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)⌝
(*   ∗ (TR max_tr ={⊤}=∗ False) *)
  ∗ (TRdup max_tr ={⊤}=∗ False)
  ∗ (∀ v n, {{{ TC 1%nat ∗ TRdup n }}} tick v {{{ RET v ; TR 1%nat ∗ TRdup (n+1)%nat }}})
)%I.



(*
 * Prerequisites on the global monoid Σ
 *)

Class tctrHeapPreG Σ := {
  tctrHeapPreG_heapPreG :> heapPreG Σ ;
  tctrHeapPreG_inG_TC    :> inG Σ (authR natUR) ;
  tctrHeapPreG_inG_TR    :> inG Σ (authR natUR) ;
  tctrHeapPreG_inG_TRdup :> inG Σ (authR mnatUR) ;
}.

Class tctrHeapG Σ := {
  tctrHeapG_heapG :> heapG Σ ;
  tctrHeapG_inG_TC    :> inG Σ (authR natUR) ;
  tctrHeapG_inG_TR    :> inG Σ (authR natUR) ;
  tctrHeapG_inG_TRdup :> inG Σ (authR mnatUR) ;
  tctrHeapG_loc :> TickCounter ;
  tctrHeapG_name_TC    : gname ;
  tctrHeapG_name_TR    : gname ;
  tctrHeapG_name_TRdup : gname ;
}.

Local Notation γ := tctrHeapG_name_TC.
Local Notation γ1 := tctrHeapG_name_TR.
Local Notation γ2 := tctrHeapG_name_TRdup.
Local Notation ℓ := tick_counter.



(*
 * Implementation and specification of `tick`, `TC`, `TR` and `TRdup`
 *)



(* This code is irrelevant for tick_spec but has to be unsafe for proving
 * the safety theorem: *)
Definition fail : val :=
  λ: <>, #() #().

Global Instance credits_tick {_:TickCounter} : Tick :=
  generic_tick fail.



Section Definitions.

  Context `{tctrHeapG Σ}.
  Context (max_tc max_tr : nat).
  Context {Ineq : max_tc < max_tr}.

  Definition TC (n : nat) : iProp Σ :=
    own γ (◯nat n).

  Lemma TC_plus m n :
    TC (m + n) ≡ (TC m ∗ TC n)%I.
  Proof using. by rewrite /TC auth_frag_op own_op. Qed.
  Lemma TC_succ n :
    TC (S n) ≡ (TC 1%nat ∗ TC n)%I.
  Proof using. by rewrite (eq_refl : S n = 1 + n)%nat TC_plus. Qed.
  Lemma TC_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TC n₁ -∗ TC n₂.
  Proof using. apply own_auth_nat_weaken. Qed.

  Lemma TC_timeless n :
    Timeless (TC n).
  Proof using. exact _. Qed.

  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TC_plus m n : IntoSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof using. by rewrite /IntoSep TC_plus. Qed.
  Global Instance from_sep_TC_plus m n : FromSep (TC (m + n)) (TC m) (TC n) | 0.
  Proof using. by rewrite /FromSep TC_plus. Qed.
  Global Instance into_sep_TC_succ n : IntoSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof using. by rewrite /IntoSep TC_succ. Qed.
  Global Instance from_sep_TC_succ n : FromSep (TC (S n)) (TC 1) (TC n) | 100.
  Proof using. by rewrite /FromSep [TC (S n)] TC_succ. Qed.

  Definition TR (n : nat) : iProp Σ :=
    own γ1 (◯nat n).

  Definition TRdup (n : mnat) : iProp Σ :=
    own γ2 (◯mnat n).
  Arguments TRdup _%nat_scope.

  Lemma TR_plus m n :
    TR (m + n) ≡ (TR m ∗ TR n)%I.
  Proof using. by rewrite /TR auth_frag_op own_op. Qed.
  Lemma TR_succ n :
    TR (S n) ≡ (TR 1 ∗ TR n)%I.
  Proof using. by rewrite (eq_refl : S n = 1 + n)%nat TR_plus. Qed.
  Lemma TR_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TR n₁ -∗ TR n₂.
  Proof using. apply own_auth_nat_weaken. Qed.

  Lemma TR_timeless n :
    Timeless (TR n).
  Proof using. exact _. Qed.


  (* We give higher priorities to the (+) instances so that the (S n)
     instances are not chosen when m is a constant. *)
  Global Instance into_sep_TR_plus m n : IntoSep (TR (m + n)) (TR m) (TR n) | 0.
  Proof using. by rewrite /IntoSep TR_plus. Qed.
  Global Instance from_sep_TR_plus m n : FromSep (TR (m + n)) (TR m) (TR n) | 0.
  Proof using. by rewrite /FromSep TR_plus. Qed.
  Global Instance into_sep_TR_succ n : IntoSep (TR (S n)) (TR 1) (TR n) | 100.
  Proof using. by rewrite /IntoSep TR_succ. Qed.
  Global Instance from_sep_TR_succ n : FromSep (TR (S n)) (TR 1) (TR n) | 100.
  Proof using. by rewrite /FromSep [TR (S n)] TR_succ. Qed.

  Lemma TRdup_max m n :
    TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)%I.
  Proof using. by rewrite /TRdup auth_frag_op own_op. Qed.
  Lemma TRdup_weaken (n₁ n₂ : nat) :
    (n₂ ≤ n₁)%nat →
    TRdup n₁ -∗ TRdup n₂.
  Proof using. apply own_auth_mnat_weaken. Qed.

  Lemma TRdup_timeless n :
    Timeless (TRdup n).
  Proof using. exact _. Qed.
  Lemma TRdup_persistent n :
    Persistent (TRdup n).
  Proof using. exact _. Qed.

  Global Instance into_sep_TRdup_max m n : IntoSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof using. by rewrite /IntoSep TRdup_max. Qed.
  Global Instance from_sep_TRdup_max m n : FromSep (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof using. by rewrite /FromSep TRdup_max. Qed.

  Definition tctrN := nroot .@ "combinedTimeCreditTimeReceipt".

  Definition TCTR_invariant : iProp Σ :=
    inv tctrN (
      ∃ (m:nat),
        ⌜(m ≤ max_tc)%nat⌝
      ∗ ℓ ↦ #m
      ∗ own γ (●nat m)
      ∗ own γ1 (●nat (max_tc - m))
      ∗ own γ2 (●mnat (max_tc - m))
    )%I.

  Lemma zero_TC :
    TCTR_invariant ={⊤}=∗ TC 0.
  Proof using.
    iIntros "#Htickinv".
    iInv tctrN as (m) ">(? & ? & H● & ?)" "InvClose".
    iDestruct (own_auth_nat_null with "H●") as "[H● $]".
    iApply "InvClose" ; eauto with iFrame.
  Qed.

  Lemma zero_TR :
    TCTR_invariant ={⊤}=∗ TR 0.
  Proof using.
    iIntros "#Htickinv".
    iInv tctrN as (m) ">(? & ? & ? & Hγ1● & ?)" "InvClose".
    iDestruct (own_auth_nat_null with "Hγ1●") as "[Hγ1● $]".
    iApply "InvClose" ; eauto with iFrame.
  Qed.

  Lemma zero_TRdup :
    TCTR_invariant ={⊤}=∗ TRdup 0.
  Proof using.
    iIntros "#Htickinv".
    iInv tctrN as (m) ">(? & ? & ? & ? & Hγ2●)" "InvClose".
    iDestruct (own_auth_mnat_null with "Hγ2●") as "[Hγ2● $]".
    iApply "InvClose" ; eauto with iFrame.
  Qed.

  Lemma TR_nmax_absurd (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR max_tr ={E}=∗ False.
  Proof using Ineq.
    iIntros (?) "#Inv Hγ1◯".
    iInv tctrN as (m) ">(I & _ & _ & Hγ1● & _)" "InvClose" ; iDestruct "I" as %I.
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %I'.
    exfalso ; lia.
  Qed.
  Lemma TR_lt_nmax n (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR n ={E}=∗ TR n ∗ ⌜n < max_tr⌝%nat.
  Proof using Ineq.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec max_tr n) as [ I | I ] ; last by iFrame.
    iDestruct (TR_weaken n max_tr with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TR_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TRdup_nmax_absurd (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TRdup max_tr ={E}=∗ False.
  Proof using Ineq.
    iIntros (?) "#Inv Hγ2◯".
    iInv tctrN as (m) ">(I & _ & _ & _ & Hγ2●)" "InvClose" ; iDestruct "I" as %I.
    iDestruct (own_auth_mnat_le with "Hγ2● Hγ2◯") as %I'.
    exfalso ; lia.
  Qed.
  Lemma TRdup_lt_nmax n (E : coPset) :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TRdup n ={E}=∗ TRdup n ∗ ⌜n < max_tr⌝%nat.
  Proof using Ineq.
    iIntros (?) "#Inv Hγ1◯".
    destruct (le_lt_dec max_tr n) as [ I | I ] ; last by iFrame.
    iDestruct (TRdup_weaken n max_tr with "Hγ1◯") as "Hγ1◯" ; first done.
    iDestruct (TRdup_nmax_absurd with "Inv Hγ1◯") as ">?" ; first done.
    done.
  Qed.

  Lemma TR_TRdup (E : coPset) n :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗ TR n ={E}=∗ TR n ∗ TRdup n.
  Proof using max_tr.
    iIntros (?) "#Inv Hγ1◯".
    iInv tctrN as (m) ">(I & Hℓ & Hγ● & Hγ1● & Hγ2●)" "InvClose".
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %I'.
    iDestruct (auth_mnat_update_read_auth with "Hγ2●") as ">[Hγ2● Hγ2◯]".
    iAssert (TR n ∗ TRdup n)%I with "[$Hγ1◯ Hγ2◯]" as "$". {
      rewrite (_ : (max_tc-m)%nat = (max_tc-m)%nat `max` n) ; last lia.
      iDestruct "Hγ2◯" as "[_ $]".
    }
    iApply "InvClose". auto with iFrame.
  Qed.

  Theorem tick_spec s E (v : val) n :
    ↑tctrN ⊆ E →
    TCTR_invariant -∗
    {{{ ▷ TC 1 ∗ ▷ TRdup n }}} tick v @ s ; E {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof using max_tr.
    intros ?. iIntros "#Inv" (Ψ) "!# [Hγ◯ Hγ2◯] HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value m of location ℓ: *)
    wp_bind (! _)%E ;
    iInv tctrN as (m) ">(I & Hℓ & Hγ● & Hγ1● & Hγ2●)" "InvClose".
    wp_load.
    (* deduce that m ≥ 1, because we hold a time credit: *)
    iDestruct (own_auth_nat_le with "Hγ● Hγ◯") as %J.
    (* close the invariant: *)
    iMod ("InvClose" with "[ I Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether m ≤ 0: *)
    wp_op ; destruct (bool_decide (m ≤ 0)) eqn:J' ; wp_if.
    (* — if m ≤ 0 then this is absurd, because we hold a time credit: *)
    - apply Is_true_eq_left, bool_decide_spec in J'.
      exfalso ; lia.
    (* — otherwise: *)
    - clear J'.
      wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
(*       iInv timeCreditN as (n') ">(Hℓ & Hγ●)" "InvClose". *)
      iInv tctrN as (m') ">(I & Hℓ & Hγ● & Hγ1● & Hγ2●)" "InvClose".
      (* test whether the value ℓ is still k, by comparing m with m': *)
      destruct (nat_eq_dec m m') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with m−1 instead of m: *)
        replace (Z.of_nat m - 1) with (Z.of_nat (m - 1)%nat) by lia.
        iMod (auth_nat_update_decr _ _ _ 1 with "Hγ● Hγ◯") as "[Hγ● Hγ◯]" ; first done.
        iMod (auth_nat_update_incr _ _ 1 with "Hγ1●") as "[Hγ1● Hγ1◯]" ; simpl.
        iMod (auth_mnat_update_incr' _ _ _ 1 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]" ; simpl.
        iDestruct "I" as %I.
        replace (max_tc - m + 1)%nat with (max_tc - (m - 1))%nat by lia.
        assert ((m-1) ≤ max_tc)%nat by lia.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. iApply "HΨ" ; by iFrame.
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ I Hℓ Hγ● Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ◯ Hγ2◯ HΨ").
  Qed.

  Theorem tick_spec_simple v n :
    TCTR_invariant -∗
    {{{ TC 1 ∗ TRdup n }}} tick v {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof using max_tr.
    iIntros "#Hinv" (Ψ) "!# [ HTC HTR ] HΨ".
    by iApply (tick_spec with "Hinv [$HTC $HTR] HΨ").
  Qed.

  Lemma TC_implementation : TCTR_invariant -∗ TCTR_interface TC max_tr TR TRdup.
  Proof using Ineq.
    iIntros "#Hinv". repeat iSplitR.
    - iPureIntro. by apply TC_timeless.
    - by iApply (zero_TC with "Hinv").
    - iPureIntro. by apply TC_plus.
    - iPureIntro. by apply TR_timeless.
    - iPureIntro. by apply TRdup_timeless.
    - iPureIntro. by apply TRdup_persistent.
    - iIntros (n). by iApply (TR_TRdup with "Hinv").
    - by iApply (zero_TR with "Hinv").
    - iPureIntro. by apply TR_plus.
    - iPureIntro. by apply TRdup_max.
    - by iApply (TRdup_nmax_absurd with "Hinv").
    - iIntros (v n). by iApply (tick_spec_simple with "Hinv").
  Qed.

End Definitions.



(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

(* TODO: a version of the tactics working with the abstract interface: *)

Section Tactics.

  Context {Σ : gFunctors}.

  Implicit Types Φ : val → iProp Σ.
  Implicit Types Δ : envs (uPredI (iResUR Σ)).

  Lemma tac_wp_tick `{tctrHeapG Σ} Δ Δ1 Δ2 Δ3 Δ' i j1 j2 j3 max_tc m n p s E K (v : val) Φ :
    ↑tctrN ⊆ E →
    MaybeIntoLaterNEnvs 1 Δ Δ1 →
    envs_lookup i Δ   = Some (true, TCTR_invariant max_tc) →
    envs_lookup j1 Δ1 = Some (false, TC (S m)) →
    envs_lookup j3 Δ1 = Some (false, TR n) →
    envs_lookup j2 Δ1 = Some (false, TRdup p) →
    envs_simple_replace j1 false (Esnoc Enil j1 (TC m)) Δ1 = Some Δ3 →
    envs_simple_replace j3 false (Esnoc Enil j3 (TR (S n))) Δ3 = Some Δ2 →
    envs_simple_replace j2 false (Esnoc Enil j2 (TRdup (S p))) Δ2 = Some Δ' →
    envs_entails Δ' (WP fill K v @ s; E {{ Φ }}) →
    envs_entails Δ (WP fill K (App tick v) @ s; E {{ Φ }}).
  Admitted.

End Tactics.

Ltac wp_tick :=
  iStartProof ;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Q) =>
      first
        [ reshape_expr false e ltac:(fun K e' =>
            eapply (tac_wp_tick _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ K)
          )
        | fail 1 "wp_tick: cannot find 'tick ?v' in" e ] ;
      [ try solve_ndisj
      | exact _
      | (* lookup invariant: *) (iAssumptionCore || fail "wp_tick: cannot find TCTR_invariant")
      | (* lookup TC:    *) (iAssumptionCore || fail "wp_tick: cannot find TC (S _)")
      | (* lookup TRdup: *) (iAssumptionCore || fail "wp_tick: cannot find TRdup _")
      | (* lookup TR:    *) (iAssumptionCore || fail "wp_tick: cannot find TR _")
      | (* replace TC:    *) proofmode.reduction.pm_reflexivity
      | (* replace TRdup: *) proofmode.reduction.pm_reflexivity
      | (* replace TR:    *) proofmode.reduction.pm_reflexivity
      | wp_expr_simpl ]
  | |- envs_entails _ (twp ?s ?E ?e ?Q) =>
      fail "wp_tick is not implemented for twp"
  | _ => fail "wp_tick: not a 'wp'"
  end.

Example test `{tctrHeapG Σ} :
  TCTR_invariant 100 -∗
  TC 37 -∗
  TRdup 63%nat -∗
  TR 0 -∗
  WP tick #0 {{ _, True }}.
Proof using.
  iIntros "#Inv HTC HTRdup HTR".
  wp_tick.
Abort.

Ltac wp_tick_rec :=
  wp_tick ; first
    [ wp_rec
    | match goal with
      | |-context [ App ?f _ ] =>
          unlock f ; wp_rec
      | |-context [ App (translation ?f) _ ] =>
          unlock f ; wp_rec
      | |-context [ App (of_val (translationV ?f)) _ ] =>
          unlock f ; wp_rec
      end
    | fail ].
Ltac wp_tick_lam := wp_tick_rec.
Ltac wp_tick_let := wp_tick ; wp_let.
Ltac wp_tick_seq := wp_tick ; wp_seq.
Ltac wp_tick_op := wp_tick ; wp_op.
Ltac wp_tick_if := wp_tick ; wp_if.
Ltac wp_tick_match := wp_tick ; wp_match ; do 2 wp_lam ; wp_tick ; wp_lam.
Ltac wp_tick_proj := wp_tick ; wp_proj.
Ltac wp_tick_alloc loc := wp_tick ; wp_alloc loc.
Ltac wp_tick_load := wp_tick ; wp_load.
Ltac wp_tick_store := wp_tick ; wp_store.