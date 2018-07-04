From iris.heap_lang Require Import proofmode notation adequacy.
From iris.algebra Require Import auth.
From iris.base_logic Require Import invariants.
From iris.proofmode Require Import classes.
From stdpp Require Import namespaces.

Require Import Auth_nat Auth_mnat Misc Reduction Tactics.
Require Export Translation Simulation.

(* Require Import TimeCredits. *)

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n : nat.

(* rem: Unicode notations?
 *   medals: 🏅🥇🎖
 *   gears: ⚙⛭
 *   shields: ⛨
 *   florettes: ✿❀
 *   squares: ▣ ▢ ▤ ▥ ☑
 *   circles: ◉ ◎ ◌ ◍ ☉
 *   pentagons: ⬟ ⬠
 *   hexagons: ⬢ ⬡
 *   shogi pieces: ☗ ☖
 *   other: ⮝ ⮙ ⯊ ⯎
 *)



(*
 * Prerequisites on the global monoid Σ
 *)

Class timeReceiptHeapPreG Σ := {
  timeReceiptHeapPreG_heapPreG :> heapPreG Σ ;
  timeReceiptHeapPreG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapPreG_inG2 :> inG Σ (authR mnatUR) ;
}.

Class timeReceiptLoc := {
  timeReceiptLoc_loc : loc ;
}.

Class timeReceiptHeapG Σ := {
  timeReceiptHeapG_heapG :> heapG Σ ;
  timeReceiptHeapG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapG_inG2 :> inG Σ (authR mnatUR) ;
  timeReceiptHeapG_loc :> timeReceiptLoc ;
  timeReceiptHeapG_name1 : gname ;
  timeReceiptHeapG_name2 : gname ;
}.

Local Notation γ1 := timeReceiptHeapG_name1.
Local Notation γ2 := timeReceiptHeapG_name2.
Local Notation ℓ := timeReceiptLoc_loc.



(*
 * Implementation and specification of `TR` and `tock`
 *)

Section Tock.

  Context `{timeReceiptLoc}.

  Definition loop : val :=
    rec: "f" <> := "f" #().

  Definition tock : val :=
    tick loop ℓ.

End Tock.



Section TockSpec.

  Context `{timeReceiptHeapG Σ}.

  Definition TR (n : nat) : iProp Σ :=
    own γ1 (◯nat n).

  Definition TRdup (n : mnat) : iProp Σ :=
    own γ2 (◯mnat n).
  Arguments TRdup _%nat_scope.

  Lemma TR_plus m n :
    TR (m + n) ≡ (TR m ∗ TR n)%I.
  Proof. by rewrite /TR auth_frag_op own_op. Qed.
  Lemma TR_succ n :
    TR (S n) ≡ (TR 1 ∗ TR n)%I.
  Proof. by rewrite (eq_refl : S n = 1 + n)%nat TR_plus. Qed.

  Lemma TR_timeless n :
    Timeless (TR n).
  Proof. exact _. Qed.

  (* note: IntoAnd false will become IntoSep in a future version of Iris *)
  Global Instance into_sep_TR_plus m n p : IntoAnd p (TR (m + n)) (TR m) (TR n).
  Proof. rewrite /IntoAnd TR_plus ; iIntros "[Hm Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TR_plus m n : FromAnd false (TR (m + n)) (TR m) (TR n).
  Proof. by rewrite /FromAnd TR_plus. Qed.
  Global Instance into_sep_TR_succ n p : IntoAnd p (TR (S n)) (TR 1) (TR n).
  Proof. rewrite /IntoAnd TR_succ ; iIntros "[H1 Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TR_succ n : FromAnd false (TR (S n)) (TR 1) (TR n).
  Proof. by rewrite /FromAnd [TR (S n)] TR_succ. Qed.

  Lemma TRdup_max m n :
    TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)%I.
  Proof. by rewrite /TRdup auth_frag_op own_op. Qed.

  Lemma TRdup_timeless n :
    Timeless (TRdup n).
  Proof. exact _. Qed.

  (* note: IntoAnd false will become IntoSep in a future version of Iris *)
  Global Instance into_sep_TRdup_max m n p : IntoAnd p (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. rewrite /IntoAnd TRdup_max ; iIntros "[Hm Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TRdup_max m n : FromAnd false (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. by rewrite /FromAnd TRdup_max. Qed.

  Definition timeReceiptN := nroot .@ "timeReceipt".

  Definition TOCKCTXT (nmax : nat) : iProp Σ :=
    inv timeReceiptN (∃ (n:nat), ℓ ↦ #(nmax-n-1) ∗ own γ1 (●nat n) ∗ own γ2 (●mnat n) ∗ ⌜(n < nmax)%nat⌝)%I.

  Lemma TR_nmax_absurd (nmax : nat) (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TOCKCTXT nmax -∗ TR nmax ={E}=∗ False.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %In'.
    exfalso ; lia.
  Qed.

  Lemma TR_TRdup (nmax : nat) (E : coPset) (n : nat) :
    ↑timeReceiptN ⊆ E →
    TOCKCTXT nmax -∗ TR n ={E}=∗ TR n ∗ TRdup n.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    iInv timeReceiptN as (m) ">(Hℓ & Hγ1● & Hγ2● & Im)" "InvClose".
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %In.
    iDestruct (auth_mnat_update_read_auth with "Hγ2●") as ">[Hγ2● Hγ2◯]".
    iAssert (TR n ∗ TRdup n)%I with "[$Hγ1◯ Hγ2◯]" as "$". {
      rewrite (_ : m = m `max` n) ; last lia.
      iDestruct "Hγ2◯" as "[_ $]".
    }
    iApply "InvClose". auto with iFrame.
  Qed.

  Theorem loop_spec s E (Φ : val → iProp Σ) :
    WP loop #() @ s ; E {{ Φ }}%I.
  Proof.
    iLöb as "IH". wp_rec. iExact "IH".
  Qed.

  Theorem tock_spec (nmax : nat) s E e v :
    ↑timeReceiptN ⊆ E →
    IntoVal e v →
    TOCKCTXT nmax -∗
    {{{ True }}} tock e @ s ; E {{{ RET v ; TR 1 }}}.
  Proof.
    intros ? <- % of_to_val. iIntros "#Inv" (Ψ) "!# _ HΨ".
    iLöb as "IH".
    wp_lam.
    (* open the invariant, in order to read the value k = nmax−n−1 of location ℓ: *)
    wp_bind (! _)%E ;
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    wp_load.
    (* close the invariant: *)
    iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
    wp_let.
    (* test whether k ≤ 0: *)
    wp_op ; destruct (bool_decide (nmax - n - 1 ≤ 0)) eqn:Im ; wp_if.
    (* — if k ≤ 0 then we loop indefinitely, which gives us any spec we want
         (because we are reasoning in partial correctness): *)
    - iApply loop_spec.
    (* — otherwise: *)
    - apply Is_true_false in Im ; rewrite -> bool_decide_spec in Im.
      wp_op.
      (* open the invariant again, in order to perform CAS on location ℓ: *)
      wp_bind (CAS _ _ _)%E ;
      iInv timeReceiptN as (n') ">(Hℓ & Hγ1● & Hγ2● & In')" "InvClose" ; iDestruct "In'" as %In'.
      (* test whether the value ℓ is still k, by comparing n with n': *)
      destruct (nat_eq_dec n n') as [ <- | Hneq ].
      (* — if it holds, then CAS succeeds and ℓ is decremented: *)
      + wp_cas_suc.
        (* reform the invariant with n+1 instead of n, and an additional time
           receipt produced: *)
        replace (nmax - n - 1 - 1) with (nmax - (n+1)%nat - 1) by lia.
        iMod (auth_nat_update_incr _ _ 1 with "Hγ1●") as "[Hγ1● Hγ1◯]" ; simpl.
        iMod (auth_mnat_update_incr _ _ 1 with "Hγ2●") as "Hγ2●" ; simpl.
        assert ((n+1) < nmax)%nat by lia.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. iApply "HΨ" ; iExact "Hγ1◯".
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ] ; clear dependent n.
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "HΨ").
  Qed.

  Theorem tock_spec_simple (nmax : nat) v :
    TOCKCTXT nmax -∗
    {{{ True }}} tock v {{{ RET v ; TR 1 }}}.
  Proof.
    iIntros "#Inv" (Ψ) "!# H HΨ".
    by iApply (tock_spec with "Inv H HΨ").
  Qed.

End TockSpec.



(*
 * Simulation
 *)

Notation trtranslation := (translation tock).
Notation trtranslationV := (translationV tock).
Notation trtranslationS := (translationS tock).
Notation trtranslationKi := (translationKi tock).
Notation trtranslationK := (translationK tock).

Notation "E« e »" := (trtranslation e%E).
Notation "V« v »" := (trtranslationV v%V).
Notation "Ki« ki »" := (trtranslationKi ki).
Notation "K« K »" := (trtranslationK K).
Notation "S« σ »" := (trtranslationS σ%V).
Notation "S« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (trtranslationS σ%V)).
Notation "T« t »" := (trtranslation <$> t%E).

Notation "« e »" := (trtranslation e%E).
Notation "« e »" := (trtranslation e%E) : expr_scope.
Notation "« v »" := (trtranslationV v%V) : val_scope.

(* for some reason, these notations make parsing fail,
 * even if they only regard printing… *)
(*
Notation "« e »" := (trtranslation e%E) (only printing).
Notation "« v »" := (trtranslationV v%V) (only printing).
Notation "« ki »" := (trtranslationKi ki) (only printing).
Notation "« K »" := (trtranslationK K) (only printing).
Notation "« σ »" := (trtranslationS σ%V) (only printing).
Notation "« σ , n »" := (<[ℓ := LitV (LitInt n%nat)]> (trtranslationS σ%V)) (only printing).
Notation "« t »" := (trtranslation <$> t%E) (only printing).
*)



Section Soundness.

  (* TODO *)

End Soundness.



(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Section Tactics.

  (* TODO *)

End Tactics.

Ltac wp_tock :=
  idtac.