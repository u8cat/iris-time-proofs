From iris.heap_lang Require Import proofmode notation adequacy.
From iris.base_logic Require Import invariants.

Require Import Auth_nat Auth_mnat Misc Reduction Tactics.
Require Export Translation Simulation.

Implicit Type e : expr.
Implicit Type v : val.
Implicit Type σ : state.
Implicit Type t : list expr.
Implicit Type K : ectx heap_ectx_lang.
Implicit Type m n nmax : nat.
Implicit Type φ ψ : val → Prop.
Implicit Type Σ : gFunctors.



(*
 * Abstract interface of time receipts
 *)

(* Ideally, this would be represented as a record (or a typeclass), but it has
 * to be an Iris proposition (iProp Σ) and not a Coq proposition (Prop). *)
Definition TR_interface `{irisG heap_lang Σ}
  (nmax : nat)
  (TR : nat → iProp Σ)
  (TRdup : nat → iProp Σ)
  (tick : val)
: iProp Σ := (
    ⌜∀ n, Timeless (TR n)⌝
  ∗ ⌜∀ n, Timeless (TRdup n)⌝
  ∗ ⌜∀ n, Persistent (TRdup n)⌝
  ∗ (∀ n, TR n ={⊤}=∗ TR n ∗ TRdup n)
  ∗ (|={⊤}=> TR 0%nat)
(*   ∗ (|={⊤}=> TRdup 0%nat) *)
  ∗ ⌜∀ m n, TR (m + n)%nat ≡ (TR m ∗ TR n)⌝
  ∗ ⌜∀ m n, TRdup (m `max` n) ≡ (TRdup m ∗ TRdup n)⌝
(*   ∗ (TR nmax ={⊤}=∗ False) *)
  ∗ (TRdup nmax ={⊤}=∗ False)
  ∗ (∀ v n, {{{ TRdup n }}} tick v {{{ RET v ; TR 1%nat ∗ TRdup (n+1)%nat }}})
)%I.



(*
 * Prerequisites on the global monoid Σ
 *)

Class timeReceiptHeapPreG Σ := {
  timeReceiptHeapPreG_heapPreG :> heapPreG Σ ;
  timeReceiptHeapPreG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapPreG_inG2 :> inG Σ (authR mnatUR) ;
}.

Class timeReceiptHeapG Σ := {
  timeReceiptHeapG_heapG :> heapG Σ ;
  timeReceiptHeapG_inG1 :> inG Σ (authR natUR) ;
  timeReceiptHeapG_inG2 :> inG Σ (authR mnatUR) ;
  timeReceiptHeapG_loc :> TickCounter ;
  timeReceiptHeapG_name1 : gname ;
  timeReceiptHeapG_name2 : gname ;
}.

Local Notation γ1 := timeReceiptHeapG_name1.
Local Notation γ2 := timeReceiptHeapG_name2.
Local Notation ℓ := tick_counter.



(*
 * Implementation and specification of `TR` and `tock`
 *)

Definition loop : val :=
  rec: "f" <> := "f" #().

Definition tock {_:TickCounter} : val :=
  tick loop.

Global Instance Tick_tock (Hloc: TickCounter) : Tick :=
  {| Translation.tick := tock |}.



Section TockSpec.

  Context `{timeReceiptHeapG Σ}.
  Context (nmax : nat).

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
  Lemma TRdup_persistent n :
    Persistent (TRdup n).
  Proof. exact _. Qed.

  (* note: IntoAnd false will become IntoSep in a future version of Iris *)
  Global Instance into_sep_TRdup_max m n p : IntoAnd p (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. rewrite /IntoAnd TRdup_max ; iIntros "[Hm Hn]". destruct p ; iFrame. Qed.
  Global Instance from_sep_TRdup_max m n : FromAnd false (TRdup (m `max` n)) (TRdup m) (TRdup n).
  Proof. by rewrite /FromAnd TRdup_max. Qed.

  Definition timeReceiptN := nroot .@ "timeReceipt".

  Definition TR_invariant : iProp Σ :=
    inv timeReceiptN (∃ (n:nat), ℓ ↦ #(nmax-n-1) ∗ own γ1 (●nat n) ∗ own γ2 (●mnat n) ∗ ⌜(n < nmax)%nat⌝)%I.

  Lemma zero_TR :
    TR_invariant ={⊤}=∗ TR 0.
  Proof.
    iIntros "#Htockinv".
    iInv timeReceiptN as (m) ">(Hcounter & Hγ1● & H)" "Hclose".
    iDestruct (own_auth_nat_null with "Hγ1●") as "[Hγ1● $]".
    iApply "Hclose" ; eauto with iFrame.
  Qed.

  Lemma zero_TRdup :
    TR_invariant ={⊤}=∗ TRdup 0.
  Proof.
    iIntros "#Htockinv".
    iInv timeReceiptN as (m) ">(Hcounter & Hγ1● & Hγ2● & Im)" "Hclose".
    iDestruct (own_auth_mnat_null with "Hγ2●") as "[Hγ2● $]".
    iApply "Hclose" ; eauto with iFrame.
  Qed.

  Lemma TR_nmax_absurd (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TR nmax ={E}=∗ False.
  Proof.
    iIntros (?) "#Inv Hγ1◯".
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    iDestruct (own_auth_nat_le with "Hγ1● Hγ1◯") as %In'.
    exfalso ; lia.
  Qed.

  Lemma TRdup_nmax_absurd (E : coPset) :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TRdup nmax ={E}=∗ False.
  Proof.
    iIntros (?) "#Inv Hγ2◯".
    iInv timeReceiptN as (n) ">(Hℓ & Hγ1● & Hγ2● & In)" "InvClose" ; iDestruct "In" as %In.
    iDestruct (own_auth_mnat_le with "Hγ2● Hγ2◯") as %In'.
    exfalso ; lia.
  Qed.

  Lemma TR_TRdup (E : coPset) n :
    ↑timeReceiptN ⊆ E →
    TR_invariant -∗ TR n ={E}=∗ TR n ∗ TRdup n.
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

  Theorem tock_spec s E e v m :
    ↑timeReceiptN ⊆ E →
    IntoVal e v →
    TR_invariant -∗
    {{{ TRdup m }}} tock e @ s ; E {{{ RET v ; TR 1 ∗ TRdup (m+1) }}}.
  Proof.
    intros ? <- % of_to_val. iIntros "#Inv" (Ψ) "!# Hγ2◯ HΨ".
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
(*         iMod (auth_mnat_update_incr _ _ 1 with "Hγ2●") as "Hγ2●" ; simpl. *)
        iMod (auth_mnat_update_incr' _ _ _ 1 with "Hγ2● Hγ2◯") as "[Hγ2● Hγ2◯]" ; simpl.
        assert ((n+1) < nmax)%nat by lia.
        (* close the invariant: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ].
        (* finish: *)
        wp_if. iApply "HΨ" ; by iFrame.
      (* — otherwise, CAS fails and ℓ is unchanged: *)
      + wp_cas_fail ; first (injection ; lia).
        (* close the invariant as is: *)
        iMod ("InvClose" with "[ Hℓ Hγ1● Hγ2● ]") as "_" ; [ by auto with iFrame | iModIntro ] ; clear dependent n.
        wp_if.
        (* conclude using the induction hypothesis: *)
        iApply ("IH" with "Hγ2◯ HΨ").
  Qed.

  Theorem tock_spec_simple v n :
    TR_invariant -∗
    {{{ TRdup n }}} tock v {{{ RET v ; TR 1 ∗ TRdup (n+1) }}}.
  Proof.
    iIntros "#Inv" (Ψ) "!# H HΨ".
    by iApply (tock_spec with "Inv H HΨ").
  Qed.

  Lemma TR_implementation : TR_invariant -∗ TR_interface nmax TR TRdup tock.
  Proof.
    iIntros "#Hinv". repeat iSplitR.
    - iPureIntro. by apply TR_timeless.
    - iPureIntro. by apply TRdup_timeless.
    - iPureIntro. by apply TRdup_persistent.
    - iIntros (n). by iApply (TR_TRdup with "Hinv").
    - by iApply (zero_TR with "Hinv").
    - iPureIntro. by apply TR_plus.
    - iPureIntro. by apply TRdup_max.
    - by iApply (TRdup_nmax_absurd with "Hinv").
    - iIntros (v n). by iApply (tock_spec_simple with "Hinv").
  Qed.

End TockSpec.



(*
 * Simulation
 *)

Section Soundness.

  Definition adequate_trtranslation__adequate := adequate_translation__adequate loop.

  (* derive the adequacy of the translated program from a Hoare triple in Iris. *)

  Lemma spec_trtranslation__adequate_translation {Σ} nmax ψ e :
    (0 < nmax)%nat →
    (∀ `{timeReceiptHeapG Σ},
      TR_invariant nmax -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜ψ v⌝ }}}
    ) →
    ∀ `{timeReceiptHeapPreG Σ} `{TickCounter} σ, adequate NotStuck «e» S«σ,nmax-1» ψ.
  Proof.
    intros Inmax Hspec HpreG Hloc σ.
    (* apply the adequacy results. *)
    apply (wp_adequacy _ _) ; simpl ; intros HinvG.
    (* … now we have to prove a WP. *)
    set σ' := S«σ».
    (* allocate the heap, including cell ℓ (on which we need to keep an eye): *)
    iMod (own_alloc (● to_gen_heap (<[ℓ := #(nmax-1)%nat]> σ') ⋅ ◯ to_gen_heap {[ℓ := #(nmax-1)%nat]}))
      as (h) "[Hh● Hℓ◯]".
    {
      apply auth_valid_discrete_2 ; split.
      - rewrite - insert_delete ; set σ'' := delete ℓ σ'.
        unfold to_gen_heap ; rewrite 2! fmap_insert fmap_empty insert_empty.
        exists (to_gen_heap σ'').
        rewrite (@gmap.insert_singleton_op _ _ _ _ (to_gen_heap σ'')) //.
        rewrite lookup_fmap ; apply fmap_None, lookup_delete.
      - apply to_gen_heap_valid.
    }
    (* allocate the ghost state associated with ℓ: *)
    iMod (auth_nat_alloc 0) as (γ1) "[Hγ1● _]".
    iMod (auth_mnat_alloc 0) as (γ2) "[Hγ2● _]".
    (* packing all those bits, build the heap instance necessary to use time credits: *)
    pose (Build_timeReceiptHeapG Σ (HeapG Σ _ (GenHeapG _ _ Σ _ _ _ h)) _ _ _ γ1 γ2)
      as HtrHeapG.
    (* create the invariant: *)
    iAssert (|={⊤}=> TR_invariant nmax)%I with "[Hℓ◯ Hγ1● Hγ2●]" as "> Hinv".
    {
      iApply inv_alloc.
      iExists 0%nat. rewrite (_ : nmax - 0 - 1 = Z.of_nat (nmax - 1)) ; last lia.
      unfold mapsto ; destruct mapsto_aux as [_ ->] ; simpl.
      unfold to_gen_heap ; rewrite fmap_insert fmap_empty insert_empty.
      by iFrame.
    }
    iModIntro.
    (* finally, use the user-given specification: *)
    iExists gen_heap_ctx. iFrame "Hh●".
    iApply (Hspec with "Hinv") ; auto.
  Qed.

  Theorem spec_trtranslation__adequate {Σ} nmax φ e :
    (0 < nmax)%nat →
    is_closed [] e →
    (∀ `{timeReceiptHeapG Σ},
      TR_invariant nmax -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ `{!timeReceiptHeapPreG Σ} σ,
      nadequate NotStuck (nmax-1) e σ φ.
  Proof.
    intros Inmax Hclosed Hspec HpreG σ.
    eapply adequate_trtranslation__adequate ; first done.
    intros Hloc. by eapply spec_trtranslation__adequate_translation.
  Qed.

  Theorem abstract_spec_trtranslation__adequate {Σ} nmax φ e :
    (0 < nmax)%nat →
    is_closed [] e →
    (∀ `{heapG Σ} (TR TRdup : nat → iProp Σ) (tock : val),
      let _ := {| Translation.tick := tock |} in
      TR_interface nmax TR TRdup tock -∗
      {{{ True }}} «e» {{{ v, RET v ; ⌜φ (invtranslationV v)⌝ }}}
    ) →
    ∀ {_ : timeReceiptHeapPreG Σ} σ,
      nadequate NotStuck (nmax-1) e σ φ.
  Proof.
    intros Inmax Hclosed Hspec HpreG σ.
    eapply spec_trtranslation__adequate ; try done.
    clear HpreG. iIntros (HtrHeapG) "#Hinv".
    iApply Hspec. by iApply TR_implementation.
  Qed.

End Soundness.



(*
 * Proof-mode tactics for proving WP of translated expressions
 *)

Section Tactics.

  (* TODO *)

End Tactics.

Ltac wp_tock :=
  idtac.