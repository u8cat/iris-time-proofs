From iris.heap_lang Require Import proofmode notation adequacy.
From iris.algebra Require Import auth.
From iris.base_logic Require Import invariants.
From stdpp Require Import namespaces.

Require Import Auth_nat Auth_mnat.

Section Thunk.

(*
  Context `{heapG Σ}.
  Context { TC : nat → iProp Σ }.
  Context { tick : val }.
  Context `{ ∀ m n, TC (m+n) ≡ (TC m ∗ TC n)%I }.
  Context `{ ∀ n, Timeless (TC n) }.
  Context `{ ∀ (v : val), {{{ TC 1 }}} tick v {{{ RET v ; True }}} }.
*)

  Require Import TimeCredits.
  Context `{timeCreditHeapG Σ}.
  Context `{inG Σ (authR mnatUR)}.

(** Notations for thunks *)
Notation UNEVALUATED f := (InjL f%V) (only parsing).
Notation EVALUATING := (InjR (InjL #())) (only parsing).
Notation EVALUATED v := (InjR (InjR v%V)) (only parsing).
Notation UNEVALUATEDV f := (InjLV f%E) (only parsing).
Notation EVALUATINGV := (InjRV (InjLV #())) (only parsing).
Notation EVALUATEDV v := (InjRV (InjRV v%V)) (only parsing).
Notation "'match:' e0 'with' 'UNEVALUATED' x1 => e1 | 'EVALUATING' => e2 | 'EVALUATED' x3 => e3 'end'" :=
  (Match e0 x1%bind e1 x3%bind (Match x3%bind BAnon e2 x3%bind e3)) (* hackish! *)
  (e0, e1, e2, x3, e3 at level 200, only parsing) : expr_scope.
(** /notations *)

From iris.base_logic Require Import invariants.
  Definition thunkN (t : loc) := nroot .@ "thunk" .@ string_of_pos t.

From iris.algebra Require Import excl cmra.
  Definition token := Excl ().
  Context `{inG Σ (exclR unitC)}.

  Definition ThunkInv (t : loc) (γ γtok : gname) (nc : nat) (φ : val → iProp Σ) : iProp Σ := (
    ∃ (ac : nat),
        own γ (●mnat ac)
      ∗ (
          (∃ (f : val),
              t ↦ UNEVALUATEDV f
            ∗ {{{ TC nc }}} f #() {{{ v, RET v ; φ v }}}
            ∗ TC ac
            ∗ own γtok token
          )
        ∨ (   t ↦ EVALUATINGV
            ∗ ⌜(ac ≥ nc)%nat⌝
          )
        ∨ (∃ (v : val),
              t ↦ EVALUATEDV v
            ∗ φ v
            ∗ ⌜(ac ≥ nc)%nat⌝
            ∗ own γtok token
          )
        )
  )%I.
  Definition Thunk (t : loc) (n : nat) (φ : val → iProp Σ) : iProp Σ := (
    ∃ (γ γtok : gname) (nc : nat),
        inv (thunkN t) (ThunkInv t γ γtok nc φ)
      ∗ own γ (◯mnat (nc-n))
  )%I.


  Lemma own_auth_mnat_weaken (γ : gname) (n₁ n₂ : mnat) :
    (n₁ ≥ n₂)%nat →
    own γ (◯mnat n₁) -∗
    own γ (◯mnat n₂).
  Proof.
    iIntros (I) "H".
    rewrite (_ : n₁ = n₁ `max` n₂)%nat ; last (by rewrite max_l).
    iDestruct "H" as "[_$]".
  Qed.
  Global Arguments own_auth_mnat_weaken _ (_ _ _)%nat_scope.
  Lemma Thunk_weaken (t : loc) (n₁ n₂ : nat) (φ : val → iProp Σ) :
    (n₁ ≤ n₂)%nat →
    Thunk t n₁ φ -∗
    Thunk t n₂ φ.
  Proof.
    iIntros (I) "H". iDestruct "H" as (γ γtok nc) "[Hinv Hγ◯]".
    iExists (γ), (γtok), (nc). iFrame "Hinv".
    iDestruct (own_auth_mnat_weaken _ (nc-n₁)%nat (nc-n₂)%nat with "Hγ◯") as "$" ; first lia.
  Qed.

  Lemma TC_weaken (n₁ n₂ : nat) :
    (n₁ ≥ n₂)%nat →
    TC n₁ -∗ TC n₂.
  Admitted.

  Definition create : val :=
    λ: "f",
      ref (UNEVALUATED "f").

  Definition force : val :=
    rec: "force" "t" :=
      match: ! "t" with
        UNEVALUATED "f" =>
          if: CAS "t" (UNEVALUATED "f") EVALUATING then
            let: "v" := "f" #() in
            if: CAS "t" EVALUATING (EVALUATED "v") then
              "v"
            else
              #() #() (* will not happen *)
          else
            "force" "t"
      | EVALUATING =>
          "force" "t"
      | EVALUATED "v" =>
          "v"
      end.

Lemma zero_TC :
  TICKCTXT ={⊤}=∗ TC 0.
Proof.
  iIntros "#Htickinv".
  iInv timeCreditN as (m) ">[Hcounter H●]" "Hclose".
  iDestruct (own_auth_nat_null with "H●") as "[H● $]".
  iApply "Hclose" ; eauto with iFrame.
Qed.

  Lemma auth_mnat_alloc `{inG Σ (authR natUR)} (n : mnat) :
    (|==> ∃ γ, own γ (●mnat n) ∗ own γ (◯mnat n))%I.
  Proof.
    by iMod (own_alloc (●mnat n ⋅ ◯mnat n)) as (γ) "[? ?]" ; auto with iFrame.
  Qed.
  Global Arguments auth_mnat_alloc {_} n%nat.

  Lemma create_spec (E : coPset) (f : val) (nc : nat) (φ : val → iProp Σ) :
    TICKCTXT -∗
    {{{ ( {{{ TC nc }}} f #() {{{ v, RET v ; φ v }}} ) }}}
    create f
    {{{ (t : loc), RET #t ; |={E}=> Thunk t nc φ }}}.
  Proof.
    iIntros "#Htickinv" (Φ) "!# Hf Post".
    iDestruct (zero_TC with "Htickinv") as ">Htc0".
    iMod (auth_mnat_alloc 0) as (γ) "[Hγ● Hγ◯]".
    iMod (own_alloc token) as (γtok) "Htok" ; first done.
    wp_lam. wp_alloc t.
    iApply "Post".
    iExists (γ), (γtok), (nc) ; rewrite (_ : nc - nc = 0)%nat ; last lia.
    iFrame "Hγ◯".
    iApply inv_alloc.
    iExists (0%nat). iFrame "Hγ●".
    iLeft. auto with iFrame.
  Qed.

  Lemma own_auth_mnat_le `{inG Σ (authR natUR)} (γ : gname) (m n : mnat) :
    own γ (●mnat m) -∗
    own γ (◯mnat n) -∗
    ⌜(n ≤ m)%nat⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as % [[k ->] _] % auth_valid_discrete_2.
    iPureIntro. apply Max.le_max_l.
  Qed.

  Lemma own_token_excl (γ : gname) :
    own γ token -∗
    own γ token -∗
    False.
  Admitted.

  Lemma force_spec t φ :
    (∀ (v : val), φ v -∗ φ v ∗ φ v) →
    TICKCTXT -∗
    {{{ Thunk t 0 φ }}}
    force #t
    {{{ v, RET v ; φ v }}}.
  Proof.
    iIntros (Hφdup).
    iIntros "#Htickinv" (Φ) "!# #Hthunk Post".
    iLöb as "IH".
    iDestruct "Hthunk" as (γ γtok nc) "#[Hthunkinv Hγ◯]".
    rewrite (_ : nc - 0 = nc)%nat ; last lia.
    wp_rec.
    (* reading the thunk… *)
    wp_bind (! _)%E ;
    iInv (thunkN t) as (ac) "(Hγ● & [ Hunevaluated | [ Hevaluating | Hevaluated ]])" "Hclose" ;
    [ iDestruct "Hunevaluated" as (f) "(>Ht & #Hf & >Htc & >Htok)"
    | iDestruct "Hevaluating" as "(>Ht & >%)"
    | iDestruct "Hevaluated" as (v) "(>Ht & Hv & >% & >Htok)" ].
    (* (1) if it is UNEVALUATED, we evaluate it: *)
    {
      wp_load.
      iMod ("Hclose" with "[Ht Hf Htc Hγ● Htok]") as "_" ;
        [ iExists (ac) ; iFrame "Hγ●" ; iLeft ; by auto with iFrame | iModIntro ].
      clear ac.
      (* trying to set the thunk to EVALUATING… *)
      wp_match.
      wp_bind (CAS _ _ _)%E ;
      iInv (thunkN t) as (ac') "(Hγ●' & [ Hunevaluated | [ Hevaluating | Hevaluated ]])" "Hclose" ;
      [ iDestruct "Hunevaluated" as (f') "(>Ht' & Hf' & >Htc' & >Htok')"
      | iDestruct "Hevaluating" as "(>Ht & >%)"
      | iDestruct "Hevaluated" as (v) "(>Ht & Hv & >% & >Htok')" ].
      (* (1.1) if at that moment it was still UNEVALUATED, then the CAS succeeds
       * and we proceed on evaluating f: *)
      {
        (* in fact, the CAS succeeds only if f = f'. Otherwise, we proceed to
         * a recursive call (but this is not supposed to happen). *)
        destruct (decide (f = f')) as [ <- | FF ] ; cycle 1.
        {
          wp_cas_fail.
          iMod ("Hclose" with "[-Post]") as "_" ;
            [ iExists (ac') ; iFrame "Hγ●'" ; iLeft ; by auto with iFrame | iModIntro ].
          wp_if.
          wp_apply ("IH" with "Post").
        }
        wp_cas_suc.
        iDestruct (own_auth_mnat_le with "Hγ●' Hγ◯") as %I.
        iDestruct (TC_weaken _ _ I with "Htc'") as "Htc".
        iMod ("Hclose" with "[Ht' Hγ●']") as "_" ;
          [ iExists (ac') ; iFrame "Hγ●'" ; iRight ; iLeft ; by iFrame | iModIntro ].
        wp_if.
        wp_apply ("Hf" with "Htc") ; iIntros (v) "Hv".
        wp_let.
        (* trying to set the location to EVALUATED with the value computed… *)
        wp_bind (CAS _ _ _)%E ;
        iInv (thunkN t) as (ac'') "(Hγ●'' & [ Hunevaluated | [ Hevaluating | Hevaluated ]])" "Hclose" ;
        [ iDestruct "Hunevaluated" as (f'') "(_ & _ & _ & >Htok'')" ; clear f''
        | iDestruct "Hevaluating" as "(>Ht & >%)"
        | iDestruct "Hevaluated" as (v'') "(_ & _ & _ & >Htok'')" ; clear v'' ].
        (* (1.1.1) if at that third moment it was UNEVALUATED, then this is
         * absurd because we took control of the thunk when we started
         * evaluating it: *)
        {
          iExFalso. iApply (own_token_excl with "Htok' Htok''").
        }
        (* (1.1.2) if at that third moment it was still EVALUATING, then the CAS
         * succeeds and we are done: *)
        {
          wp_cas_suc.
          iDestruct (Hφdup with "Hv") as "[Hv Hv_dup]".
          iMod ("Hclose" with "[Ht Hv Hγ●'' Htok']") as "_" ;
            [iExists (ac'') ; iFrame "Hγ●''" ; iRight ; iRight ; by auto with iFrame | iModIntro ].
          wp_if.
          by iApply ("Post" with "Hv_dup").
        }
        (* (1.1.3) if at that third moment it was EVALUATED, then this is
         * absurd because we took control of the thunk when we started
         * evaluating it: *)
        {
          iExFalso. iApply (own_token_excl with "Htok' Htok''").
        }
      }
      (* (1.2) if at that moment it was EVALUATING, then the CAS fails and we
       * proceed to a recursive call (waiting loop): *)
      {
        wp_cas_fail.
        iMod ("Hclose" with "[-Post]") as "_" ;
          [ iExists (ac') ; iFrame "Hγ●'" ; iRight ; iLeft ; by auto with iFrame | iModIntro ].
        wp_if.
        wp_apply ("IH" with "Post").
      }
      (* (1.3) if at that moment it was EVALUATED, then the CAS fails and we
       * proceed to a recursive call (waiting loop): *)
      {
        wp_cas_fail.
        iMod ("Hclose" with "[-Post]") as "_" ;
          [ iExists (ac') ; iFrame "Hγ●'" ; iRight ; iRight ; by auto with iFrame | iModIntro ].
        wp_if.
        wp_apply ("IH" with "Post").
      }
    }
    (* (2) if it is EVALUATING, we proceed to a recursive call (waiting loop): *)
    {
      wp_load.
      iMod ("Hclose" with "[-Post]") as "_" ;
        [ iExists (ac) ; iFrame "Hγ●" ; iRight ; iLeft ; by auto with iFrame | iModIntro ].
      wp_match. wp_match.
      wp_apply ("IH" with "Post").
    }
    (* (3) if it is EVALUATED, we get the result which is already memoized: *)
    {
      iDestruct (Hφdup with "Hv") as "[Hv Hv_dup]".
      wp_load.
      iMod ("Hclose" with "[Ht Hv Hγ● Htok]") as "_" ;
        [ iExists (ac) ; iFrame "Hγ●" ; iRight ; iRight ; by auto with iFrame | iModIntro ].
      wp_match. wp_match.
      iApply ("Post" with "Hv_dup").
    }
  Qed.

  Lemma auth_mnat_update_incr' (γ : gname) (m n k : mnat) :
    own γ (●mnat m) -∗
    own γ (◯mnat n) -∗
    |==> own γ (●mnat (m + k : mnat)) ∗ own γ (◯mnat (n + k : mnat)).
  Proof.
    iIntros "H● H◯".
    iDestruct (own_auth_mnat_le with "H● H◯") as %I. iClear "H◯".
    iDestruct (auth_mnat_update_incr _ _ k with "H●") as ">H●".
    iDestruct (auth_mnat_update_read_auth with "H●") as ">[$ H◯]".
    iModIntro.
    rewrite (_ : m + k = (n + k) `max` (m + k))%nat ; last lia.
    iDestruct "H◯" as "[$ _]".
  Qed.
  Global Arguments auth_mnat_update_incr' _ (_ _ _)%nat_scope.

  Lemma pay_spec (E : coPset) (n k : nat) (t : loc) (φ : val → iProp Σ) :
    ↑thunkN t ⊆ E →
    Thunk t n φ -∗ TC k ={E}=∗ Thunk t (n-k) φ.
  Proof.
    iIntros (?) "#Hthunk Htc_k".
    iDestruct "Hthunk" as (γ γtok nc) "[#Hthunkinv Hγ◯]".
    (* reasoning by case analysis on the state of the thunk… *)
    iInv (thunkN t) as (ac) "(Hγ● & [ Hunevaluated | [ Hevaluating | Hevaluated ]])" "Hclose" ;
    [ iDestruct "Hunevaluated" as (f) "(>Ht & #Hf & >Htc & >Htok)"
    | iDestruct "Hevaluating" as "(>Ht & >%)"
    | iDestruct "Hevaluated" as (v) "(>Ht & Hv & >% & >Htok)" ].
    (* (1) if it is UNEVALUATED, then we add the time credits to the deposit: *)
    {
      iAssert (TC (ac + k)) with "[Htc Htc_k]" as "Htc" ;
        first by iSplitL "Htc".
      iDestruct (auth_mnat_update_incr' _ _ _ k with "Hγ● Hγ◯") as ">[Hγ●' Hγ◯']".
      iMod ("Hclose" with "[-Hγ◯']") as "_" ;
        [ iLeft ; by auto with iFrame | iModIntro ].
      iExists (γ) ; iExists (nc). iFrame "Hthunkinv".
      destruct (decide (n ≤ nc)) ;
      destruct (decide (k ≤ n)) ;
      iDestruct (own_auth_mnat_weaken _ ((nc-n)+k) (nc-(n-k)) with "Hγ◯'") as "$" ; lia.
    }
    (* (2) if it is EVALUATING, then we do nothing: *)
    {
      
      iMod ("Hclose" with "[-Hγ◯]") as "_" ;
        [ iRight ; iLeft ; by auto with iFrame | iModIntro ].
      iExists (γ) ; iExists (nc).
      eauto with iFrame.
    }
    (* (2) if it is EVALUATED, then we do nothing: *)
    {
    }
  Admitted.

  Lemma thunk_dup ℓ n φ :
    (Thunk ℓ n φ ≡ Thunk ℓ n φ ∗ Thunk ℓ n φ)%I.
  Admitted.

End Thunk.