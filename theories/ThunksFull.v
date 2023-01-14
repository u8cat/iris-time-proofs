From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksStep.

(* -------------------------------------------------------------------------- *)

Section Full.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type E F : coPset.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.
Implicit Type f v : val.

Definition Thunk p F t n R φ : iProp :=
  ∃ SomeThunk,
  ∃ (_ : ∀ p F t n R φ, Persistent (SomeThunk p F t n R φ)),
  ∃ (_ : BasicThunkAPI SomeThunk),
  ∃ N d F',
  ⌜ ∀ d', d < d' → F' ## ↑(N .@ d') ⌝ ∗
  ⌜ F' ⊆ ↑N ⊆ F ⌝ ∗
  SomeThunk p F' t n R φ.

Local Ltac destruct_thunk :=
  iDestruct "Hthunk" as (SomeThunk ? ? N d F'') "(%Hroom & (%HF''N & %HNF) & #Hthunk)".

Local Ltac pure_conjunct :=
  iSplitR; [ iPureIntro; eauto |].

Global Instance thunk_persistent p F t n R φ :
  Persistent (Thunk p F t n R φ).
Proof.
  exact _.
Qed.

Lemma thunk_create p N F nc R φ f :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 3 ∗ isAction f nc R φ }}}
    «create f»
  {{{ t, RET #t ; Thunk p F t nc R φ }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!> [Htc Hf] Post".
  (* Allocate a base thunk. *)
  iApply (base_thunk_create p (N .@ 0) with "Htickinv [$Htc $Hf]").
  { reflexivity. }
  iNext. iIntros (t) "Hthunk".
  iApply "Post".
  (* Wrap this base thunk as a Thunk. *)
  iExists BaseThunk, _, _.
  iExists N, 0, (↑(N .@ 0)).
  repeat pure_conjunct.
  { intros. assert (0 ≠ d') by lia. eauto with ndisj. }
  { eauto with ndisj. }
  eauto with iFrame.
Qed.

Lemma thunk_consequence E p F t n1 n2 n R φ ψ :
  TC 0 -∗ (* TODO get rid of this? *)
  Thunk p F t n1 R φ -∗
  (∀ v, R -∗ TC n2 -∗ □ φ v ={⊤}=∗ R ∗ □ ψ v) ={E}=∗
  Thunk p F t (n1 + n2) R ψ.
Proof.
  iIntros "Htc #Hthunk Hupdate".
  destruct_thunk.
  (* Wrap this thunk into a fresh ghost thunk. *)
  iMod (thunkstep_consequence (N .@ (d+1)) with "Htc Hthunk Hupdate")
    as "Hthunk'".
  { reflexivity. }
  { eauto with lia. }
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  iModIntro.
  (* Pack existentials. *)
  iExists ThunkStep, _, _.
  iExists N, (d+1), _.
  iFrame "Hthunk".
  iPureIntro; split.
  { intros. assert (d' ≠ d + 1) by lia.
    eapply disjoint_union_l; eauto with lia ndisj. }
  { eauto using namespaces.coPset_union_least with ndisj. }
Qed.

Global Instance full_thunk_api :
  BasicThunkAPI Thunk.
Proof.
  constructor; intros.

  { (* thunk_increase_debt *)
    iIntros "Hthunk".
    destruct_thunk.
    iPoseProof (thunk_increase_debt with "Hthunk") as "Hthunk'"; [ done |].
    iClear "Hthunk".
    iExists SomeThunk, _, _.
    iExists _, _, _.
    eauto. }

  { (* thunk_force *)
    iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Hp & HR) Post".
    destruct_thunk.
    iApply (thunk_force with "Htickinv [$Hcredits $Hthunk $Hp $HR]").
    { set_solver. }
    done. }

  { (* thunk_force_forced_weak *)
    iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Hp & HR) Post".
    destruct_thunk.
    iApply (thunk_force_forced_weak with "Htickinv [$Hcredits $Hthunk $Hp $HR]").
    { set_solver. }
    done. }

  { (* thunk_pay *)
    iIntros "Htoken #Hthunk Hk".
    destruct_thunk.
    iMod (thunk_pay with "Htoken Hthunk Hk") as "(Htoken & Hthunk')".
    { set_solver. }
    { set_solver. }
    iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
    iFrame "Htoken".
    iModIntro.
    (* Pack existentials. *)
    iExists SomeThunk, _, _.
    iExists _, _, _.
    iFrame "Hthunk".
    eauto. }

Qed.

End Full.
