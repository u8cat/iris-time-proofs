From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksStep.

(* In this file, we complete the construction of thunks. By combining the
   results in ThunksBase.v and ThunksStep.v, we are able to define a predicate
   [Thunk] which which satisfies the common API in ThunksAPI.v and also has
   the creation rule and the consequence rule. *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section Full.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Implicit Type p : na_inv_pool_name.
Implicit Type T : namespace.
Implicit Type E F : coPset.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.
Implicit Type f v : val.

(* -------------------------------------------------------------------------- *)

(* The definition of the predicate [Thunk] is essentially an iterated
   application of [ProxyThunk] over [BasicThunk]. The application is
   repeated a number of times, [d], which is then existentially quantified:
   this allows us to prove that it supports both the creation rule and the
   consequence rule. *)

Fixpoint Thunk_rec d p F t n R φ : iProp :=
  match d with
  | 0 => BaseThunk p F t n R φ
  | S d' => ProxyThunk (Thunk_rec d') p F t n R φ
  end.

Definition Thunk p F t n R φ : iProp :=
  ∃ T d, ⌜ ↑T ⊆ F ⌝ ∗ Thunk_rec d p (F ∖ ↑T) t n R φ.

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_thunk :=
  iDestruct "Hthunk" as (T d) "(%HTF & #Hthunk)".

Local Ltac pure_conjunct :=
  iSplitR; [ iPureIntro; eauto |].

(* -------------------------------------------------------------------------- *)

(* The predicates [Thunk_rec] and [Thunk] satisfy the common thunk API. *)

Instance thunk_rec_api d :
  CommonThunkAPI (Thunk_rec d).
Proof. induction d; tc_solve. Qed.

Global Instance thunk_api :
  CommonThunkAPI Thunk.
Proof.
  constructor; intros.

  { tc_solve. (* persistent *) }

  { solve_proper. (* thunk_proper *) }

  { (* thunk_ne *)
    unfold Thunk. intros ??????. do 5 f_equiv. by apply thunk_ne. }

  { solve_contractive. (* thunk_contractive *) }

  { (* thunk_mask_subseteq *)
    iIntros "#Hthunk". destruct_thunk.
    iExists T, _. pure_conjunct; [set_solver|]. iApply thunk_mask_subseteq; [|done]. set_solver. }

  { (* thunk_increase_debt *)
    iIntros "#Hthunk". destruct_thunk.
    iExists _, _. pure_conjunct. by iApply thunk_increase_debt. }

  { (* thunk_force *)
    iIntros "#Htickinv" (Φ) "!> (Hcredits & #Hthunk & Hp & HR) Post". destruct_thunk.
    iApply (thunk_force with "Htickinv [$Hcredits $Hthunk $Hp $ HR] Post"). set_solver. }

  { (* thunk_pay *)
    iIntros "#Hthunk Hk". destruct_thunk. iExists T, d. pure_conjunct.
    by iApply (thunk_pay with "Hthunk Hk"). }
Qed.

(* -------------------------------------------------------------------------- *)

(* A public reasoning rule: the construction of a thunk. *)

Lemma thunk_create p T F nc R φ f :
  ↑T ⊆ F →
  TC_invariant -∗
  {{{ TC Tcr ∗ isAction f nc R φ }}}
    «create f»
  {{{ t, RET «#t» ; Thunk p F t nc R φ }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!> [Htc Hf] Post".
  (* Allocate a base thunk. *)
  iApply (base_thunk_create p (T.@1) with "Htickinv [$Htc $Hf]").
  { reflexivity. }
  iIntros "!>" (t) "Hthunk".
  iApply "Post".
  (* Wrap this base thunk as a Thunk. *)
  iExists (T.@0), 0. iSplit; [solve_ndisj|].
  iApply (thunk_mask_subseteq (Thunk:=Thunk_rec _)); [|done]. solve_ndisj.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public reasoning rule: the consequence rule. *)

Lemma thunk_consequence E p F t n1 n2 R φ ψ :
  Thunk p F t n1 R φ -∗
  isUpdate n2 R φ ψ ={E}=∗
  Thunk p F t (n1 + n2) R ψ.
Proof.
  iIntros "#Hthunk Hupdate". destruct_thunk.
  (* Wrap this thunk into a fresh ghost thunk. *)
  iMod (proxythunk_consequence (T.@1) with "Hthunk Hupdate") as "Hthunk'".
  { reflexivity. }
  { solve_ndisj. }
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  iModIntro.
  (* Pack existentials. *)
  iExists (T.@0), (S d). iSplit; [solve_ndisj|].
  iApply (thunk_mask_subseteq (Thunk:=Thunk_rec _)); [|done]. solve_ndisj.
Qed.

End Full.
