From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksFull.

Section Examples.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Implicit Type t : loc.

(* -------------------------------------------------------------------------- *)

(* Creating a thunk that forces a thunk: *)

Lemma create_thunk_forcing_thunk p N1 F2 t2 n2 R φ :
  TC_invariant -∗
  {{{ TC 3 ∗ Thunk p F2 t2 n2 R φ }}}
    « create (λ: <>, force #t2)%V »
  {{{ t1, RET #t1 ;
      Thunk p (↑N1) t1 (12+n2) (ThunkToken p F2 ∗ R)
            (λ v, ThunkVal t2 v ∗ □ φ v)
  }}}.
Proof.
  iIntros "#Htickinv" (?) "!> [Htc #Ht2] Post".
  (* Pay 3 credits to create the thunk [t1]. *)
  wp_apply (thunk_create with "Htickinv [$Htc Ht2] Post"); [ done |].
  (* Reason about the action. *)
  unfold isAction.
  iIntros "[Htok2 HR] [Htc12 Htcn2]" (Ψ) "Post".
  (* Entering the function costs 1 credit. *)
  wp_tick_lam.
  (* We have [n2 + 11] credits left, *)
  iCombine "Htcn2"  "Htc12" as "Htc".
  (* which can use to force the thunk [t2]. *)
  iApply (thunk_pay_force with "Htickinv [$Htc $Ht2 $Htok2 $HR]"); [ done |].
  iNext.
  iIntros (v) "(#Hφ & #Hval2 & Htok2 & HR)".
  by iApply ("Post" with "[$] [$]").
Qed.

End Examples.
