From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksFull.
From iris_time Require Import Generations.
Open Scope nat_scope.

(* This file offers a theory of thunks indexed with integer heights.
   It is built on top of ThunksFull, which offers a more low-level theory
   of thunks indexed with masks. *)

(* In both cases, this discipline aims to prevent the construction of cyclic
   thunks. The main idea is that a thunk is allowed to force a thunk at a
   lower height. It is *not* allowed to force a thunk at the same height or
   higher. A thunk is allowed to *construct* a thunk at an arbitrary height.  *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section HThunks.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Definition height := generation.

Implicit Type p : na_inv_pool_name.
Implicit Type t : loc.
Implicit Type h : height.
Implicit Type n : nat.
Implicit Type φ : val → iProp.

(* -------------------------------------------------------------------------- *)

(* The token associated with a pool [p] and bound [b]. *)

Definition HToken p b :=
  na_own p (gens_below_bound b).

(* This lemma allocates a new pool together with its token, which controls
   all heights in this pool. *)

Lemma gtoken_alloc :
  ⊢ |==> ∃ p, HToken p None.
Proof using.
    iApply na_alloc.
  Qed.

(* -------------------------------------------------------------------------- *)

(* The existing predicate [Thunk] is parameterized with a resource [R], which
   is passed to the suspended computation, and must be preserved by it. Thus,
   forcing a thunk requires the conjunction of the token [ThunkToken p F] and
   of the resource [R]. Thus, [ThunkToken p F] and [R] must be separate. *)

(* When a thunk [t] must force another thunk [t'], this implies that the token
   that controls [t] and the token that controls [t'] must be separate. For an
   end user, setting up these tokens in a suitable way can be tricky. In this
   file, we provide a simple discipline that removes most of this burden from
   the end user. *)

(* The idea is simple: we index thunks with integer heights, and we allow
   a thunk to force a thunk at a lower height only. *)

(* To do so, we use a thunk whose parameters [F] and [R] are instantiated in
   such a way that the tokens [ThunkToken p F] and [R] are disjoint. [F] is
   instantiated with [↑(gen_ns h')], that is, control over the height [h']
   only. [R] is instantiated with [HToken p (Some h')], that is, control over
   all heights below [h']. *)

(* An existential quantification over [h'], with the constraint [h' ≤ h],
   ensures that [HThunk] is covariant in [h]. *)

(* We could keep a parameterization in [R], so as to allow our thunks to have
   visible side effects (that is, side effects that require a token). We have
   not yet felt the need to do so; so, for the moment, a thunk is not allowed
   to have visible side effects other than forcing other thunks. *)

Definition HThunk p h t n φ : iProp :=
  ∃ h', ⌜ h' ≤ h ⌝ ∗
  let F := ↑(gen_ns h') in
  let R := HToken p (Some h') in
  Thunk p F t n R φ.

(* -------------------------------------------------------------------------- *)

(* Local tactics. *)

Local Ltac deconstruct_thunk :=
  iDestruct "Hthunk" as (h') "(% & Hthunk)".

Local Ltac construct_thunk h' :=
  iExists h'; iSplitR; [ eauto with lia |].

Local Ltac construct_texan_triple ipat :=
  iIntros "#?"; (* introduce TC_invariant *)
  iIntros (Φ) "!>";
  iIntros ipat;
  iIntros "Post".

(* -------------------------------------------------------------------------- *)

(* [HThunk] is persistent. *)

Global Instance hthunk_persistent p h t n φ :
  Persistent (HThunk p h t n φ).
Proof using.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

(* The creation rule passes the token [HToken p (Some h)] to the suspended
   computation [f]. Thus, the newly created thunk, which lies at height [h],
   can force thunks at heights less than [h]. *)

(* There is no restriction regarding the thunks that this new thunk may
   construct. Indeed, the postcondition [φ] is arbitrary. *)

Lemma hthunk_create p h n φ f :
  let token := HToken p (Some h) in
  TC_invariant -∗
  {{{ TC 3 ∗ isAction f n token φ }}}
    « create f »
  {{{ t, RET «#t» ; HThunk p h t n φ }}}.
Proof.
  intro. construct_texan_triple "H".
  wp_apply (thunk_create with "[$] H"); [ done |].
  iIntros (t) "Hthunk".
  iApply "Post". construct_thunk h. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* The consequence rule is standard. *)

Lemma hthunk_consequence p h t n1 n2 φ ψ E :
  (∀ v, TC n2 -∗ □ φ v ={⊤}=∗ □ ψ v) -∗
  HThunk p h t  n1       φ  ={E}=∗
  HThunk p h t (n1 + n2) ψ.
Proof.
  iIntros "Hupdate Hthunk".
  deconstruct_thunk.
  iMod (thunk_consequence with "Hthunk [Hupdate]").
  { (* The token [HToken p (Some h')] is not passed to the update,
       because it would be essentially useless, as [h'] is unknown. *)
    iIntros (v) "$ Htc Hv".
    iApply ("Hupdate" with "Htc").
    iAssumption. }
  iModIntro. construct_thunk h'. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* [HThunk] is covariant in the parameter [h]. That is, it is safe to view a
   thunk at a low height as a thunk at a greater height. This makes this thunk
   more difficult to force, as a stronger token is required. *)

Lemma hthunk_covariant_in_h p h1 h2 t n φ :
  h1 ≤ h2 →
  HThunk p h1 t n φ -∗
  HThunk p h2 t n φ.
Proof.
  iIntros (?) "Hthunk".
  deconstruct_thunk.
  construct_thunk h'.
  done.
Qed.

(* -------------------------------------------------------------------------- *)

(* [HThunk] is covariant in the parameter [n]. That is, it is safe to view a
   thunk with a small debt as a thunk with a greater debt. *)

Lemma hthunk_increase_debt p h t n1 n2 φ :
  n1 ≤ n2 →
  HThunk p h t n1 φ -∗
  HThunk p h t n2 φ.
Proof using.
  iIntros (?) "Hthunk".
  deconstruct_thunk.
  construct_thunk h'.
  by iApply thunk_increase_debt.
Qed.

(* -------------------------------------------------------------------------- *)

(* Forcing a thunk at height [h] that lies below the bound [b] requires the
   token [HToken p b]. *)

(* To solve the proof obligation [lies_below h b], use [eauto with thunks].   *)

(* The thunk must have zero debit. If it has more than zero debit, then [pay]
   and [force] must be composed; see [hthunk_pay_force] below. *)

Lemma hthunk_force p h b t φ :
  lies_below h b →
  let token := HToken p b in
  TC_invariant -∗
  {{{ TC 11 ∗ HThunk p h t 0 φ ∗ token }}}
    « force #t »
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ token }}}.
Proof using.
  intros Hh ?. construct_texan_triple "(Htc & Hthunk & Htoken)".
  deconstruct_thunk.
  assert (Hh': lies_below h' b) by eauto using leq_lies_below.
  rewrite /token /HToken (carve_out_gens_below_gen _ _ Hh').
  iDestruct (na_own_union with "Htoken") as "[Htoken1 Htoken2]".
  { set_solver. }
  (* Both tokens are required here. *)
  wp_apply (thunk_force with "[$] [$Htc $Hthunk $Htoken2 $Htoken1]").
  { eauto using gen_ns_subseteq_interval. }
  (* Conclude. *)
  iIntros (v) "(#Hv & #Hval & Htoken1 & Htoken2)".
  iApply "Post". iFrame "Hv Hval".
  iDestruct (na_own_union with "[$Htoken2 $Htoken1]") as "Htoken".
  { set_solver. }
  iFrame "Htoken".
Qed.

(* -------------------------------------------------------------------------- *)

(* Paying. *)

Lemma hthunk_pay k E p h t n φ :
  ↑ThunkPayment ⊆ E →
  HThunk p h t n φ -∗ TC k
    ={E}=∗
  HThunk p h t (n-k) φ.
Proof using.
  iIntros (?) "Hthunk Htc".
  deconstruct_thunk.
  iMod (thunk_pay with "Hthunk Htc"); [ done |].
  iModIntro. construct_thunk h'. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* The composition of [pay] and [force]. *)

Lemma hthunk_pay_force p h b t d φ :
  lies_below h b →
  let token := HToken p b in
  TC_invariant -∗
  {{{ TC (11 + d) ∗ HThunk p h t d φ ∗ token }}}
    « force #t »
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ token }}}.
Proof.
  intros Hh ?. iIntros "#HtickInv" (Φ) "!# ((Htc1 & Htc2) & #Hthunk & Htoken) Post".
  iMod (hthunk_pay with "Hthunk Htc2") as "#Hthunk'"; [ done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  wp_apply (hthunk_force with "[$] [$Htc1 Hthunk $Htoken]").
  { done. }
  { rewrite Nat.sub_diag. iFrame "Hthunk". }
  eauto.
Qed.

End HThunks.
