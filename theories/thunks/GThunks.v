From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time Require Import TimeCredits.
From iris_time Require Import ThunksCode ThunksBase ThunksAPI ThunksFull.
From iris_time Require Import Generations.
Open Scope nat_scope.

(* This file offers a theory of thunks indexed with integer generations.
   It is built on top of ThunksFull, which offers a more low-level theory
   of thunks indexed with masks. *)

(* In both cases, this discipline aims to prevent the construction of
   cyclic thunks. The main idea is that a thunk is allowed to force a
   thunk of an earlier generation. It is *not* allowed to force a thunk
   in the same generation or in a newer generation. A thunk is allowed
   to *construct* a thunk in an arbitrary generation. *)

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section GThunks.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Definition generation := generation.

Implicit Type p : na_inv_pool_name.
Implicit Type t : loc.
Implicit Type g : generation.
Implicit Type n : nat.
Implicit Type φ : val → iProp.

(* -------------------------------------------------------------------------- *)

(* The token associated with a pool [p] and bound [b]. *)

Definition GToken p b :=
  na_own p (gens_below_bound b).

(* This lemma allocates a new pool together with its token, which controls
   all generations in this pool. *)

Lemma gtoken_alloc :
  ⊢ |==> ∃ p, GToken p None.
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

(* The idea is simple: we index thunks with integer generations, and we allow
   a thunk to force a thunk of an earlier generation. *)

(* To do so, we use a thunk whose parameters [F] and [R] are instantiated in
   such a way that the tokens [ThunkToken p F] and [R] are disjoint. [F] is
   instantiated with [↑(gen_ns g')], that is, control over the generation [g']
   only. [R] is instantiated with [GToken p (Some g')], that is, control over
   all generations below [g']. *)

(* An existential quantification over [g'], with the constraint [g' ≤ g],
   ensures that [GThunk] is covariant in [g]. That is, it is safe to view
   a thunk in an early generation as a thunk in a newer generation. *)

(* We could keep a parameterization in [R], so as to allow our thunks to have
   visible side effects (that is, side effects that require a token). We have
   not yet felt the need to do so; so, for the moment, a thunk is not allowed
   to have visible side effects other than forcing other thunks. *)

Definition GThunk p g t n φ : iProp :=
  ∃ g', ⌜ g' ≤ g ⌝ ∗
  let F := ↑(gen_ns g') in
  let R := GToken p (Some g') in
  Thunk p F t n R φ.

(* -------------------------------------------------------------------------- *)

(* Local tactics. *)

Local Ltac deconstruct_thunk :=
  iDestruct "Hthunk" as (g') "(% & Hthunk)".

Local Ltac construct_thunk g' :=
  iExists g'; iSplitR; [ eauto with lia |].

Local Ltac construct_texan_triple ipat :=
  iIntros "#?"; (* introduce TC_invariant *)
  iIntros (Φ) "!>";
  iIntros ipat;
  iIntros "Post".

(* -------------------------------------------------------------------------- *)

(* [GThunk] is persistent. *)

Global Instance gthunk_persistent p g t n φ :
  Persistent (GThunk p g t n φ).
Proof using.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

(* The creation rule passes the token [GToken p (Some g)] to the suspended
   computation [f]. Thus, the newly created thunk, which belongs in the
   generation [g], can force thunks in generations less than [g]. *)

(* There is no restriction regarding the thunks that this new thunk may
   construct. Indeed, the postcondition [φ] is arbitrary. *)

Lemma gthunk_create p g n φ f :
  let token := GToken p (Some g) in
  TC_invariant -∗
  {{{ TC 3 ∗ isAction f n token φ }}}
    « create f »
  {{{ t, RET «#t» ; GThunk p g t n φ }}}.
Proof.
  construct_texan_triple "H".
  wp_apply (thunk_create with "[$] H"); [ done |].
  iIntros (t) "Hthunk".
  iApply "Post". construct_thunk g. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* The consequence rule is standard. *)

Lemma gthunk_consequence p g t n1 n2 φ ψ E :
  (∀ v, TC n2 -∗ □ φ v ={⊤}=∗ □ ψ v) -∗
  GThunk p g t  n1       φ  ={E}=∗
  GThunk p g t (n1 + n2) ψ.
Proof.
  iIntros "Hupdate Hthunk".
  deconstruct_thunk.
  iMod (thunk_consequence with "Hthunk [Hupdate]").
  { (* The token [GToken p (Some g')] is not passed to the update,
       because it would be essentially useless, as [g'] is unknown. *)
    iIntros (v) "$ Htc Hv".
    iApply ("Hupdate" with "Htc").
    iAssumption. }
  iModIntro. construct_thunk g'. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* [GThunk] is covariant in the parameter [g]. That is, it is safe to view a
   thunk in an early generation as a thunk in a newer generation. This makes
   this thunk more difficult to force, as a stronger token is required. *)

Lemma gthunk_covariant_in_g p g1 g2 t n φ :
  g1 ≤ g2 →
  GThunk p g1 t n φ -∗
  GThunk p g2 t n φ.
Proof.
  iIntros (?) "Hthunk".
  deconstruct_thunk.
  construct_thunk g'.
  done.
Qed.

(* -------------------------------------------------------------------------- *)

(* [GThunk] is covariant in the parameter [n]. That is, it is safe to view a
   thunk with a small debt as a thunk with a greater debt. *)

Lemma gthunk_increase_debt p g t n1 n2 φ :
  n1 ≤ n2 →
  GThunk p g t n1 φ -∗
  GThunk p g t n2 φ.
Proof using.
  iIntros (?) "Hthunk".
  deconstruct_thunk.
  construct_thunk g'.
  by iApply thunk_increase_debt.
Qed.

(* -------------------------------------------------------------------------- *)

(* Forcing a thunk in a generation [g] that lies below the bound [b] requires
   the token [GToken p b]. *)

(* To solve the proof obligation [lies_below g b], use [eauto with thunks].   *)

(* The thunk must have zero debit. If it has more than zero debit, then [pay]
   and [force] must be composed; see [gthunk_pay_force] below. *)

Lemma gthunk_force p g b t φ :
  lies_below g b →
  let token := GToken p b in
  TC_invariant -∗
  {{{ TC 11 ∗ GThunk p g t 0 φ ∗ token }}}
    « force #t »
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ token }}}.
Proof using.
  intros Hg.
  construct_texan_triple "(Htc & Hthunk & Htoken)".
  deconstruct_thunk.
  assert (Hg': lies_below g' b) by eauto using leq_lies_below.
  rewrite /GToken.
  rewrite (carve_out_gens_below_gen _ _ Hg').
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

(* Forcing a thunk that has already been forced. See ThunksAPI for comments. *)

Lemma gthunk_force_forced p g t n φ b v :
  lies_below g b →
  let token := GToken p b in
  TC_invariant -∗
  {{{ TC 11 ∗ GThunk p g t n φ ∗ ThunkVal t v ∗ token }}}
    « force #t »
  {{{ RET «v» ; token }}}.
Proof using.
  intros Hg.
  construct_texan_triple "(Htc & Hthunk & Hval & Htoken)".
  deconstruct_thunk.
  assert (Hg': lies_below g' b) by eauto using leq_lies_below.
  rewrite /GToken.
  rewrite (carve_out_gens_below_gen _ _ Hg').
  iDestruct (na_own_union with "Htoken") as "[Htoken1 Htoken2]".
  { set_solver. }
  (* Only one token is required here. *)
  wp_apply (thunk_force_forced with "[$] [$Htc $Hthunk $Hval $Htoken2]").
  { eauto using gen_ns_subseteq_interval. }
  (* Conclude. *)
  iIntros "Htoken2".
  iApply "Post".
  iDestruct (na_own_union with "[$Htoken1 $Htoken2]") as "Htoken".
  { set_solver. }
  iFrame "Htoken".
Qed.

(* -------------------------------------------------------------------------- *)

(* Paying. *)

Lemma gthunk_pay k E p g t n φ :
  ↑ThunkPayment ⊆ E →
  GThunk p g t n φ -∗ TC k
    ={E}=∗
  GThunk p g t (n-k) φ.
Proof using.
  iIntros (?) "Hthunk Htc".
  deconstruct_thunk.
  iMod (thunk_pay with "Hthunk Htc"); [ done |].
  iModIntro. construct_thunk g'. done.
Qed.

(* -------------------------------------------------------------------------- *)

(* The composition of [pay] and [force]. *)

Lemma gthunk_pay_force p g b t d φ :
  lies_below g b →
  let token := GToken p b in
  TC_invariant -∗
  {{{ TC (11 + d) ∗ GThunk p g t d φ ∗ token }}}
    « force #t »
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ token }}}.
Proof.
  intros Hg.
  iIntros "#HtickInv" (Φ) "!# ((Htc1 & Htc2) & #Hthunk & Htoken) Post".
  iMod (gthunk_pay with "Hthunk Htc2") as "#Hthunk'"; [ done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  wp_apply (gthunk_force with "[$] [$Htc1 Hthunk $Htoken]").
  { done. }
  { rewrite Nat.sub_diag. iFrame "Hthunk". }
  eauto.
Qed.

End GThunks.
