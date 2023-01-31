From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits PiggyBank.
From iris_time Require Import ThunksCode.

(* This file defines the predicate [ThunkVal]. It also provides a definition
   of the predicate [BaseThunk]. Together, these definitions satisfy the
   common thunk API defined in ThunksAPI.v. *)

(* -------------------------------------------------------------------------- *)

(* We write [ThunkToken p F] as a synonym for [na_own p F]. *)

Notation ThunkToken := na_own.

(* -------------------------------------------------------------------------- *)

(* Prologue. *)

Section Proofs.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).
Open Scope nat_scope.

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type E F : coPset.
Implicit Type t : loc.
Implicit Type n nc ac : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.
Implicit Type f v : val.
Implicit Type γdecided : gname.

(* -------------------------------------------------------------------------- *)

(* We write [isAction f n R φ] to indicate that [f] is a one-shot function
   that takes a unit argument and returns a value v such that [□ φ v] holds.
   The cost of this call is [n] time credits. The resource [R] is required,
   but not consumed, by this call. *)

(* This is essentially a Texan triple without a persistence modality. *)

Definition isAction f n R φ : iProp :=
  R -∗ TC n -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }}.

(* -------------------------------------------------------------------------- *)

(* The parameters of the public predicate [BaseThunk p F t n R φ] are:

    - p, F: a non-atomic-invariant pool and a mask; the token
            [ThunkToken p F] is required to force this thunk

    - t: a memory location; the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - R: a resource that is required, but not consumed,
         when the thunk is forced

    - φ: a postcondition; the value v produced by forcing this thunk
         satisfies [□ φ v].

 *)

(* The following variables are used internally:

    - γdecided: a ghost cell, whose content is either [Cinl (Excl ())] or
      [Cinr (to_agree v)], indicating whether the thunk has been forced
      already; the left side is exclusive and represents a unique permission
      to force; the right side is persistent and represents agreement on the
      value v

    - f: the function that is invoked when the thunk is forced

    - v: the result of calling f(), and of forcing the thunk

*)

Local Definition ownUndecided γdecided :=
  own γdecided (Cinl (Excl ())).

Local Definition ownDecided γdecided v :=
  own γdecided (Cinr (to_agree v)).

(* The predicate [BaseThunk p F t n R φ] is public. It is an abstract
   predicate: its definition is not meant to be exposed to the user. *)

(* The predicate [BaseThunk] involves a piggy bank whose branches are defined
   as follows:

     - in the left branch, the thunk is currently unevaluated: the ghost cell
       [γdecided] is undecided, the memory location [t] holds [UNEVALUATEDV
       «f»], and we have a unique permission to call f, which requires [nc]
       time credits;

     - in the right branch, the thunk is evaluated already: the ghost cell
       [γdecided] is decided, the memory location [t] holds [EVALUATEDV «v»],
       and the value v satisfies the postcondition □φ.

   The postcondition □φ is persistent by construction. Indeed, a copy of the
   value [v] is returned to the caller and a copy of [v] is memoized for later
   use. Both copies must satisfy the postcondition, so the postcondition must
   be duplicable. *)

(* The definition of [BaseThunk] further states that:

   + the ghost location [γdecided] is uniquely associated with the thunk [t];
     this is needed to synchronize [BaseThunk] and [ThunkVal] without exposing
     [γdecided] in the public API;

   + the piggy bank is indexed by [p] and [N], where [↑N ⊆ F] holds, which
     means that the token [ThunkToken p F] suffices to force this piggy bank;

   + the piggy bank is indexed by [ThunkPayment], which means that paying
     requires the current atomic mask [E] to satisfy [↑ThunkPayment ⊆ E]. *)

Local Definition LeftBranch t γdecided R φ nc : iProp :=
  ∃ f,
      ownUndecided γdecided
    ∗ t ↦ UNEVALUATEDV « f »
    ∗ isAction f nc R φ.

Local Definition RightBranch t γdecided φ : iProp :=
  ∃ v,
      ownDecided γdecided v
    ∗ t ↦ EVALUATEDV « v »
    ∗ □ φ v.

Definition ThunkPayment : namespace :=
  nroot .@ "thunk_payment".

Definition BaseThunk p F t n R φ : iProp :=

  ∃ γdecided N,
      ⌜ ↑N ⊆ F ⌝
    ∗ meta t nroot γdecided
    ∗ PiggyBank
        (LeftBranch t γdecided R φ)
        (RightBranch t γdecided φ)
        ThunkPayment
        p N n

.

(* The predicate [ThunkVal t v] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* This predicate is persistent. It means that the thunk t has been forced
   and that its value is v. *)

Definition ThunkVal t v : iProp :=

  ∃ γdecided,
      meta t nroot γdecided
    ∗ ownDecided γdecided v

.

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_thunk :=
  iDestruct "Hthunk"
    as (γdecided N) "(%HNF & Hmeta & #Hpiggy)".

Local Ltac destruct_left_branch :=
  iDestruct "Hbranch" as (f) "(>Hundecided & >Ht & Hf)".

Local Ltac destruct_right_branch :=
  iDestruct "Hbranch" as (v) "(>#Hdecided & >Ht & #Hv)".

Local Ltac destruct_thunkval :=
  iDestruct "Hval" as (γdecided) "(Hmeta & Hγdecided)".

Local Ltac construct_thunkval :=
  try iModIntro; iExists _; auto.

Local Ltac construct_right_branch :=
  try iNext; iExists _; eauto with iFrame.

Local Ltac construct_thunk :=
  try iModIntro; iExists _, _; eauto with iFrame.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about our ghost state. *)

Local Lemma decide γdecided v :
  ownUndecided γdecided ==∗ ownDecided γdecided v.
Proof.
  unfold ownUndecided, ownDecided.
  iIntros "Hγdecided".
  iApply (own_update with "Hγdecided").
  by apply cmra_update_exclusive.
Qed.

Local Lemma ownDecided_agree γdecided v1 v2 :
  ownDecided γdecided v1 -∗ ownDecided γdecided v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hag.
  iPureIntro.
  eapply to_agree_op_valid_L, (proj1 (Cinr_valid (A:=unitR) _)).
  by rewrite Cinr_op.
Qed.

Local Lemma decided_xor_undecided γdecided v :
  ownUndecided γdecided -∗ ownDecided γdecided v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %Hag.
  iPureIntro.
  auto.
Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the common thunk API. *)

Global Instance base_thunk_persistent p F t n R φ :
  Persistent (BaseThunk p F t n R φ).
Proof using.
  exact _.
Qed.

(* A public lemma: ThunkVal is persistent. *)

Global Instance thunkval_persistent t v :
  Persistent (ThunkVal t v).
Proof.
  exact _.
Qed.

(* A public lemma: ThunkVal is timeless. *)

Global Instance thunkval_timeless t v :
  Timeless (ThunkVal t v).
Proof.
  exact _.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: in [ThunkVal t v], [t] determines [v]. That is, a thunk
   has at most one value. Once its value has been decided, it becomes fixed
   forever. *)

Lemma confront_thunkval_thunkval t v1 v2 :
  ThunkVal t v1 -∗ ThunkVal t v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "Hval Hval2".
  destruct_thunkval.
  iDestruct "Hval2" as (γdecided2) "(Hmeta2 & Hγdecided2)".
  iDestruct (meta_agree with "[$][$]") as "%Heq". iClear "Hmeta Hmeta2".
  assert (γdecided2 = γdecided) by congruence. subst.
  iApply (ownDecided_agree with "Hγdecided [$]").
Qed.

(* -------------------------------------------------------------------------- *)

(* The conjunction of [BaseThunk p F t n R φ] and [ThunkVal t v] implies that
   the thunk [t] has zero debits, that is, [BaseThunk p F t 0 R φ] holds. This
   guarantees that this thunk can be forced at a constant cost. *)

(* This lemma is not part of the common thunk API because it is true at level
   zero only; it is not true at higher levels. The fact that a physical thunk
   has been forced does not imply that the ghost thunks above it have been
   forced; so a ghost thunk does not satisfy this law. *)

Lemma confront_base_thunk_thunkval p F t n R φ v F' E :
  ↑ThunkPayment ⊆ E →
  F ⊆ E →
  F ⊆ F' →
  BaseThunk p F t n R φ -∗
  ThunkVal t v -∗
  ThunkToken p F'
  ={E}=∗
  BaseThunk p F t 0 R φ ∗
  ▷ □ φ v ∗
  ThunkToken p F'.
Proof.
  intros.
  iIntros "#Hthunk #Hval Htoken".
  destruct_thunk.
  iDestruct "Hval" as (γdecided2) "(Hmeta2 & Hdecided)".

  (* Exploit the agreement of the meta tokens. *)
  iDestruct (meta_agree with "Hmeta Hmeta2") as "%Heq".
  subst γdecided2.
  iClear "Hmeta2".

  (* Prove that the piggy bank must be in its right branch and must
     have zero debit. *)
  iMod (piggybank_peek with "Hpiggy Htoken [] []")
    as "(#Hpiggy0 & $ & $)";
    [ eassumption | set_solver | set_solver | | | construct_thunk ].

  (* Subgoal 1: we must prove that in the left branch
     we are able to obtain a contradiction. *)
  { iIntros (nc) "Hbranch".
    destruct_left_branch.
    (* The contradiction follows from the fact that the ghost cell γdecided
       cannot be both decided and undecided. *)
    iDestruct (decided_xor_undecided with "Hundecided Hdecided")
      as "%contradiction".
    tauto. }

  (* Subgoal 2: we must prove that in the right branch
     we are able to extract [□ φ v]. *)
  { iIntros "Hbranch". iNext.
    rename v into v'.
    iRename "Hdecided" into "Hdecided'".
    iDestruct "Hbranch" as (v) "(#Hdecided & _ & #Hv)".
    iPoseProof (ownDecided_agree with "Hdecided Hdecided'") as "%Heq".
    subst v'. eauto. }

Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the common thunk API. *)

Lemma base_thunk_increase_debt p F t n1 n2 R φ :
  n1 ≤ n2 →
  BaseThunk p F t n1 R φ -∗
  BaseThunk p F t n2 R φ.
Proof.
  iIntros (?) "Hthunk".
  destruct_thunk.
  iPoseProof (piggybank_increase_debt with "Hpiggy") as "#Hpiggy'"; [eauto|].
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* A public lemma: the specification of [create]. *)

(* In short, [create] requires
   + 3 time credits;
   + a permission to call f(), at most once,
     with precondition nc$ and postcondition φ.

   [create] returns a thunk [t] whose number of debits is [nc]
                            and whose postcondition is [φ].

   The pool [p] is arbitrarily chosen by the user. *)

Lemma base_thunk_create p N F nc R φ f :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 3 ∗ isAction f nc R φ }}}
    «create f»
  {{{ t, RET «#t» ; BaseThunk p F t nc R φ }}}.
Proof.
  intros.
  iIntros "#Htickinv" (Φ) "!# [Htc Hf] Post".
  (* Step over the code of [create f] until the end. *)
  iApply wp_fupd.
  wp_tick_lam. wp_tick_inj. wp_tick.
  wp_alloc_with_meta t as "Ht" "Hmeta".
  (* Allocate the ghost cell γdecided. *)
  iMod (own_alloc (Cinl $ Excl ())) as (γdecided) "Hundecided"; first done.
  (* Associate [t] and [γdecided] via a [meta] assertion. *)
  iMod (meta_set _ t _ nroot with "[$]") as "#Hmeta". { set_solver. }
  (* Create a piggy bank. This requires checking that the left branch holds. *)
  iMod (piggybank_create
                (LeftBranch t γdecided R φ)
                (RightBranch t γdecided φ)
              with "[Hundecided Ht Hf]") as "#Hpiggy".
  { iExists _. eauto with iFrame. }
  (* Conclude. *)
  iApply "Post".
  construct_thunk.
Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the common thunk API. *)

Lemma base_thunk_force p F F' t R φ :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ BaseThunk p F t 0 R φ ∗ ThunkToken p F' ∗ R }}}
    «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ ThunkToken p F' ∗ R }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & Htoken & HR) Post".
  destruct_thunk.
  iApply wp_fupd.
  wp_tick_lam.

  (* Break the bank! *)
  iMod (piggybank_break with "Hpiggy Htoken")
    as (nc) "(Hbank & Htoken & Hclose)";
    [ set_solver | set_solver | set_solver |].

  (* This places us in one of two situations: either the bank has never
     been broken yet, or it has been broken before. *)
  iDestruct "Hbank" as "[(Hbranch & Hnc) | Hbranch]".

  (* Case: the bank has never been broken. *)
  {
    (* The piggy bank gives us [nc] time credits as well as the ability
       to close the bank's invariant, provided we are able to establish
       the right branch of our invariant. *)
    destruct_left_branch.
    (* We now step through the code. The left branch is taken. *)
    wp_tick_load. wp_tick_match.
    (* Because we have the necessary time credits, we can invoke f(), *)
    wp_apply ("Hf" with "HR Hnc") ; iIntros (v) "HR #Hv".
    (* and update the reference. *)
    wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
    (* Update the ghost state to remember that the value has been computed. *)
    iMod (decide with "Hundecided") as "#Hdecided".
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { construct_thunkval. }
    (* Subgoal: close the invariant. *)
    { iApply ("Hclose" with "[Ht] Htoken"). construct_right_branch. }
  }

  (* Case: the bank has been broken already. *)
  {
    (* The piggy bank requires us to preserve the right branch of our
       invariant. *)
    destruct_right_branch.
    (* We now step through the code. The right branch is taken. *)
    wp_tick_load. wp_tick_match.
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { construct_thunkval. }
    (* Subgoal: close the invariant. *)
    { iApply ("Hclose" with "[Ht] Htoken"). construct_right_branch. }
  }

Qed.

(* -------------------------------------------------------------------------- *)

(* A different specification for [force] in the case where the thunk has been
   forced already. *)

(* In this case, the number of debits [n] is not required to be zero, and the
   resource [R] is not required. Furthermore, the result value [v] is known
   ahead of time. *)

(* We are able to prove [□ φ v], but this property is not preserved at higher
   levels (see ThunksAPI and ThunksStep). *)

Lemma base_thunk_force_forced p F t n R φ v F' :
  F ⊆ F' →
  TC_invariant -∗
  {{{ TC 11 ∗ BaseThunk p F t n R φ ∗ ThunkVal t v ∗ ThunkToken p F' }}}
    «force #t»
  {{{ RET «v» ; □ φ v ∗ ThunkToken p F' }}}.
Proof.
  intros ?.
  iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & #Hval & Htoken) Post".

  (* Argue that this thunk has zero debits. *)
  iMod (confront_base_thunk_thunkval with "Hthunk Hval Htoken")
    as "(#Hthunk' & #Hv & Htoken)"; [ done | done | done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  iClear "Hv". (* Not needed below; we rediscover it. *)

  destruct_thunk.
  iApply wp_fupd.
  wp_tick_lam. simpl.

  (* Break the bank! *)
  iMod (piggybank_break with "Hpiggy Htoken")
    as (nc) "(Hbank & Htoken & Hclose)";
    [ set_solver | set_solver | set_solver |].

  (* This places us in one of two situations: either the bank has never
     been broken yet, or it has been broken before. *)
  iDestruct "Hbank" as "[(Hbranch & Hnc) | Hbranch]".

  (* Case: the bank has never been broken. *)
  {
    destruct_left_branch.
    (* This case is impossible. We repeat an argument that is already
       found in the proof of [confront_base_thunk_thunkval], and we have
       already invoked this lemma above, so there is some redundancy here.
       Never mind. This is not a big deal. *)
    iExFalso. iClear "Htickinv Hpiggy Post".
    iDestruct "Hval" as (γdecided2) "(Hmeta2 & Hdecided)".
    (* Exploit the agreement of the meta tokens. *)
    iDestruct (meta_agree with "Hmeta Hmeta2") as "%Heq".
    subst γdecided2.
    iClear "Hmeta2".
    (* The contradiction follows from the fact that the ghost cell γdecided
       cannot be both decided and undecided. *)
    iDestruct (decided_xor_undecided with "Hundecided Hdecided")
      as "%contradiction".
    tauto.
  }

  (* Case: the bank has been broken already. *)
  {
    (* The piggy bank requires us to preserve the right branch of our
       invariant. *)
    rename v into v'.
    destruct_right_branch.
    (* [v] and [v'] must be the same value. *)
    iDestruct (confront_thunkval_thunkval with "Hval [Hdecided]") as "%Heq".
    { iExists _. iFrame "Hmeta Hdecided". }
    subst v'.
    (* We now step through the code. The right branch is taken. *)
    wp_tick_load. wp_tick_match.
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv".
    (* Close the invariant. *)
    iApply ("Hclose" with "[Ht] Htoken").
    construct_right_branch.
  }

Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the common thunk API. *)

Lemma base_thunk_pay p F E n k t R φ :
  ↑ThunkPayment ⊆ E →
  BaseThunk p F t n R φ -∗   TC k   ={E}=∗
  BaseThunk p F t (n-k) R φ.
Proof.
  intros.
  iIntros "#Hthunk Hk".
  destruct_thunk.

  (* Put the [k] credits into the piggy bank. *)
  iMod (piggybank_pay with "Hpiggy Hk") as "#Hpiggy'";
    [ set_solver |].

  construct_thunk.
Qed.

End Proofs.
