From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl agree csum.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.
From iris_time Require Import ThunksCode ThunksAPI.

(* This file contains definitions of the predicates [Thunk] and [ThunkVal]
   that satisfy the basic thunk API defined in ThunksAPI.v. *)

(* -------------------------------------------------------------------------- *)

Section Proofs.

Notation valO := (valO heap_lang).
Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (csumR (exclR unitO) (agreeR valO))}. (* γdecided *)
Context `{na_invG Σ}.

(* The parameters of the public predicate [Thunk p N t n R φ] are:

    - p: a non-atomic-invariant pool name

    - N: a non-atomic-invariant namespace

    - t: the physical location of the thunk

    - n: the apparent remaining debt,
         that is, the number of debits associated with this thunk

    - R: a resource that is required, but not consumed,
         when the thunk is forced

    - φ: the postcondition of this thunk is □φ

 *)

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type t : loc.
Implicit Type n : nat.
Implicit Type R : iProp Σ.
Implicit Type φ : val → iProp Σ.

(* The following variables are used internally:

    - γpaid: a ghost cell, whose content inhabits the monoid Auth (Nat, max)

    - γdecided: a ghost cell, whose content is either Left () or Right v,
      indicating whether the thunk has been forced already;
      the left side is exclusive and represents a unique permission to force;
      the right side is persistent and represents agreement on the value v

    - nc: the necessary credits, that is, the credits that appear
          in the precondition of the function f

    - ac: the available credits, that is, the credits that have
          been paid so far and currently stored in the thunk

    - f: the function that is invoked when the thunk is forced

    - v: the result of calling f(), and of forcing the thunk

*)

Implicit Type γpaid γdecided : gname.
Implicit Type nc ac : nat.
Implicit Type f v : val.

Local Definition ownUndecided γdecided :=
  own γdecided (Cinl $ Excl ()).

Local Definition ownDecided γdecided v :=
  own γdecided (Cinr $ to_agree v).

(* The internal predicate [ThunkInv ...] is the thunk's invariant. *)

(* It states that
   + the ghost cell γpaid contains the authoritative value ac;
     that is, ac is the authoritative number of "available credits";
   + and
     - either the thunk is currently unevaluated,
       in which case we have a unique permission to call f,
       and this call requires nc time credits,
       and we currently have ac time credits at hand;
     - or the thunk is evaluated already,
       and its value v satisfies the postcondition □φ,
       and the thunk must have been fully paid for (nc ≤ ac). *)

(* The postcondition □φ is persistent by construction. Indeed, a copy
   of the value [v] is returned to the caller and a copy of [v] is
   memoized for later use. Both copies must satisfy the postcondition,
   so the postcondition must be duplicable. *)

(* The assertion [nc ≤ ac] in the second disjunct expresses the idea that if a
   thunk has been forced then it must have been fully paid for. This assertion
   is used in the proof of the lemma Thunk_ThunkVal, which states that if a
   thunk has been forced, then it can be viewed as a zero-debit thunk. *)

Local Definition ThunkInv t γpaid γdecided nc R φ : iProp Σ :=

  ∃ ac,
      own γpaid (● MaxNat ac)
    ∗ (
        (∃ (f : val),
            ownUndecided γdecided
          ∗ t ↦ UNEVALUATEDV « f »
          ∗ (R -∗ TC nc -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }})
          ∗ TC ac
        )
      ∨ (∃ (v : val),
            ownDecided γdecided v
          ∗ t ↦ EVALUATEDV « v »
          ∗ □ φ v
          ∗ ⌜ nc ≤ ac ⌝
        )
      )
.

(* The predicate [Thunk p N t n R φ] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* Its definition states that:

   + γpaid and γdecided are the ghost locations associated with this thunk;

   + the thunk's invariant holds; it is placed in a non-atomic invariant
     indexed by the pool p;

   + we have a fragmentary view of the ghost cell γpaid containing the value
     [nc - n].

   Because γpaid inhabits the monoid Auth (Nat, max), this fragmentary view
   is duplicable. Intuitively, this means that we know [nc - n ≤ ac], hence
   [nc ≤ ac + n]. That is, the credits that have been paid already, plus the
   credits that remain to be paid, are sufficient to cover the actual cost
   of invoking f. *)

Definition Thunk p N t n R φ : iProp Σ :=

  ∃ γpaid γdecided nc,
      meta t nroot (γpaid, γdecided)
    ∗ na_inv p N (ThunkInv t γpaid γdecided nc R φ)
    ∗ own γpaid (◯ MaxNat (nc - n))

.

(* The predicate [ThunkVal t v] is public. It is an abstract predicate:
   its definition is not meant to be exposed to the user. *)

(* This predicate is persistent. It means that the thunk t has been forced
   and that its value is v. *)

Definition ThunkVal t v : iProp Σ :=

  ∃ γpaid γdecided,
      meta t nroot (γpaid, γdecided)
    ∗ ownDecided γdecided v

.

(* -------------------------------------------------------------------------- *)

(* Private lemmas about our ghost state. *)

Local Lemma decide γdecided v :
  ownUndecided γdecided ==∗ ownDecided γdecided v.
Proof.
  unfold ownUndecided, ownDecided.
  iIntros "Hγdecided".
  iApply (own_update _ _ _ with "Hγdecided").
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

(* A public lemma: the assertion [Thunk p N t n R φ] is persistent. This means
   that a thunk can be shared. In combination with [thunk_weakening] and
   [thunk_pay], this implies that several different views of a thunk, with
   distinct numbers of debits, can co-exist. *)

Global Instance thunk_persistent p N t n R φ :
  Persistent (Thunk p N t n R φ).
Proof using.
  exact _.
Qed.

(* The assertion [ThunkVal t v] is persistent and timeless. *)

Global Instance ThunkVal_persistent t v :
  Persistent (ThunkVal t v).
Proof. exact _. Qed.

Global Instance ThunkVal_timeless t v :
  Timeless (ThunkVal t v).
Proof. exact _. Qed.

(* This law is part of the basic thunk API. *)

Local Lemma ThunkVal_agree t v1 v2 :
  ThunkVal t v1 -∗ ThunkVal t v2 -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as (γpaid1 γdecided1) "(Hmeta1 & Hown1)".
  iDestruct "H2" as (γpaid2 γdecided2) "(Hmeta2 & Hown2)".
  iDestruct (meta_agree with "[$][$]") as "%Heq".
  assert (γdecided1 = γdecided2) by congruence. subst. clear Heq.
  iApply (ownDecided_agree with "Hown1 Hown2").
Qed.

(* A public lemma: the conjunction of [Thunk p N t n R φ] and [ThunkVal t v]
   implies that the thunk [t] has zero debits, that is, [Thunk p N t 0 R φ]
   holds. This guarantees that this thunk can be forced for a constant cost. *)

(* This lemma is not part of the basic thunk API because it is true at level
   zero only; it is not true at higher levels. The fact that a physical thunk
   has been forced does not imply that the ghost thunks above it have been
   forced; so a ghost thunk does not satisfy this law. *)

Lemma Thunk_ThunkVal p N t n R φ v F E :
  ↑N ⊆ E →
  ↑N ⊆ F →
  Thunk p N t n R φ -∗ ThunkVal t v -∗ na_own p F
  ={E}=∗
  Thunk p N t 0 R φ ∗                  na_own p F.
Proof.
  iIntros (? ?) "#Hthunk #Hval Hp".
  iDestruct "Hthunk" as (γpaid1 γdecided1 nc) "(Hmeta1 & Hinv & Hγpaid◯)".
  iDestruct "Hval" as (γpaid2 γdecided2) "(Hmeta2 & Hdecided)".
  (* Exploit the agreement of the meta tokens. *)
  iDestruct (meta_agree with "Hmeta1 Hmeta2") as "%Heq".
  assert (γpaid1 = γpaid2) by congruence.
  assert (γdecided1 = γdecided2) by congruence.
  subst. clear Heq.
  iClear "Hmeta2". iRename "Hmeta1" into "Hmeta".
  rename γpaid2 into γpaid.
  rename γdecided2 into γdecided.

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hinv Hp")
    as ">(Hthunk & Hp & Hclose)";
    [done|done|]. (* side conditions about masks *)

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & [ Hunevaluated | Hevaluated ])".

  (* Case: the thunk is UNEVALUATED. This is impossible. *)
  {
    iDestruct "Hunevaluated" as (f) "(>Hundecided & _ & _ & _)".
    (* The ghost cell cannot be both decided and undecided. *)
    iDestruct (decided_xor_undecided with "Hundecided Hdecided")
      as "%contradiction".
    tauto.
  }

  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v') "(>#Hdecided' & >Ht & #Hv & >%Hncac)".
    (* The following two lines argue that v and v' are the same value.
       This is not necessary in this proof, but we do it for clarity. *)
    iDestruct (ownDecided_agree with "Hdecided Hdecided'") as "%Heq".
    subst v'. iClear "Hdecided'".
    (* We know that this thunk has been paid for: we have nc ≤ ac.
       We can create a ghost witness of this fact. This will allow
       us to argue that this thunk has zero debits. *)
    iClear "Hγpaid◯".
    iMod (auth_max_nat_update_read_auth with "Hγpaid●")
      as "(Hγpaid● & Hγpaid◯)".
    iPoseProof (own_auth_max_nat_weaken _ ac (nc - 0) with "Hγpaid◯")
      as "Hγpaid◯"; [ lia |].
    (* Close the invariant. *)
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists ac. iFrame "Hγpaid●". iRight.
      iExists v. eauto with iFrame. }
    iModIntro.
    iExists γpaid, γdecided, nc.
    iFrame "Hmeta Hinv Hγpaid◯".
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the basic thunk API. *)

Local Lemma thunk_weakening p N t n1 n2 R φ :
  n1 ≤ n2 →
  Thunk p N t n1 R φ -∗
  Thunk p N t n2 R φ.
Proof.
  iIntros (?) "Hthunk".
  iDestruct "Hthunk" as (γpaid γdecided nc) "(Hmeta & Hinv & Hγpaid◯)".
  iExists γpaid, γdecided, nc. iFrame "Hmeta Hinv".
  iDestruct (own_auth_max_nat_weaken with "Hγpaid◯") as "$".
  lia.
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

Lemma thunk_create_spec p N nc R φ f :
  TC_invariant -∗
  {{{
      TC 3 ∗
      ( R -∗ TC nc -∗ ∀ ψ, (∀ v, R -∗ □ φ v -∗ ψ «v»%V) -∗ WP «f #()» {{ ψ }} )
  }}}
    «create f»
  {{{ (t : loc), RET #t ; Thunk p N t nc R φ }}}.
Proof.
  iIntros "#Htickinv" (Φ) "!# [? Hf] Post".
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● Hγpaid◯]".
  iMod (own_alloc (Cinl $ Excl ())) as (γdecided) "?"; first done.
  iApply wp_fupd.
  wp_tick_lam. wp_tick_inj. wp_tick.
  wp_alloc_with_meta t as "Ht" "Hmeta".
  iMod (meta_set _ t _ nroot with "[$]") as "#Hmeta". { set_solver. }
  iApply "Post".
  iExists γpaid, γdecided, nc ; rewrite (_ : nc - nc = 0); last lia.
  iFrame "Hmeta Hγpaid◯".
  iApply na_inv_alloc.
  iNext.
  (* The number of available credits is initially 0. *)
  iExists 0.
  auto with iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the basic thunk API. *)

Local Lemma thunk_force_spec p N F t R φ :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t 0 R φ ∗ na_own p F ∗ R }}}
  «force #t»
  {{{ v, RET «v» ; □ φ v ∗ ThunkVal t v ∗ na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (? & #Hthunk & Hp & HR) Post".
  iDestruct "Hthunk" as (γpaid γdecided nc) "#(Hmeta & Hthunkinv & Hγpaid◯)".
  rewrite (_ : nc - 0 = nc); last lia.
  iApply wp_fupd.
  wp_tick_lam.

  (* Open the invariant before reading and possibly writing the reference. *)
  iDestruct (na_inv_acc with "Hthunkinv Hp")
    as ">(Hthunk & Hp & Hclose)";
    [done|done|]. (* side conditions about masks *)

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & [ Hunevaluated | Hevaluated ])".
  (* Case: the thunk is UNEVALUATED. *)
  {
    iDestruct "Hunevaluated" as (f) "(>Hundecided & >Ht & Hf & >Htc)".
    wp_tick_load. wp_tick_match.
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    iDestruct (own_auth_max_nat_le with "Hγpaid● Hγpaid◯") as %I.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ I with "Htc") as "Htc".
    (* We can invoke f(), *)
    wp_apply ("Hf" with "HR Htc") ; iIntros (v) "HR #Hv".
    (* and update the reference. *)
    wp_tick_let. wp_tick_inj. wp_tick_store. wp_tick_seq.
    (* Update the ghost state to remember that the value has been computed. *)
    iMod (decide with "Hundecided") as "#Hdecided".
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { iModIntro. unfold ThunkVal. auto. }
    (* Subgoal: close the invariant. *)
    iApply "Hclose". iFrame "Hp". iNext.
    (* [ac] remains unchanged. We cannot make it zero, and we do not need to. *)
    iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v. eauto with iFrame.
  }
  (* Case: the thunk is EVALUATED. *)
  {
    iDestruct "Hevaluated" as (v) "(>#Hdecided & >Ht & #Hv & >%Hncac)".
    wp_tick_load. wp_tick_match.
    (* Establish the postcondition. *)
    iApply "Post".
    iFrame "Hv HR".
    iSplitR.
    (* Subgoal: establish [ThunkVal t v]. *)
    { iModIntro. unfold ThunkVal. auto. }
    (* Subgoal: close the invariant. *)
    iApply "Hclose". iFrame "Hp". iNext. iExists ac.
    iFrame "Hγpaid●".
    iRight. iExists v. eauto with iFrame.
  }
Qed.

(* -------------------------------------------------------------------------- *)

(* This law is part of the basic thunk API. *)

Lemma thunk_pay p N F E (n k : nat) t R φ :
  ↑N ⊆ F →
  ↑N ⊆ E →
  na_own p F -∗ Thunk p N t n R φ -∗
  TC k ={E}=∗
  na_own p F  ∗ Thunk p N t (n-k) R φ.
Proof.
  iIntros (? ?) "Hp #Hthunk Hk".
  iDestruct "Hthunk" as (γpaid γdecided nc) "#(Hmeta & Hinv & Hγpaid◯)".

  (* Open the invariant. *)
  iDestruct (na_inv_acc with "Hinv Hp") as ">(Hthunk & Hp & Hclose)";
    [done|done|].
  iDestruct "Hthunk" as (ac) "(>Hγpaid● & Hthunk)".

  (* Increment the ghost payment record from [ac] to [ac + k]. This is
     done in both branches of the case analysis (which follows). *)
  iDestruct (auth_max_nat_update_incr' _ _ _ k with "Hγpaid● Hγpaid◯")
    as ">[Hγpaid● #Hγpaid◯']".
  iClear "Hγpaid◯". iRename "Hγpaid◯'" into "Hγpaid◯".

  (* Perform a case analysis. *)
  iDestruct "Hthunk" as "[ Hthunk | Hthunk ]".

  (* Case: the thunk is unevaluated. *)
  {
    iDestruct "Hthunk" as (f) "(>Hundecided & >Ht & Hf & >Hac)".
    (* We have [ac + k] time credits. *)
    iAssert (TC (ac + k)) with "[Hac Hk]" as "Hack"; first by iSplitL "Hac".
    (* The invariant can be closed. *)
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists (ac+k). auto with iFrame. }
    iModIntro.
    iExists γpaid, γdecided, nc. iFrame "Hmeta Hinv".
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [Thunk] assertion. *)
    iApply (own_auth_max_nat_weaken with "[$]").
    lia.
  }

  (* Case: the thunk is evaluated. *)
  {
    iDestruct "Hthunk" as (v) "(>#Hdecided & >Ht & #Hv & >%Hncac)".
    (* The invariant can be closed. In this case, no new time credits are
       stored in the invariant. The extra payment is wasted. *)
    iClear "Hk".
    iMod ("Hclose" with "[-Hγpaid◯]") as "$".
    { iFrame "Hp". iNext. iExists (ac+k). iFrame "Hγpaid●".
      iRight. iExists v. iFrame "Hdecided Ht Hv". iPureIntro. lia. }
    iModIntro.
    iExists γpaid, γdecided, nc. iFrame "Hmeta Hinv".
    iApply (own_auth_max_nat_weaken with "[$]").
    lia.
  }

Qed.

(* -------------------------------------------------------------------------- *)

(* The special case of [force] where the thunk has been forced already. *)

(* In this case, the resource [R] is not needed, so a stronger specification
   could be given. Its proof would require duplicating the proof of [force],
   or (better) generalizing the spec of [force] to cover both cases. We do
   not do so because we have no use for this stronger specification. Indeed,
   the construction that we have in mind (ThunksStep.v) does not need it and
   does not preserve it. Forcing a ghost proxy thunk can require [R], even
   if the underlying physical thunk has been forced already, because we
   allow the ghost update to use [R]. *)

(* In this strong statement, the postcondition mentions [□ φ v]. *)

Lemma thunk_force_forced_strong p N t n R φ v F :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t n R φ ∗ ThunkVal t v ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ RET «v» ; □ φ v ∗ na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & #Hval & Hp & HR) Post".
  (* Argue that this thunk has zero debits. *)
  iMod (Thunk_ThunkVal with "Hthunk Hval Hp") as "(#Hthunk' & Hp)";
    [ done | done |].
  iClear "Hthunk". iRename "Hthunk'" into "Hthunk".
  (* Force the thunk. *)
  iApply (thunk_force_spec with "Htickinv [$Hcredits $Hthunk $Hp $HR]");
    [ done |].
  iNext.
  iIntros (v') "(#Hv' & #Hval' & Hp & HR)".
  (* Argue that the two values must be the same. *)
  iPoseProof (ThunkVal_agree with "Hval Hval'") as "%". subst v'.
  (* Done. *)
  iApply "Post". auto with iFrame.
Qed.

(* In this weak statement, the postcondition does not mention [□ φ v]. *)

Local Lemma thunk_force_forced_weak p N t n R φ v F :
  ↑N ⊆ F →
  TC_invariant -∗
  {{{ TC 11 ∗ Thunk p N t n R φ ∗ ThunkVal t v ∗ na_own p F ∗ R }}}
    «force #t»
  {{{ RET «v» ; na_own p F ∗ R }}}.
Proof.
  iIntros (?).
  iIntros "#Htickinv" (Φ) "!# (Hcredits & #Hthunk & #Hval & Hp & HR) Post".
  iApply (thunk_force_forced_strong with
    "Htickinv [$Hcredits $Hthunk $Hp $HR]"); [ done | done |].
  iNext.
  iIntros "(Hv & Hp & HR)".
  iClear "Hv". (* drop □ φ v *)
  iApply "Post". eauto with iFrame.
Qed.

(* -------------------------------------------------------------------------- *)

(* We now check that the API is satisfied. *)

Global Instance thunkbase_api :
  BasicThunkAPI Thunk ThunkVal.
Proof.
  constructor.
  { eauto using ThunkVal_agree. }
  { eauto using thunk_weakening. }
  { eauto using thunk_force_spec. }
  { eauto using thunk_force_forced_weak. }
  { eauto using thunk_pay. }
Qed.

End Proofs.
