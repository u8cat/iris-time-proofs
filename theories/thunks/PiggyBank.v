From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum gset coPset.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(* A piggy bank is a ghost concept: no code is involved. A piggy bank is a
   place where one can accumulate time credits, by paying in several
   increments, until a point in time where one decides to "force" (or "break")
   the piggy bank and spend the time credits. *)

(* A piggy bank is either forced or not yet forced. (The internal ghost cell
   γforced keeps track of this information.) As long it is not forced, the
   assertion [LeftBranch nc] holds, where [nc] is a certain number of time
   credits that are deemed "necessary" in order to force the piggy bank. Once
   it is forced, the assertion [RightBranch] holds. *)

(* A piggy bank is shareable (that is, persistent). The predicate [PiggyBank]
   carries a parameter [n] which represents a number of debits, that is, a
   debt that must be paid before the piggy bank can be forced. Once the debt
   is zero, the piggy bank can be forced. A piggy bank can be forced several
   times. When it is forced for the first time, it performs an internal
   transition from [LeftBranch nc] to [RightBranch]; if it is forced again,
   it remains in the state [RightBranch]. *)

(* This file defines the predicate [PiggyBank LeftBranch RightBranch P p N n]
   and provides a number of reasoning rules for this predicate. *)

(* -------------------------------------------------------------------------- *)

(* Context. *)

Section PiggyBank.

Context `{timeCreditHeapG Σ}.        (* time credits are needed *)
Context `{inG Σ (authR max_natUR)}.  (* camera for the ghost cell γpaid *)
Context `{na_invG Σ}.                (* non-atomic invariants are needed *)
Notation iProp := (iProp Σ).

Local Existing Instance na_inv_inG.

(* The following parameters of the predicate [PiggyBank] are fixed throughout
   this file. *)

(* The assertion [LeftBranch nc] describes the state of the piggy bank when it
   has not been forced yet. It is typically an implication of the form [TC nc
   -∗ ...], that is, an assertion that needs [nc] time credits in order to be
   exploited. *)

(* The assertion [RightBranch] describes the state of the piggy bank after it
   has been forced. *)

(* The piggy bank internally involves an atomic invariant in the namespace [P]
   and a non-atomic invariant in the pool [p] and namespace [N]. *)

Variable LeftBranch  : (* nc: *) nat → iProp.
Variable RightBranch :                 iProp.
Variable P           :             namespace.
Variable p           :      na_inv_pool_name.
Variable N           :             namespace.

(* We typically use [n] for a number of debits, [nc] for a number of necessary
   time credits, and [ac] a number of available time credits. We use [forced]
   for a Boolean flag that determines whether the piggy bank has been forced.

   The ghost cell [γforced] stores the Boolean flag [forced]. This ghost cell
   is used to synchronize the two invariants and ensure that they both (and
   only they) have access to [forced]. Two exclusive tokens [●E] and [◯E] are
   used to keep track of the value of [forced].

   The ghost cell [γpaid] keeps track of the number of time credits that have
   been paid so far. It is a monotonic cell: its authoritative value [● ac]
   increases over time. A persistent witness [◯ (nc - n)] guarantees that [ac]
   is at least [nc - n], that is, [nc ≤ ac + n] holds. Thus, when the number
   of debits [n] is zero, we get [nc ≤ ac], that is, the number of available
   credits exceeds the number of necessary credits. This is the intuitive
   reason why it is sound to force the piggy bank once its apparent debt is
   zero. *)

Implicit Type n nc ac : nat.
Implicit Type forced : bool.
Implicit Type γforced γpaid : gname.

(* -------------------------------------------------------------------------- *)

(* Definitions. *)

(* The (ghost) operations that the piggy bank must support include [pay] and
   [force]. We want [pay] to be an atomic operation: a ghost update. However,
   we cannot view [force] as an atomic operation, because our intended use of
   the piggy bank does not allow it. Our main intended use of the piggy bank
   is the definition of thunks. Forcing a thunk is not an atomic operation: it
   requires several steps of computation. The piggy bank must be forced at the
   beginning of this operation, in order to obtain the necessary time credits,
   but its invariant cannot be restored until the end of this operation. So,
   breaking a piggy bank cannot be represented as single ghost update: it must
   be represented as a pair of nested updates, [begin force] and [end force].
   Between these updates, the piggy bank must not be forced, as it is not in a
   valid state. Paying is safe at all times, though, including while the piggy
   bank is being forced. *)

(* One might expect the piggy bank to involve one invariant, stating that
   either we are in the left branch and we have [ac] time credits at hand, or
   we are in the right branch. A definition based on a single invariant is
   possible indeed, but not would be satisfactory. Out of necessity, this
   invariant would have to be a non-atomic invariant, because [force] is not
   an atomic operation. As a result, [pay] would necessarily be forbidden
   while the piggy bank is being forced. (That is, [pay] would require a
   [na_own] token.)

   We are able to avoid this limitation by using two distinct invariants. A
   non-atomic invariant governs the state of the piggy bank: if the piggy bank
   has not been forced yet, then [LeftBranch nc] holds, otherwise
   [RightBranch] holds. An atomic invariant governs the time credits that have
   been accumulated: if the piggy bank has not been forced yet, then [ac] time
   credits are stored, otherwise no time credits are stored. (In the latter
   case, we have [nc ≤ ac].)

   Paying requires opening the atomic invariant only, so does not require a
   [na_own] token. Forcing requires opening both invariants simultanesously,
   so does require a [na_own] token.

   The two invariants must agree on the status of the piggy bank: either
   forced or not forced. To this end, they share the ghost cell [γforced]. One
   invariant holds [●E forced], the other holds [◯E forced']. Opening both
   invariants at once allows concluding [forced = forced'] and allows setting
   [γforced] to a new value. Opening just one invariant allows reading
   [γforced] but does not allow updating it. *)

Let PiggyBankInvariant i γpaid nc : iProp :=
  ∃ ac,
    own γpaid (● MaxNat ac)
  ∗ (own p (ε, GSet {[i]}) ∗ LeftBranch nc ∗ TC ac ∨
     na_own p {[i]} ∗ ⌜ nc ≤ ac ⌝ ∨
     own p (ε, GSet {[i]}) ∗ RightBranch ∗ ⌜ nc ≤ ac ⌝).

Definition PiggyBank n : iProp :=
  ∃ i γpaid nc,
      ⌜i ∈ (↑N:coPset)⌝
      ∗ inv P (PiggyBankInvariant i γpaid nc) ∗ own γpaid (◯ MaxNat (nc - n)).

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_piggy :=
  iDestruct "Hpiggy" as (i γpaid nc) "(% & Hinv & Hγpaid◯)".

Local Ltac open_na_invariant :=
  iDestruct (na_inv_acc with "Hnainv Htoken")
    as ">(Hcontent & Htoken & Hclose)";
    [set_solver | set_solver |];
  iDestruct "Hcontent" as (forced) "(>Hγforced● & Hbranch)".

Local Ltac open_invariant :=
  iMod (inv_acc with "Hinv") as "[Hcontent Hclose]"; [ done |];
  iDestruct "Hcontent" as (ac) "(>Hγpaid● & Hcontent)".

Local Ltac duplicate_itok :=
  iDestruct "Hcontent" as "(>Hitok' & _ & _)";
  iCombine "Hitok Hitok'" gives %[_ Hval%gset_disj_valid_op];
  by set_solver.

Local Ltac duplicate_toki :=
  iDestruct "Hcontent" as "(>Htoki' & _)";
  iDestruct (na_own_disjoint with "Htoki Htoki'") as %?;
  by set_solver.

Local Ltac case_analysis :=
  iDestruct "Hcontent" as "[Hcontent|[Hcontent|Hcontent]]"; [
    (iDestruct "Hcontent" as "(>Hitok & Hleft & >Hac)" || duplicate_itok) |
    (iDestruct "Hcontent" as "(>Htoki & >%)" || duplicate_toki) |
    (iDestruct "Hcontent" as "(>Hitok & Hright & >%)" || duplicate_itok)
  ].

Local Ltac create_white_bullet :=
  iMod (auth_max_nat_update_read_auth with "Hγpaid●")
    as "(Hγpaid● & #Hγpaid◯)".

Local Ltac weaken_white_bullet :=
  iDestruct (own_auth_max_nat_weaken with "Hγpaid◯") as "$";
  lia.

Local Ltac exploit_white_bullet :=
  iDestruct (own_auth_max_nat_le with "Hγpaid● Hγpaid◯") as "%Hleq".

Local Ltac increase_black_bullet k :=
  iMod (auth_max_nat_update_incr _ _ k with "Hγpaid●") as "Hγpaid●".

Local Ltac close_invariant pat :=
  iMod ("Hclose" with pat) as "_";
  [ iExists _; iFrame "Hγpaid●"; by auto 10 with iFrame lia |].
(*
iMod ("Hclose" with "[Hγpaid● Htoki]") as "_".
{ iExists _; iFrame "Hγpaid●"; iRight; iLeft; iFrame "Htoki"; auto with lia. }

iMod ("Hclose" with "[Hγpaid● Hright Hitok]") as "_".
{ iExists _; iFrame "Hγpaid●"; iRight; iRight; iFrame "Hright Hitok"; auto with lia. }
*)
Local Ltac construct_na_invariant :=
  try iNext; iExists _; iFrame "Hγforced●"; simpl; eauto.

Local Ltac construct_at_invariant :=
  try iNext; iExists _, _; iFrame "Hγforced◯ Hγpaid●"; simpl; eauto with lia.

Local Ltac close_na_invariant :=
  iMod ("Hclose" with "[-]") as "$"; [
    (* Subgoal: prove that the invariant holds *)
    iFrame "Htoken"; construct_na_invariant
  | (* Subgoal: after the invariant is closed *)
    iModIntro; (* We assume that we do not need the modality any more. *)
    eauto 2    (* Kill the goal if possible *)
  ].

Local Ltac close_at_invariant :=
  first [
    iMod ("Hclose" with "[Hγforced◯ Hγpaid● Hac]")
  | iMod ("Hclose" with "[Hγforced◯ Hγpaid●]")
  ];
  [ construct_at_invariant |].

Local Ltac construct_piggy :=
  try iModIntro;
  iExists _, _, _; iSplit; [done|]; iFrame "Hinv"; weaken_white_bullet.

(* -------------------------------------------------------------------------- *)

(* The following public lemmas are the reasoning rules of the piggy bank.     *)

(* The predicate [PiggyBank] is persistent. Thus, a piggy bank can be shared. *)

Global Instance piggybank_persistent n :
  Persistent (PiggyBank n).
Proof using.
  exact _.
Qed.

(* It is sound to increase the apparent debt (the number of debits) associated
   with a piggy bank. *)

Lemma piggybank_increase_debt n1 n2 :
  n1 ≤ n2 →
  PiggyBank n1 -∗
  PiggyBank n2.
Proof.
  intros.
  iIntros "#Hpiggy".
  destruct_piggy.
  construct_piggy.
Qed.

(* Creating a fresh piggy bank requires establishing [LeftBranch nc]. This
   assertion is consumed, and the new piggy bank initially has [nc] debits. *)

Lemma piggybank_create nc E :
  LeftBranch nc ={E}=∗
  PiggyBank nc.
Proof.
  iIntros "Hleft".
  (* Allocate the ghost cell [γpaid]. Its initial value is 0. *)
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● #Hγpaid◯]".
  (* We initially have 0 time credits at hand. *)
  iAssert (TC 0) as "Hac".
  { iApply zero_TC_now. }
  (* Allocate the NA ghost token. *)
  iMod (own_unit (prodUR coPset_disjUR (gset_disjUR positive)) p) as "Hempty".
  iMod (own_updateP with "Hempty") as ([m1 m2]) "[Hm Hitok]".
  { apply prod_updateP'.
    - apply cmra_updateP_id, (reflexivity (R:=eq)).
    - apply (gset_disj_alloc_empty_updateP_strong' (λ i, i ∈ (↑N:coPset)))=> Ef.
      apply fresh_inv_name. }
  simpl. iDestruct "Hm" as %(<- & i & -> & ?).
  (* Allocate the invariant. *)
  iAssert (PiggyBankInvariant i γpaid nc) with "[-]" as "Hcontent".
  { iExists _; iFrame "Hγpaid●"; iLeft; iFrame "Hitok Hleft Hac". }
  iMod (inv_alloc with "Hcontent") as "Hinv".
  (* Done. *)
  construct_piggy.
Qed.

(* Paying consumes [k] time credits and decreases the piggy bank's debit
   from [n] to [n-k]. It is a ghost update. *)

Lemma piggybank_pay k E n :
  ↑P ⊆ E →
  PiggyBank n -∗
  TC k ={E}=∗
  PiggyBank (n-k).
Proof.
  intros.
  iIntros "#Hpiggy Hk".
  destruct_piggy.

  (* Open the invariant. *)
  open_invariant.

  (* We learn [nc - n ≤ ac]. *)
  exploit_white_bullet.

  (* Increment the ghost payment record from [ac] to [ac + k]. *)
  increase_black_bullet k.
  iClear "Hγpaid◯".
  create_white_bullet.

  (* Perform a case analysis. *)
  case_analysis.

  (* Case: piggy bank is not broken. *)
  {
    (* We have [ac + k] time credits. *)
    iCombine "Hac Hk" as "Hac".
    (* The invariant can be closed. *)
    close_invariant "[-]".
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [PiggyBank] assertion. *)
    construct_piggy.
  }

  (* Case: piggy bank is being broken. *)
  {
    (* In this case, no new time credits are stored in the invariant.
       The payment is wasted. *)
    iClear "Hk".
    (* The invariant can be closed. *)
    close_invariant "[-]".
    (* We conclude in the same way as above. *)
    construct_piggy.
  }

  (* Case: piggy bank is broken *)
  {
    (* In this case, no new time credits are stored in the invariant.
       The payment is wasted. *)
    iClear "Hk".
    (* The invariant can be closed. *)
    close_invariant "[-]".
    (* We conclude in the same way as above. *)
    construct_piggy.
  }
Qed.

(* Forcing (or breaking) the piggy bank is the most complex operation. It is
   a ghost operation. As explained earlier, it is not an atomic operation,
   so it is not described as a single update. Instead, it is described as an
   update whose conclusion involves an update. These two updates mark the
   beginning and end of the operation.

   Forcing the piggy bank requires the token [na_own p F]. While forcing is
   in progress (that is, in between the two updates), this token is replaced
   with the weaker token [na_own p (F ∖ ↑N)]. This forbids forcing the piggy
   bank while it is already being forced. At the end, the stronger token
   [na_own p F] re-appears.

   The conclusion of the first update is a conjunction of three items:

   + a disjunction of two situations: either the piggy bank has not been
     forced yet, in which case we have [LeftBranch nc] and [nc] time credits
     at hand; or the piggy bank has been forced already, in which case we
     have [RightBranch];

   + a degraded token;

   + a second update, which transforms the degraded token back into the
     original token (thus making the piggy bank usable again), and which
     requires [RightBranch]. Thus, regardless of which state the piggy bank
     was in at the beginning, the user must (somehow) leave it in the right
     branch.

   Paying while the piggy bank is being forced is permitted. Indeed, paying
   does not require a [na_own] token. *)

(* The rule PiggyBank-Break in the paper does not involve a degraded token;
   the original token disappears at the beginning and re-appears at the end.
   Because a token can be split, the two versions of the rule are logically
   equivalent. *)

Lemma piggybank_break E F :
  (* The strong token and the weak token: *)
  let token := na_own p F in
  let token' := na_own p (F ∖ ↑N) in
  (* Side conditions about masks: *)
  ↑P ⊆ E →
  ↑N ⊆ E →
  ↑N ⊆ F →
  (* Forcing requires a piggy bank whose debt is zero.
     It also requires [token]. *)
  PiggyBank 0 -∗
  token ={E}=∗
  (* As a result of this first update, the user obtains: *)
  ∃ nc,
   (* either the left branch [LeftBranch nc] together with [nc] time
      credits, or the right branch [RightBranch]; *)
   ((▷ LeftBranch nc ∗ TC nc) ∨ ▷ RightBranch) ∗
   (* a degraded token; *)
   token' ∗
   (* and a second update, which must be used to recover the original
      token, and can therefore be viewed as an obligation to leave
      the piggy bank in the right branch: *)
   (▷ RightBranch -∗ token' ={E}=∗ token).
Proof.
  intros.
  iIntros "#Hpiggy Htoken".
  destruct_piggy.
  rewrite Nat.sub_0_r. (* nc - 0 = nc *)
  iExists nc.

  (* Massage the tokens. *)
  rewrite /token /token' [F as X in na_own p X](union_difference_L (↑N) F) //.
  rewrite [X in (X ∪ _)](union_difference_L {[i]} (↑N)) ?na_own_union; [|set_solver..].
  iDestruct "Htoken" as "[[Htoki $] $]".

  (* Open invariant. *)
  open_invariant.

  (* Perform case analysis. *)
  case_analysis.

  (* Case: piggy bank is not broken. *)
  {
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    exploit_white_bullet.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ Hleq with "Hac") as "Htc".

    (* The invariant can be closed. *)
    close_invariant "[Hγpaid● Htoki]".
    (* We are in the left-hand branch of the disjunction. *)
    iModIntro. iSplitL "Hleft Htc".
    { iLeft. iFrame "Hleft Htc". }
    (* Once the user performs a state change to [RightBranch],
       we will be able to re-open the invariant. *)
    iIntros "Hright $". clear ac Hleq.
    (* Open invariant. *)
    open_invariant.
    (* Perform case analysis and keep only the relevent case. *)
    case_analysis.
    (* The invariant can be closed in the new final state. *)
    iFrame "Htoki".
    by close_invariant "[-]".
  }

  (* Case: piggy bank is broken. *)
  {
    (* Close the invariant now. *)
    close_invariant "[Hγpaid● Htoki]".
    (* We are in the right-hand branch of the disjunction. *)
    iSplitL "Hright".
    { by iRight. }
    (* Once the user performs a state change to [RightBranch],
       we will be able to restore the invariant to its final state. *)
    clear dependent ac. iIntros "!> Hright $".
    open_invariant.
    (* Perform case analysis and keep only the relevent case. *)
    case_analysis.
    (* The invariant can be closed in the new final state. *)
    iFrame "Htoki".
    by close_invariant "[-]".
  }
Qed.

(* The following law may be viewed as more exotic and less essential than
   the previous laws. It states that if the user is somehow able to prove
   that the piggy bank cannot be in the left branch then the apparent debt
   of the piggy bank can be reduced from [n] to zero. Furthermore, it lets
   the user extract persistent information out of the right branch. *)

Lemma piggybank_peek φ n E F :
  (* The token: *)
  let token := na_own p F in
  (* Side conditions about masks: *)
  ↑P ⊆ E →
  ↑N ⊆ E →
  ↑N ⊆ F →
  (* A piggy bank with debit [n] and a token. *)
  PiggyBank n -∗
  token -∗
  (* A proof that the piggy bank cannot be in its left branch. *)
  (∀ nc, ▷ LeftBranch nc -∗ ▷ False) -∗
  (* An extractor of persistent information out of the right branch. *)
  (▷ RightBranch -∗ ▷ □ φ) ={E}=∗
  (* As a result, the user gets a view of the piggy bank with zero debits,
     and obtains the persistent information □ φ. *)
  PiggyBank 0 ∗ ▷ □ φ ∗
  token.
Proof.
  intros.
  iIntros "#Hpiggy Htoki Hcontradiction Hextractor".
  destruct_piggy.
  open_invariant.
  case_analysis.

  (* Case: left branch. This is impossible. *)
  { iDestruct ("Hcontradiction" with "Hleft") as ">contradiction".
    (* Because the goal is an update, we can strip a ▷ modality. *)
    iExFalso. eauto. }

  (* Case: right branch. *)
  iClear "Hcontradiction".
  iClear "Hγpaid◯".
  (* We have [nc ≤ ac]. We may create a ghost witness of this fact.
     This will allow us to argue that this piggy bank has debt zero. *)
  create_white_bullet.
  (* Extract ▷ □ φ. *)
  iPoseProof ("Hextractor" with "Hright") as "#$".
  (* Close the invariant. *)
  iFrame "Htoki".
  close_invariant "[-]".
  (* Done. *)
  construct_piggy.
Qed.

End PiggyBank.

Section PiggyBank_proper.

Context `{timeCreditHeapG Σ}.        (* time credits are needed *)
Context `{inG Σ (authR max_natUR)}.  (* camera for the ghost cell γpaid *)
Context `{na_invG Σ}.

Global Instance PiggyBank_proper :
  Proper (pointwise_relation _ (≡) ==> (≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) PiggyBank.
Proof. solve_proper. Qed.

Global Instance PiggyBank_ne n :
  Proper (pointwise_relation _ (dist n) ==> (dist n) ==> (=) ==> (=) ==> (=) ==> (=) ==> (dist n)) PiggyBank.
Proof. solve_proper. Qed.

Global Instance PiggyBank_contractive n :
  Proper (pointwise_relation _ (dist_later n) ==> (dist_later n) ==> (=) ==> (=) ==> (=) ==> (=) ==> (dist n)) PiggyBank.
Proof. solve_contractive. Qed.

End PiggyBank_proper.
