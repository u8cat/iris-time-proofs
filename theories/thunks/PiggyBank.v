From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
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
Context `{inG Σ (excl_authR boolO)}. (* camera for the ghost cell γforced *)
Context `{na_invG Σ}.                (* non-atomic invariants are needed *)
Notation iProp := (iProp Σ).

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

Local Definition PiggyBankNonAtomicInvariant γforced nc : iProp :=
  ∃ forced,
      own γforced (●E forced)
    ∗ if negb forced then LeftBranch nc else RightBranch.

Local Definition PiggyBankAtomicInvariant γforced γpaid nc : iProp :=
  ∃ forced ac,
      own γforced (◯E forced)
    ∗ own γpaid (● MaxNat ac)
    ∗ if negb forced then TC ac else ⌜ nc ≤ ac ⌝.

Definition PiggyBank n : iProp :=
  ∃ γforced γpaid nc,
      na_inv p N (PiggyBankNonAtomicInvariant γforced nc)
    ∗ inv P (PiggyBankAtomicInvariant γforced γpaid nc)
    ∗ own γpaid (◯ MaxNat (nc - n)).

(* -------------------------------------------------------------------------- *)

(* Local lemmas about the ghost cell γforced. *)

Local Lemma agree_forced γforced forced forced' :
  own γforced (●E forced) -∗
  own γforced (◯E forced') -∗
  ⌜ forced' = forced ⌝.
Proof.
  iIntros "Hγforced● Hγforced◯".
  iDestruct (own_valid_2 with "Hγforced● Hγforced◯") as "%Hvalid".
  iPureIntro. symmetry. eauto using excl_auth_agree_L.
Qed.

Local Lemma update_forced γforced forced forced' :
  own γforced (●E forced) -∗
  own γforced (◯E forced) ==∗
  own γforced (●E forced') ∗
  own γforced (◯E forced').
Proof.
  iIntros "Hγforced● Hγforced◯".
  iMod (own_update_2 with "Hγforced● Hγforced◯") as "[$ $]"; [| done ].
  eapply excl_auth_update.
Qed.

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_piggy :=
  iDestruct "Hpiggy" as (γforced γpaid nc) "(Hnainv & Hatinv & Hγpaid◯)".

Local Ltac open_na_invariant :=
  iDestruct (na_inv_acc with "Hnainv Htoken")
    as ">(Hcontent & Htoken & Hclose)";
    [set_solver | set_solver |];
  iDestruct "Hcontent" as (forced) "(>Hγforced● & Hbranch)".

Local Ltac open_at_invariant forced :=
  iMod (inv_acc with "Hatinv") as "[Hcontent Hatclose]"; [ done |];
  iDestruct "Hcontent" as (forced ac) "(>Hγforced◯ & >Hγpaid● & Hac)".

Local Ltac open_both_invariants :=
  (* Open the two invariants. *)
  open_na_invariant;
  let forced' := fresh in
  open_at_invariant forced';
  (* The two invariants must agree on the value of the ghost cell γforced. *)
  iDestruct (agree_forced with "Hγforced● Hγforced◯") as "%Hagree";
  subst forced'.

Local Ltac case_analysis forced :=
  (* Perform case analysis on the Boolean value [forced]. *)
  destruct forced;
  (* We want to handle the case [forced = false] first,
     so we swap the subgoals. *)
  swap 1 2;
  (* Simplify the conditionals that depend on [forced]. *)
  simpl;
  (* If the atomic invariant is currently opened, simplify the hypothesis
     "Hac", which is either [▷ TC ac] or [▷ ⌜ nc ≤ ac ⌝]. *)
  [
    try iDestruct "Hac" as ">Hac"
  | try iDestruct "Hac" as ">%Hac"
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

Local Ltac update_forced b :=
  iMod (update_forced _ _ b with "Hγforced● Hγforced◯")
    as "[Hγforced● Hγforced◯]".

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
    iMod ("Hatclose" with "[Hγforced◯ Hγpaid● Hac]")
  | iMod ("Hatclose" with "[Hγforced◯ Hγpaid●]")
  ];
  [ construct_at_invariant |].

Local Ltac construct_piggy :=
  try iModIntro;
  iExists _, _, _; iFrame "Hnainv Hatinv"; weaken_white_bullet.

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
  (* Allocate the ghost cell [γforced]. Its initial value is [false]. *)
  iMod (own_alloc (●E false ⋅ ◯E false)) as (γforced) "[Hγforced● Hγforced◯]".
  { apply excl_auth_valid. }
  (* Allocate the non-atomic invariant. *)
  iAssert (PiggyBankNonAtomicInvariant γforced nc)
    with "[Hγforced● Hleft]"
    as "Hcontent".
  { construct_na_invariant. }
  iMod (na_inv_alloc with "Hcontent") as "Hnainv".
  (* We initially have 0 time credits at hand. *)
  iAssert (TC 0) as "Htc".
  { iApply zero_TC_now. }
  (* Allocate the atomic invariant. *)
  iAssert (PiggyBankAtomicInvariant γforced γpaid nc)
    with "[Hγforced◯ Hγpaid●]" as "Hcontent".
  { construct_at_invariant. }
  iMod (inv_alloc with "Hcontent") as "Hatinv".
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

  (* Open the atomic invariant (and only this one). *)
  open_at_invariant forced.

  (* We learn [nc - n ≤ ac]. *)
  exploit_white_bullet.

  (* Increment the ghost payment record from [ac] to [ac + k]. *)
  increase_black_bullet k.
  iClear "Hγpaid◯".
  create_white_bullet.

  (* Perform a case analysis. *)
  case_analysis forced.

  (* Case: left branch. *)
  {
    (* We have [ac + k] time credits. *)
    iCombine "Hac Hk" as "Hac".
    (* The invariant can be closed. *)
    close_at_invariant.
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [PiggyBank] assertion. *)
    construct_piggy.
  }

  (* Case: right branch. *)
  {
    (* In this case, no new time credits are stored in the invariant.
       The payment is wasted. *)
    iClear "Hk".
    (* The invariant can be closed. *)
    close_at_invariant.
    (* We conclude in the same way as above. *)
    construct_piggy.
  }

Qed.

(* Forcing (or breaking) the piggy bank is the most complex operation. It is
   a ghost operation. As explained earlier, it is not an atomic operation,
   so it is not described as a single update. Instead, it takes the form of
   an update ([begin force]) whose conclusion is a disjunction of two
   situations:

   - either the piggy bank has not been forced yet, in which case we have
     [LeftBranch nc] and [nc] time credits at hand; it is then up to the
     user to (somehow) transition to [RightBranch], at which point we allow
     the user to perform a second update ([end force]) which completes the
     operation and restores the validity of the piggy bank;

  - or the piggy bank has been forced already, in which case we have
    [RightBranch]; it is then up to the user to perform whatever action is
    desired, while preserving [RightBranch]; at which point we allow the
    user to perform a second update ([end force]) which completes the
    operation and restores the validity of the piggy bank.

  Forcing the piggy bank requires the token [na_own p F]. While forcing is
  in progress (that is, between the [begin force] and [end force] updates)
  this token is replaced with the weaker token [na_own p (F ∖ ↑N)]. This
  forbids forcing the piggy bank while it is already being forced. At the
  end, the stronger token [na_own p F] re-appears.

  Paying while the piggy bank is being forced is permitted. Indeed, paying
  does not require a [na_own] token. *)

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
   ((▷ LeftBranch nc ∗ TC nc) ∨ ▷ RightBranch) ∗ token' ∗
   (* and a second update, which must be used to recover the original
      token, and can therefore be viewed as an obligation to leave
      the piggy bank in the right branch: *)
   (▷ RightBranch -∗ token' ={E}=∗ token).
Proof.
  intros.
  iIntros "#Hpiggy Htoken".
  destruct_piggy.
  rewrite Nat.sub_0_r. (* nc - 0 = nc *)

  (* Open both invariants. *)
  open_both_invariants.

  (* Part of the goal can be met. *)
  iExists nc.
  iFrame "Htoken".

  (* Perform case analysis. *)
  case_analysis forced.

  (* Case: left branch. *)
  {
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    exploit_white_bullet.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ Hleq with "Hac") as "Htc".
    (* Set γforced to [true]. *)
    update_forced true.
    (* Close the atomic invariant now. *)
    close_at_invariant. iModIntro.
    (* We are in the left-hand branch of the disjunction. *)
    iSplitL "Hbranch Htc".
    { iLeft. iFrame "Hbranch Htc". }
    (* Once the user performs a state change to [RightBranch],
       we will be able to close the non-atomic invariant. *)
    iIntros "Hbranch Htoken".
    close_na_invariant.
  }

  (* Case: right branch. This case is trivial. *)
  {
    (* Close the atomic invariant now. *)
    close_at_invariant. iModIntro.
    (* We are in the right-hand branch of the disjunction. *)
    iSplitL "Hbranch".
    { iRight. iFrame "Hbranch". }
    (* Once the user performs a state change to [RightBranch],
       we will be able to close the non-atomic invariant. *)
    iIntros "Hbranch Htoken".
    close_na_invariant.
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
  iIntros "#Hpiggy Htoken Hcontradiction Hextractor".
  destruct_piggy.
  open_both_invariants.
  case_analysis forced.

  (* Case: left branch. This is impossible. *)
  { iDestruct ("Hcontradiction" with "Hbranch") as ">contradiction".
      (* Because the goal is an update, we can strip a ▷ modality. *)
    iExFalso. eauto. }

  (* Case: right branch. *)
  iClear "Hcontradiction".
  iClear "Hγpaid◯".
  (* We have [nc ≤ ac]. We may create a ghost witness of this fact.
     This will allow us to argue that this piggy bank has debt zero. *)
  create_white_bullet.
  (* Extract ▷ □ φ. *)
  iPoseProof ("Hextractor" with "Hbranch") as "#Hφ".
  (* Close the atomic invariant. *)
  close_at_invariant.
  (* Close the non-atomic invariant. *)
  close_na_invariant.
  (* Done. *)
  iFrame "Hφ".
  construct_piggy.

Qed.

End PiggyBank.
