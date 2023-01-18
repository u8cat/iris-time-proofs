From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris.algebra Require Import auth excl excl_auth agree csum.
  (* TODO try Require Export *)
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(* -------------------------------------------------------------------------- *)

Section PiggyBank.

Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{inG Σ (excl_authR boolO)}.                  (* γforced *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type n nc ac : nat.
Implicit Type forced : bool.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.
Implicit Type γforced γpaid : gname.

Variable LeftBranch  : (* nc: *) nat → iProp.
Variable RightBranch :                 iProp.
Variable P           :             namespace.

Local Definition PiggyBankNonAtomicInvariant γforced nc : iProp :=
  ∃ forced,
      own γforced (●E forced)
    ∗ if negb forced then LeftBranch nc else RightBranch.

Local Definition PiggyBankAtomicInvariant γforced γpaid nc : iProp :=
  ∃ forced ac,
      own γforced (◯E forced)
    ∗ own γpaid (● MaxNat ac)
    ∗ if negb forced then TC ac else  ⌜ nc ≤ ac ⌝.

Definition PiggyBank p N n : iProp :=
  ∃ γforced γpaid nc,
      na_inv p N (PiggyBankNonAtomicInvariant γforced nc)
    ∗ inv P (PiggyBankAtomicInvariant γforced γpaid nc)
    ∗ own γpaid (◯ MaxNat (nc - n)).

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_piggy :=
  iDestruct "Hpiggy" as (γforced γpaid nc) "(Hnainv & Hatinv & Hγpaid◯)".

Local Ltac open_na_invariant :=
  iDestruct (na_inv_acc with "Hnainv Htoken")
    as ">(Hcontent & Htoken & Hclose)";
    [set_solver | set_solver |];
  iDestruct "Hcontent" as (forced) "(>Hγforced● & Hbranch)".

Local Ltac case_analysis forced :=
  (* Perform case analysis on the Boolean value [forced]. *)
  destruct forced;
  (* We want to handle the case [forced = false], so we swap the subgoals. *)
  swap 1 2;
  (* Simplify the conditionals that depend on [forced]. *)
  simpl;
  (* If the atomic invariant is currently opened, simplify the hypothesis
     Hac, which is either [▷ TC ac] or [▷ ⌜ nc ≤ ac ⌝]. *)
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

Local Ltac set_γforced b :=
  iMod (update_forced _ _ b with "Hγforced● Hγforced◯")
    as "[Hγforced● Hγforced◯]".

(* -------------------------------------------------------------------------- *)

(* Properties. *)

Global Instance piggybank_persistent p N n :
  Persistent (PiggyBank p N n).
Proof using.
  exact _.
Qed.

Lemma piggy_bank_increase_debt p N n1 n2 :
  n1 ≤ n2 →
  PiggyBank p N n1 -∗
  PiggyBank p N n2.
Proof.
  intros.
  iIntros "#Hpiggy".
  destruct_piggy.
  construct_piggy.
Qed.

Lemma piggybank_create p N nc E :
  LeftBranch nc ={E}=∗
  PiggyBank p N nc.
Proof.
  iIntros "Hleft".
  (* Allocate the ghost cell γpaid. Its initial value is 0. *)
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● #Hγpaid◯]".
  (* Allocate the ghost cell γforced. Its initial value is [false]. *)
  iMod (own_alloc (●E false ⋅ ◯E false)) as (γforced) "[Hγforced● Hγforced◯]".
  { apply excl_auth_valid. }
  (* Allocate the non-atomic invariant. *)
  iAssert (PiggyBankNonAtomicInvariant γforced nc)
    with "[Hγforced● Hleft]"
    as "Hcontent".
  { construct_na_invariant. }
  iMod (na_inv_alloc with "Hcontent") as "Hnainv".
  (* Note that we have 0 time credits. *)
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

Local Ltac open_at_invariant forced :=
  iMod (inv_acc with "Hatinv") as "[Hcontent Hatclose]"; [ done |];
  iDestruct "Hcontent" as (forced ac) "(>Hγforced◯ & >Hγpaid● & Hac)".

Lemma piggybank_pay k p N E n :
  ↑P ⊆ E →
  PiggyBank p N n -∗   TC k   ={E}=∗
  PiggyBank p N (n-k).
Proof.
  intros.
  iIntros "#Hpiggy Hk".
  destruct_piggy.
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
    (* TODO use [close_at_invariant] *)
    iMod ("Hatclose" with "[Hγforced◯ Hγpaid● Hac]").
    { construct_at_invariant. }
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [PiggyBank] assertion. *)
    construct_piggy.
  }

  (* Case: right branch. *)
  {
    (* The invariant can be closed. In this case, no new time credits are
       stored in the invariant. The extra payment is wasted. *)
    iClear "Hk".
    (* TODO use [close_at_invariant] *)
    iMod ("Hatclose" with "[Hγforced◯ Hγpaid●]").
    { construct_at_invariant. }
    construct_piggy.
  }

Qed.

Local Ltac open_both_invariants :=
  (* Open the two invariants. *)
  open_na_invariant;
  let forced' := fresh in
  open_at_invariant forced';
  (* The two invariants must agree on the value of the ghost cell γforced. *)
  iDestruct (agree_forced with "Hγforced● Hγforced◯") as "%Hagree";
  subst forced'.

Lemma piggybank_break p N E F :
  let token := na_own p F in
  let token' := na_own p (F ∖ ↑N) in
  ↑P ⊆ E →
  ↑N ⊆ E →
  ↑N ⊆ F →
  PiggyBank p N 0 -∗
  token
   ={E}=∗
   ( ∃ nc,
      ▷ LeftBranch nc ∗ TC nc ∗ token' ∗
     (▷ RightBranch -∗ token' ={E}=∗ token)
   ) ∨
   ( ∃ nc,
      ▷ RightBranch ∗ token' ∗
     (▷ RightBranch -∗ token' ={E}=∗ token)
   ).
Proof.
  intros.
  iIntros "#Hpiggy Htoken".
  destruct_piggy.
  rewrite Nat.sub_0_r.

  (* Open both invariants. *)
  open_both_invariants.

  (* Perform case analysis. *)
  case_analysis forced.

  (* Case: left branch. *)
  {
    (* We are in the left-hand branch of the conclusion. *)
    iLeft. iExists nc. iFrame "Hbranch Htoken".
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    exploit_white_bullet.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ Hleq with "Hac") as "$".
    (* Set γforced to [true]. *)
    set_γforced true.
    (* Close the atomic invariant now. *)
    close_at_invariant.
    (* Once the user performs a state change to [RightBranch],
       we will be able to close the non-atomic invariant. *)
    iModIntro.
    iIntros "Hbranch Htoken".
    close_na_invariant.
  }

  (* Case: right branch. This case is trivial. *)
  {
    (* We are in the right-hand branch of the conclusion. *)
    iRight. iExists nc. iFrame "Hbranch Htoken".
    (* Close the atomic invariant now. *)
    close_at_invariant.
    (* Once the user performs a state change to [RightBranch],
       we will be able to close the invariant. *)
    iModIntro.
    iIntros "Hbranch Htoken".
    close_na_invariant.
  }

Qed.

Lemma piggybank_discover_zero_debit p N n E F :
  ↑P ⊆ E →
  ↑N ⊆ E →
  ↑N ⊆ F →
  PiggyBank p N n -∗
  na_own p F -∗
  (∀ nc, ▷ LeftBranch nc -∗ ▷ False) ={E}=∗
  PiggyBank p N 0 ∗
  na_own p F.
Proof.
  intros.
  iIntros "#Hpiggy Htoken Hcontradiction".
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
  (* Close the atomic invariant. *)
  close_at_invariant.
  (* Close the non-atomic invariant. *)
  close_na_invariant.
  (* Done. *)
  construct_piggy.

Qed.

End PiggyBank.
