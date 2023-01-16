From stdpp Require Import namespaces.
From iris.base_logic.lib Require Import na_invariants.
From iris_time.heap_lang Require Import proofmode notation.
From iris_time Require Import TimeCredits Auth_max_nat.

(* -------------------------------------------------------------------------- *)

Section PiggyBank.

Context `{timeCreditHeapG Σ}.
Context `{inG Σ (authR max_natUR)}.                   (* γpaid *)
Context `{na_invG Σ}.
Notation iProp := (iProp Σ).

Implicit Type p : na_inv_pool_name.
Implicit Type N : namespace.
Implicit Type n nc ac : nat.
Implicit Type R : iProp.
Implicit Type φ : val → iProp.
Implicit Type γpaid : gname.

Variable LeftBranch  : (* nc: *) nat → iProp.
Variable RightBranch : (* nc: *) nat → iProp.

Definition PiggyBankInvariant γpaid nc : iProp :=
  ∃ ac,
      own γpaid (● MaxNat ac)
    ∗ ((LeftBranch nc ∗ TC ac) ∨ (RightBranch nc ∗ ⌜ nc ≤ ac ⌝)).

Definition PiggyBank p N n : iProp :=
  ∃ γpaid nc,
      na_inv p N (PiggyBankInvariant γpaid nc)
    ∗ own γpaid (◯ MaxNat (nc - n)).

(* -------------------------------------------------------------------------- *)

(* Local tactics, for clarity. *)

Local Ltac destruct_piggy :=
  iDestruct "Hpiggy" as (γpaid nc) "(Hinv & Hγpaid◯)".

Local Ltac open_invariant :=
  iDestruct (na_inv_acc with "Hinv Htoken") as ">(Hbank & Htoken & Hclose)";
    [set_solver | set_solver |];
  iDestruct "Hbank" as (ac) "(>Hγpaid● & Hbank)".

Local Ltac case_analysis :=
  iDestruct "Hbank" as "[ (Hbranch & >Hac) | (Hbranch & >%Hncac) ]".

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

Local Ltac close_invariant ac :=
  iMod ("Hclose" with "[-]") as "$"; [
    (* Subgoal: prove that the invariant holds *)
    iFrame "Htoken"; iNext; iExists ac; iFrame "Hγpaid●"
  | (* Subgoal: after the invariant is closed *)
    iModIntro (* We assume that we do not need the modality any more. *)
  ].

Local Ltac construct_piggy :=
  iExists _, _; iFrame "Hinv"; weaken_white_bullet.

(* -------------------------------------------------------------------------- *)

(* Properties. *)

Global Instance piggybank_persistent p N n :
  Persistent (PiggyBank p N n).
Proof using.
  exact _.
Qed.

Lemma piggybank_discover_zero_debit p N n E F :
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
  open_invariant.
  case_analysis.

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
  (* Close the invariant. *)
  close_invariant ac.
  { iRight. eauto. }
  construct_piggy.

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
  TC 0 -∗
  LeftBranch nc ={E}=∗
  PiggyBank p N nc.
Proof.
  iIntros "Htc Hleft".
  (* Allocate the ghost cell γpaid. *)
  iMod (auth_max_nat_alloc 0) as (γpaid) "[Hγpaid● #Hγpaid◯]".
  (* Allocate an invariant. The number of credits in the bank is zero. *)
  iAssert (PiggyBankInvariant γpaid nc) with "[-]" as "Hbank".
  { iExists 0. iFrame "Hγpaid●". iLeft. eauto. }
  iMod (na_inv_alloc with "Hbank") as "Hinv";
  iModIntro.
  construct_piggy.
Qed.

Lemma piggybank_break p N E F :
  let token := na_own p F in
  let token' := na_own p (F ∖ ↑N) in
  ↑N ⊆ E →
  ↑N ⊆ F →
  PiggyBank p N 0 -∗
  token
   ={E}=∗
   ( ∃ nc,
      ▷ LeftBranch nc ∗ TC nc ∗ token' ∗
     (▷ RightBranch nc -∗ token' ={E}=∗ token)
   ) ∨
   ( ∃ nc,
      ▷ RightBranch nc ∗ token' ∗
     (▷ RightBranch nc -∗ token' ={E}=∗ token)
   ).
Proof.
  intros.
  iIntros "#Hpiggy Htoken".
  destruct_piggy.
  rewrite Nat.sub_0_r.
  open_invariant.
  case_analysis;
  iModIntro.

  (* Case: left branch. *)
  {
    (* We are in the left-hand branch of the conclusion. *)
    iLeft. iExists nc. iFrame "Hbranch Htoken".
    (* The number of debits is zero, so we learn [nc ≤ ac]. *)
    exploit_white_bullet.
    (* Therefore, we have the necessary time credits at hand. *)
    iDestruct (TC_weaken _ _ Hleq with "Hac") as "$".
    (* Once the user performs a state change to [RightBranch nc],
       we will be able to close the invariant. *)
    iIntros "Hbranch Htoken".
    close_invariant ac; [| done ].
    { iRight. eauto. }
  }

  (* Case: right branch. This case is trivial. *)
  {
    (* We are in the right-hand branch of the conclusion. *)
    iRight. iExists nc. iFrame "Hbranch Htoken".
    (* Once the user performs a state change to [RightBranch nc],
       we will be able to close the invariant. *)
    iIntros "Hbranch Htoken".
    close_invariant ac; [| done ].
    { iRight. eauto. }
  }

Qed.

Lemma piggybank_pay k p N E F n :
  ↑N ⊆ E →
  ↑N ⊆ F →
  na_own p F -∗ PiggyBank p N n -∗   TC k   ={E}=∗
  na_own p F  ∗ PiggyBank p N (n-k).
Proof.
  intros.
  iIntros "Htoken #Hpiggy Hk".
  destruct_piggy.
  open_invariant.

  (* We learn [nc - n ≤ ac]. *)
  exploit_white_bullet.

  (* Increment the ghost payment record from [ac] to [ac + k]. *)
  increase_black_bullet k.
  iClear "Hγpaid◯".
  create_white_bullet.

  (* Perform a case analysis. *)
  case_analysis.

  (* Case: left branch. *)
  {
    (* We have [ac + k] time credits. *)
    iCombine "Hac Hk" as "Hac".
    (* The invariant can be closed. *)
    close_invariant (ac + k).
    { iLeft. eauto with iFrame. }
    (* Our updated fragmentary view of the ghost cell γpaid
       allows us to produce an updated [PiggyBank] assertion. *)
    construct_piggy.
  }

  (* Case: right branch. *)
  {
    (* The invariant can be closed. In this case, no new time credits are
       stored in the invariant. The extra payment is wasted. *)
    iClear "Hk".
    close_invariant (ac + k).
    { iRight. eauto with lia iFrame. }
    construct_piggy.
  }

Qed.

End PiggyBank.
