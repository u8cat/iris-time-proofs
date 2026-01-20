From Stdlib Require Export ssreflect.
From stdpp Require Export base list relations.

Tactic Notation "make_eq" constr(t) "as" ident(x) ident(E) :=
  set x := t ;
  assert (t = x) as E by reflexivity ;
  clearbody x.

Lemma take_cons {A : Type} (n : nat) (x : A) (xs : list A) :
  (0 < n)%nat → take n (x :: xs) = x :: take (n-1)%nat xs.
Proof.
  intros <- % Nat.succ_pred_pos. by rewrite /= Nat.sub_0_r.
Qed.

Lemma drop_cons {A : Type} (n : nat) (x : A) (xs : list A) :
  (0 < n)%nat → drop n (x :: xs) = drop (n-1)%nat xs.
Proof.
  intros <- % Nat.succ_pred_pos. by rewrite /= Nat.sub_0_r.
Qed.

Lemma nsteps_split `{R : relation A} m n x y :
  nsteps R (m+n) x y →
  ∃ (z : A), nsteps R m x z ∧ nsteps R n z y.
Proof.
  revert x ; induction m as [ | m' IH ] ; intros x H.
  - exists x. split ; [ constructor | assumption ].
  - inversion H as [ (*…*) | sum' x_ z y_ Hxz Hzy Esum' Ex Ey ] ; clear dependent sum' x_ y_.
    apply IH in Hzy as (ω & Hzω & Hωy).
    exists ω. split ; first econstructor ; eassumption.
Qed.

Lemma repeat_succ_last A (a : A) n :
  repeat a (S n) = repeat a n ++ [a].
Proof. rewrite /= repeat_cons //. Qed.

Lemma map_repeat A B (f : A → B) a n :
  map f (repeat a n) = repeat (f a) n.
Proof. induction n; cbn; eauto; rewrite IHn //. Qed.

Lemma pow2_pos n : 1 ≤ 2 ^ n.
Proof.
  pose proof (Nat.pow_le_mono_r 2 0 n ltac:(lia) ltac:(lia)).
  cbn in *; lia.
Qed.
