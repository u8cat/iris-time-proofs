From iris_time.heap_lang Require Import notation.
From iris_time Require Import Translation.
From iris_time Require Import ThunksCode.

(* This file defines the syntactic sugar [lazy e]. *)

(* -------------------------------------------------------------------------- *)

(* [lazy e] is syntactic sugar for [create (λ_.e)].

   Thus, [e] is an expression, whose evaluation is suspended.
   Despite appearances, [lazy e] is NOT a function application. *)

Definition lazy (e : expr) :=
  (create (Lam <>%bind e))%E.

(* -------------------------------------------------------------------------- *)

(* [lazy] commutes with substitution. *)

Lemma subst_lazy x v e :
  subst x v (lazy e) = lazy (subst x v e).
Proof.
  reflexivity.
Qed.

#[export] Hint Rewrite subst_lazy : push_subst.

(* -------------------------------------------------------------------------- *)

(* [lazy] commutes with the tick translation, as follows. *)

Section Tick.

Context `{Tick}.

Lemma translate_lazy_expr (e : expr) :
  « lazy e » = tick « create » (tick (Lam <> «e»)).
Proof.
  reflexivity.
Qed.

Lemma translate_lazy_val (v : val) :
  « lazy v » = tick «create»%V (tick (Lam <> « v »%V)).
Proof.
  reflexivity.
Qed.

End Tick.

(* -------------------------------------------------------------------------- *)

(* We make [lazy] an opaque construction, so as to prevent the expansion of
   this sugar. *)

Global Opaque lazy.
