From iris_time.heap_lang Require Import notation.

(* This file contains a HeapLang implementation of thunks, as presented in the
   ESOP 2019 paper. It contains just code; no specs or proofs. *)

(* -------------------------------------------------------------------------- *)

(* Notations that make the HeapLang code more readable. *)

Notation UNEVALUATED f := (InjL f%V) (only parsing).
Notation EVALUATED v := (InjR v%V) (only parsing).
Notation UNEVALUATEDV f := (InjLV f%V) (only parsing).
Notation EVALUATEDV v := (InjRV v%V) (only parsing).
Notation "'match:' e0 'with' 'UNEVALUATED' x1 => e1 | 'EVALUATED' x2 => e2 'end'" :=
  (Match e0 x1%bind e1 x2%bind e2)
  (e0, e1, x2, e2 at level 200, only parsing) : expr_scope.

(* -------------------------------------------------------------------------- *)

(* The HeapLang code. *)

(* There are only two operations on thunks: [create] and [force]. *)

(* A thunk is either white (unevaluated) or black (evaluated). There is no
   grey color (which would mean that a thunk is currently being evaluated) and
   there is no runtime check against reentrancy. Yet, reentrancy is dangerous:
   we wish to guarantee that the function [f] is invoked at most once, but a
   reentrant call to [force] could violate this property. Thus, reentrancy
   must be statically ruled out by the specification of thunks. *)

Definition create : val :=
  λ: "f",
    ref (UNEVALUATED "f").

Definition force : val :=
  λ: "t",
    match: ! "t" with
      UNEVALUATED "f" =>
        let: "v" := "f" #() in
        "t" <- (EVALUATED "v") ;;
        "v"
    | EVALUATED "v" =>
        "v"
    end.
