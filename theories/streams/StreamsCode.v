From iris_time.heap_lang Require Import notation.
From iris_time Require Import ThunksCode LazyCode.

(* This file contains HeapLang code for streams. *)

Definition NIL : expr :=
  InjL (LitV LitUnit).

Definition NILV : val :=
  InjLV (LitV LitUnit).

Definition CONS (v vs : expr) : expr :=
  InjR (v, vs).

Definition CONSV (v vs : val) : val :=
  InjRV (v, vs).

Notation
  "'match:' e0 'with' 'NIL' => e1 | 'CONS' ( x , xs ) => e2 'end'" :=
  (Match e0
    <>%bind (* => *) e1
    xs%bind (* => *) (Lam x%bind (Lam xs%bind e2%E (Snd xs%bind)) (Fst xs%bind))
                     (* this is let: x := Fst xs in let: xs := Snd xs in e2 *)
  )
  (e0, e1, x, xs, e2 at level 200, only parsing) : expr_scope.

(* The algebraic data type of streams would be defined in OCaml as follows:

  type 'a stream =
    'a cell Lazy.t

  and 'a cell =
    | Nil
    | Cons of 'a * 'a stream

 *)

(* TODO in the paper, [nil] has type [unit → stream] *)
Definition nil : expr := (* : stream *)
  lazy NIL.

Definition cons : val := (* : val → stream → stream *)
  λ: "x" "xs",
    lazy (CONS "x" "xs").

Definition uncons : val := (* : stream → val × stream *)
  λ: "xs",
    match: force "xs" with
      NIL              => #() (* this case must not happen *)
    | CONS ("x", "xs") => ("x", "xs")
    end.

Definition revl_append : val := (* : list → cell → cell *)
  rec: "revl_append" "xs" "ys" :=
    match: "xs" with
      NIL              => "ys"
    | CONS ("x", "xs") => "revl_append" "xs" (CONS "x" (lazy "ys"))
    end.

Definition revl : val := (* : list → stream *)
  λ: "xs",
    lazy (revl_append "xs" NIL).

Definition append : val := (* : stream → stream → stream *)
  rec: "append" "xs" "ys" :=
    lazy (
      match: force "xs" with
        NIL              => force "ys"
      | CONS ("x", "xs") => CONS "x" ("append" "xs" "ys")
      end
    ).
