From iris_time.heap_lang Require Import notation.
From iris_time.streams Require Streams.

(* The Banker's Queue from Okasaki's 6.3.2. *)

Notation "'letq:' ( lenf , f , lenr , r ) := e1 'in' e2" :=
  (let: "__x" := e1%E in
   let: lenf%bind := Fst (Fst (Fst "__x")) in
   let: f%bind := Snd (Fst (Fst "__x")) in
   let: lenr%bind := Snd (Fst "__x") in
   let: r%bind := Snd "__x" in
   e2%E)%E
  (at level 200, lenf, f, lenr, r at level 1, e1, e2 at level 200)
  : expr_scope.

Notation NIL := (InjL (LitV LitUnit)).
Notation CONS v vs := (InjR (v%V, vs%V)).

Definition empty : val := λ: <>,
  (#0, Streams.nil, #0, NIL).

Definition cons : val := λ: "x" "q",
  letq: ("lenf", "f", "lenr", "r") := "q" in
  ("lenf" + #1, Streams.cons "x" "f", "lenr", "r").

Definition check : val := λ: "q",
  letq: ("lenf", "f", "lenr", "r") := "q" in
  if: "lenr" ≤ "lenf" then
    "q"
  else
    ("lenf" + "lenr", Streams.append "f" (Streams.rev "r"), #0, NIL).

Definition snoc : val := λ: "q" "x",
  letq: ("lenf", "f", "lenr", "r") := "q" in
  check ("lenf", "f", "lenr" + #1, CONS "x" "r").

Definition is_empty : val := λ: "q",
  letq: ("lenf", "f", "lenr", "r") := "q" in
  "lenf" = #0.

Definition extract : val := λ: "q",
  letq: ("lenf", "f", "lenr", "r") := "q" in
  let: "p" := Streams.extract "f" in
  let: "x" := Fst "p" in
  let: "f'" := Snd "p" in
  let: "q'" := check ("lenf" - #1, "f'", "lenr", "r") in
  ("x", "q'").
