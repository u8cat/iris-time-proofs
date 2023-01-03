From iris_time.heap_lang Require Import notation.
From iris_time Require Import ThunksCode. (* create, force *)

(* Persistent queues from Okasaki's "Purely Functional Data Structures", using
   thunks to achieve constant time amortized complexity.

   This is the queue using the "physicist method" described in Section 6.4.2. *)

Notation "'letq:' ( w , lenf , f , lenr , r ) := e1 'in' e2" :=
  (let: "__x" := e1%E in
   let: w%bind := (Fst (Fst (Fst (Fst "__x")))) in
   let: lenf%bind := (Snd (Fst (Fst (Fst "__x")))) in
   let: f%bind := (Snd (Fst (Fst "__x"))) in
   let: lenr%bind := (Snd (Fst "__x")) in
   let: r%bind := Snd "__x" in
   e2%E)%E
  (at level 200, w, lenf, f, lenr, r at level 1, e1, e2 at level 200)
  : expr_scope.

(* XXX ideally this should be a value, but this is not possible because thunks
   are implemented as a library and thus are not primitive values of the
   language *)
Definition empty : val := λ: <>,
  (#(), #0, create (λ: <>, #()), #0, #()).

Definition checkw : val := λ: "q",
  letq: ("w", "lenf", "f", "lenr", "r") := "q" in
  if: "w" = #() then
    (force "f", "lenf", "f", "lenr", "r")
  else
    ("w", "lenf", "f", "lenr", "r").

Definition rev_aux : val := rec: "rev_aux" "l" := λ: "acc",
  if: "l" = #() then "acc"
  else "rev_aux" (Snd "l") (Fst "l", "acc").

Definition rev : val := λ: "l", rev_aux "l" #().

Definition append : val := rec: "append" "l1" := λ: "l2",
  if: "l1" = #() then "l2"
  else (Fst "l1", "append" (Snd "l1") "l2").

Definition check : val := λ: "q",
  letq: ("w", "lenf", "f", "lenr", "r") := "q" in
  if: "lenr" ≤ "lenf" then
    checkw "q"
  else (
    let: "fv" := force "f" in
    let: "f'" := create (λ: <>, append "fv" (rev "r")) in
    checkw ("fv", "lenf" + "lenr", "f'", #0, #())
  ).

Definition push : val := λ: "q" "x",
  letq: ("w", "lenf", "f", "lenr", "r") := "q" in
  check ("w", "lenf", "f", "lenr" + #1, ("x", "r")).

Definition pop : val := λ: "q",
  letq: ("w", "lenf", "f", "lenr", "r") := "q" in
  if: "w" = #() then NONE else (
    let: "x" := Fst "w" in
    let: "w'" := Snd "w" in
    let: "f'" := create (λ: <>, Snd (force "f")) in
    let: "q'" := check ("w'", "lenf" - #1, "f'", "lenr", "r") in
    SOME ("x", "q'")
  ).
