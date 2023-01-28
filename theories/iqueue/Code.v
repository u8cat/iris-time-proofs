From iris_time.heap_lang Require Import notation.
From iris_time.thunks Require Import LazyCode ThunksCode.

(* Implicit Queues from Okasaki's 11.1 *)

(* digits *)
Notation ZERO := (InjL (LitV LitUnit)).
Notation ONEa v := (InjR v%V).

Notation ONEb v := (InjL v%V).
Notation TWO v1 v2 := (InjR (v1%V, v2%V)).

Notation ZEROV := (InjLV (LitV LitUnit)).
Notation ONEaV v := (InjRV v%V).

Notation ONEbV v := (InjLV v%V).
Notation TWOV v1 v2 := (InjRV (v1%V, v2%V)).

(* queue *)
Notation SHALLOW d := (InjL d%V) (only parsing).
Notation DEEP f m r := (InjR (f%V, m%V, r%V)) (only parsing).
Notation SHALLOWV d := (InjLV d%V) (only parsing).
Notation DEEPV f m r := (InjRV (f%V, m%V, r%V)) (only parsing).

Section ImplicitQueue.

Notation "'match:' e0 'with' | 'SHALLOW' d => e1 | 'DEEP' ( f , m , r ) => e2 'end'" :=
  (Match e0
    d%bind (* => *) e1
    "_p"   (* => *) (let: r%bind := Snd "_p" in
                     let: "_p" := Fst "_p" in
                     let: f%bind := Fst "_p" in
                     let: m%bind := Snd "_p" in
                     e2)
  )
  (e0, e1, d, f, m, r, e2 at level 200, only parsing) : expr_scope.

Notation "'match:' e0 'with' | 'ZERO' => e1 | 'ONEa' v => e2 'end'" :=
  (Match e0
     <>%bind (* => *) e1
     v%bind  (* => *) e2
  )
  (e0, e1, v, e2 at level 200, only parsing) : expr_scope.

Notation "'match:' e0 'with' | 'ONEb' v => e1 | 'TWO' ( v1 , v2 ) => e2 'end'" :=
  (Match e0
     v%bind (* => *) e1
     "_x"   (* => *) (let: v1%bind := Fst "_x" in
                      let: v2%bind := Snd "_x" in
                      e2)
  )
  (e0, v, e1, v1, v2, e2 at level 200, only parsing) : expr_scope.

Definition empty : val :=
  SHALLOWV ZEROV.

Definition is_empty : val := λ: "q",
  match: "q" with
  | SHALLOW "d" =>
    match: "d" with
    | ZERO => #true
    | ONEa <> => #false
    end
  | DEEP (<>, <>, <>) => #false
  end.

Definition snoc : val := rec: "snoc" "q" "y" :=
  match: "q" with
  | SHALLOW "d" =>
    match: "d" with
    | ZERO => SHALLOW (ONEa "y")
    | ONEa "x" => DEEP (TWO "x" "y") (lazy (SHALLOW ZERO)) ZERO
    end
  | DEEP ("f", "m", "r") =>
    match: "r" with
    | ZERO => DEEP "f" "m" (ONEa "y")
    | ONEa "x" => DEEP "f" (lazy ("snoc" (force "m") ("x", "y")))%E ZERO
    end
  end.

Definition head : val := λ: "q",
  match: "q" with
  | SHALLOW "d" =>
    match: "d" with
    | ZERO => #() (* not supposed to happen *)
    | ONEa "x" => "x"
    end
  | DEEP ("f", <>, <>) =>
    match: "f" with
    | ONEb "x" => "x"
    | TWO ("x", <>) => "x"
    end
  end.

Definition tail : val := rec: "tail" "q" :=
  match: "q" with
  | SHALLOW "d" =>
    match: "d" with
    | ZERO => #() (* not supposed to happen *)
    | ONEa <> => SHALLOW ZERO
    end
  | DEEP ("f", "m", "r") =>
    match: "f" with
    | ONEb <> =>
      let: "q" := force "m" in
      if: is_empty "q" then SHALLOW "r" else
        let: "yz" := head "q" in
        let: "y" := Fst "yz" in
        let: "z" := Snd "yz" in
        DEEP (TWO "y" "z")
             (lazy ("tail" "q"))
             "r"
    | TWO (<>, "y") => DEEP (ONEb "y") "m" "r"
    end
  end.

End ImplicitQueue.
