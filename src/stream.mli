(* A data structure for streams with memoization. *)

type 'a stream

(* Construction. *)

val nil: 'a stream
val cons: 'a -> 'a stream -> 'a stream

(* Destruction. *)

val extract: 'a stream -> 'a * 'a stream

(* Reversal. *)

val rev: 'a list -> 'a stream

(* Concatenation. *)

val (++): 'a stream -> 'a stream -> 'a stream

(* Truncation. *)

val take: int -> 'a stream -> 'a stream
val drop: int -> 'a stream -> 'a stream

