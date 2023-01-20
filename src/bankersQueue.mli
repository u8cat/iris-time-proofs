(* A data structure for queues, due to Chris Okasaki. All operations
   require worst-case constant time, except [extract], which requires
   amortized constant time. *)

type 'a queue

(* Construction. *)

val empty: 'a queue

(* Insertion at the left end. *)

val cons: 'a -> 'a queue -> 'a queue

(* Insertion at the right end. *)

val snoc: 'a queue -> 'a -> 'a queue

(* Test for emptiness. *)

val is_empty: 'a queue -> bool

(* Removal at the left end. *)

val extract: 'a queue -> 'a * 'a queue

(* Cardinal. *)

val cardinal: 'a queue -> int

