open Stream

(* A data structure for queues, due to Chris Okasaki. All operations
   require worst-case constant time, except [extract], which requires
   amortized constant time. *)

(* The data structure has the following invariants: [lenf] is the length
   of [f]; [lenr] is the length of [r]; [lenf] is greater than or equal
   to [lenr]. That is, there are never too many elements in [r]. *)

type 'a queue = {
  lenf: int;
  f: 'a stream;
  lenr: int;
  r: 'a list;
}

(* Construction. *)

let empty : 'a queue = {
  lenf = 0;
  f = nil;
  lenr = 0;
  r = [];
}

(* Insertion at the left end. *)

let cons x q = { q with
  lenf = q.lenf + 1;
  f = cons x q.f;
}

(* Re-balancing. *)

(* When [check] is invoked, the invariant is violated at most by one unit,
   because [lenf] has just been decreased or [lenr] has just been increased.
   Thus, we have [lenf + 1 >= lenr]. We check whether the invariant is in
   fact still valid, i.e. whether [lenf >= lenr] holds. If it does, there
   is nothing to do. If it does not, then we have [lenr > lenf], which
   implies [lenf + 1 = lenr]. Thus, the front and rear sequences have
   comparable lengths. This means that, in the stream [q.f ++ rev q.r],
   the cost of forcing the thunk [rev q.r] can be spread over the elements
   of [q.f], at a constant cost per element. *)

let check ({ lenf = lenf ; f = f; lenr = lenr; r = r } as q) =
  assert (lenf + 1 >= lenr);
  if lenf >= lenr then
    q
  else begin
    assert (lenf + 1 = lenr);
    {
      lenf = lenf + lenr;
      f = f ++ rev r;
      lenr = 0;
      r = [];
    }
  end

(* Insertion at the right end. *)

let snoc q x = check { q with
  lenr = q.lenr + 1;
  r = x :: q.r;
}

(* Test for emptiness. *)

let is_empty q =
  q.lenf = 0

(* Removal at the left end. *)

let extract q =
  let x, f = extract q.f in
  x,
  check { q with
    f = f;
    lenf = q.lenf - 1;
  }

(* Cardinal. *)

let cardinal q =
  q.lenf + q.lenr

