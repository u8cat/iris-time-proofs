type 'a digit01 = ZERO | ONEa of 'a
type 'a digit12 = ONEb of 'a | TWO of 'a * 'a

type 'a queue =
  | SHALLOW of 'a digit01
  | DEEP of 'a digit12 * ('a * 'a) queue Lazy.t * 'a digit01

let empty = SHALLOW ZERO
let is_empty = function SHALLOW ZERO -> true | _ -> false

let rec snoc : type a. a queue -> a -> a queue = fun q y ->
  match q with
  | SHALLOW ZERO -> SHALLOW (ONEa y)
  | SHALLOW (ONEa x) -> DEEP (TWO (x, y), lazy empty, ZERO)
  | DEEP (f, m, ZERO) -> DEEP (f, m, ONEa y)
  | DEEP (f, m, ONEa x) -> DEEP (f, lazy (snoc (Lazy.force m) (x, y)), ZERO)

let head : type a. a queue -> a = function
  | SHALLOW ZERO -> raise (Invalid_argument "ImplicitQueue.head")
  | SHALLOW (ONEa x) -> x
  | DEEP (ONEb x, _, _) -> x
  | DEEP (TWO (x, _), _, _) -> x

let rec tail : type a. a queue -> a queue = function
  | SHALLOW ZERO -> raise (Invalid_argument "ImplicitQueue.tail")
  | SHALLOW (ONEa _) -> SHALLOW ZERO
  | DEEP (TWO (_, y), m, r) -> DEEP (ONEb y, m, r)
  | DEEP (ONEb _, m, r) ->
    let q = Lazy.force m in
    if is_empty q then SHALLOW r else
      let (y, z) = head q in
      DEEP (TWO (y, z), lazy (tail q), r)
