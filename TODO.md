* Prove specs for [lazy e] and [lazy v]
  at the level of the Thunk API,
  without connection with streams.
  Then, hoist these specs to the level of the GThunk API.
  Then, deduce the lemmas lazy_spec and lazy_spec_val in Streams.

* Think about diminishing the problems with the translation.
  What conventions do we want?
  + Always keep the translation at the root of the expression?
  + Always push the translation down to the leaves?
  + Or reconstruct Iris$ from scratch in a primitive manner,
    without a translation?
  When a predicate is indexed with a value (or a list of values, etc.),
  + Do we want to index it with a source value?
  + Or with a translated value?
  E.g., `Stream` is currently indexed with translated values.
