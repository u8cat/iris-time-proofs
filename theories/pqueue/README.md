# Okasaki's persistent queues using the physicist method

*Author:* Armaël Guéneau.

Here are the code and proof for the structure described in §6.4.2 of Okasaki's
book, which uses the physicist's method. It is simpler than the queue based on
the banker's method. Here, each instance of the data structure involves only a
single thunk.

It is still quite interesting to see how to account for reentrancy and manage
namespaces and `na_own` tokens, as we do need to reason about thunks forcing
other thunks. In the end, a relatively simple strategy suffices: associate a
given thunk with a namespace indexed by an integer identity. Then, this thunk
has permission to force all thunks whose id is less than its own (and thus is
given access to the corresponding `na_own` tokens). When creating a new thunk
that wraps an existing thunk, we simply pick the successor of the identity of
the wrapped thunk as the identity of the new thunk.
