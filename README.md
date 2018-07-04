## Compiling

To compile the Coq scripts:

    cd src/
    make

The first time (and each time `_CoqProject` is updated), it also creates the
file `Makefile.coq`.

Other recipes are available, such as `all`, `clean` and `userinstall` (Makefile
taken from [here][coqproject]).

[coqproject]: https://blog.zhenzhang.me/2016/09/19/coq-dev.html

## Index of modules

 *  `Misc`: some basic things
 *  `Auth_nat`, `Auth_mnat`: simple lemmas about the authoritative resources on
    (ℕ, +) and (ℕ, max)
 *  `Reduction`: generic lemmas about reduction, safety, closedness, fresh
    locations… [should be renamed or split into several files]
 *  `Tactics`: tactics that help reducing concrete terms
 *  `Translation`: definition of the translation and syntactic lemmas about it
 *  `Simulation`: Lemmas about the operational semantics of the translation
 *  `TimeCredits`: implementation of time credits
 *  `TimeReceipts`: implementation of time receipts
 *  `Examples`: a (too) simple example illustrating the use of time credits
 *  `LibThunk`: implementation of timed thunks using time credits [WIP, does not
    compile for now]
 *  `test`: an alternative proof of the main theorem of time credits, that does
    not rely on the unsafe behaviour of `tick` [to be merged into `TimeCredits`]
