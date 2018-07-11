## Compiling

The project is known to compile with:
 *  Coq 8.7.2
 *  iris-coq dev.2018-04-10.0 (development version of Iris)

To install Iris, follow instructions [there][iris-coq].

To compile the Coq scripts:

    cd src/
    make

The first time (and each time `_CoqProject` is updated), it also creates the
file `Makefile.coq`.

Other recipes are available, such as `all`, `clean` and `userinstall` (Makefile
taken from [here][coqproject]).

To create an archive of the project:

    ./make_archive.sh

[iris-coq]: https://gitlab.mpi-sws.org/FP/iris-coq/blob/master/README.md
[coqproject]: https://blog.zhenzhang.me/2016/09/19/coq-dev.html

## Index of modules

Important modules are highlighted.

 *  `Misc`: some basic things
 *  `Auth_nat`, `Auth_mnat`: simple lemmas about the authoritative resources on
    (ℕ, +) and (ℕ, max)
 *  `Reduction`: generic lemmas about reduction, safety, closedness, fresh
    locations… [should be renamed or split into several files]
 *  `Tactics`: helper tactics to reduce concrete terms
 *  __`Translation`: definition of the translation and syntactic lemmas about
    it__
 *  __`Simulation`: generic definition of `tick`; operational lemmas about the
    translation with that `tick`__
 *  __`TimeCredits`: interface, implementation, and proof of soundness for time
    credits (plus a proof-mode tactic `wp_pay`)__
 *  __`TimeCreditsAltProofs`: alternative proofs of the soundness theorem of
    time credits, that does not rely on the unsafe behavior of `tick`__
 *  __`TimeReceipts`: interface, implementation, and proof of soundness for time
    receipts (both exclusive and persistent)__
 *  `Examples`: a very simple example illustrating the use of time credits to
    specify a program with lists
 *  __`Thunks`: implementation of timed thunks using time credits__
