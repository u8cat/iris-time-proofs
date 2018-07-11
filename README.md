## Requirements

The project is known to compile with:
 *  Coq 8.7.2
 *  coq-iris dev.2018-04-10.0 (development version of Iris)

### Step 1: Install opam

See instructions [there][install-opam]; then:

    opam init --comp=4.06.1

(This will create a `~/.opam` directory.)

### Step 2: Install Coq

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install -j4 -v coq.8.7.2

If you want to use CoqIDE (a graphical, interactive toplevel for Coq), install
it as well:

    opam install coqide.8.7.2

### Step 3: Install a development version of Iris

    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git
    opam update

    # to get a specific development version:
    opam pin add coq-iris -k version dev.2018-04-10.0
    # OR, to get the latest development version (beware that the analysis of
    # dependencies can be very slow):
    opam install coq-iris

(This will also install `coq-stdpp`, another Coq library made available through
the same repo.)

More info on the Coq development of Iris: [there][coq-iris].

## Compiling

To compile the Coq scripts:

    cd src/
    make

The first time (and each time `_CoqProject` is updated), it also creates the
file `Makefile.coq`.

Other recipes are available, such as `all`, `clean` and `userinstall` (Makefile
taken from [here][coqproject]).

To create an archive of the project:

    ./make_archive.sh

[install-opam]: https://opam.ocaml.org/doc/Install.html
[coq-iris]: https://gitlab.mpi-sws.org/FP/iris-coq
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
    credits (plus a proof-mode tactic `wp_tick`)__
 *  __`TimeCreditsAltProofs`: alternative proofs of the soundness theorem of
    time credits, that does not rely on the unsafe behavior of `tick`__
 *  __`TimeReceipts`: interface, implementation, and proof of soundness for time
    receipts (both exclusive and persistent)__
 *  `Examples`: a very simple example illustrating the use of time credits to
    specify a program with lists
 *  __`Thunks`: implementation of timed thunks using time credits__
