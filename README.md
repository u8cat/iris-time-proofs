## Requirements

The project is known to compile with:
 *  Coq 8.7.2
 *  coq-iris dev.2018-10-13.0.7041c043 (development version of Iris)
 *  coq-tlc 20180316 (for the proof of union-find)

### Step 1: Install opam

_If opam is not already installed:_ See instructions [there][install-opam] to
install it; then:

    opam init --comp=4.06.1

(This will create a `~/.opam` directory.)

_If opam is already installed:_ Create a new switch for the project:

    opam switch -A 4.06.1 iris-time-proofs

### Step 2: Install Coq

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam update
    opam install -j4 -v coq.8.7.2

If you want to use CoqIDE (a graphical, interactive toplevel for Coq), install
it as well:

    opam install coqide.8.7.2

### Step 3: Install a development version of Iris

Do _not_ install the latest development version, as this project does not
support it.

    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git
    opam update
    opam pin add coq-iris -k version dev.2018-10-13.0.7041c043

(This will also install `coq-stdpp`, another Coq library made available through
the same repo.)

More info on the Coq development of Iris: [there][coq-iris].

### Step 4: Install TLC

The TLC library is required by the proof of the union-find algorithm. It is
available through an opam package in the Coq repository (added earlier).

    opam install coq-tlc

TODO: version?

## Compiling

To compile the Coq scripts:

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
 *  __`ClockedIntegers`: reconstruction of Clochard’s integer types (`onetime`
    and `peano`) using time receipts__

### From the paper to the Coq code

#### Generic translation and “tick”

The basic properties of the translation are proven in `Translation.v` (for
example, `translation_subst` and `translation_of_val`).

In `Simulation.v`:

 *  The operational semantics of “tick” in the nonzero case is given by lemma
    `exec_tick_success`.
 *  The “Forward Simulation” lemma is `simulation_exec_success`.
 *  The “Forward Simulation of Unsafe Behaviors” lemma corresponds roughly to
    `safe_translation__safe_here`.
 *  The “Safety Transfer” lemma is `adequate_translation__adequate` (in the Coq
    development, by contrast with the paper, not only do we prove safety of
    programs, but also their _adequacy_ with respect to some formula φ; this is
    not a difficult property to transfer anyway).

#### Time credits

In `TimeCredits.v`:

 *  The “Credit Exhaustion” lemma is `simulation_exec_failure_now`.
 *  The “Soundness of the Time Credit Translation” lemma is
    `simulation_exec_failure`.
 *  The “Time Credit Initialization” lemma does not have an exact counterpart in
    the Coq development, but corresponds roughly to a portion of the proof of
    `spec_tctranslation__adequate`. The fact that our implementation matches the
    interface is stated by `TC_implementation`.
 *  The “Soundness of Iris^$ ” lemma is
    `abstract_spec_tctranslation__adequate_and_bounded`.

#### Time receipts

In `TimeReceipts.v`:

 *  The “Time Receipt Initialization” lemma does not have an exact counterpart
    in the Coq development, but corresponds roughly to a portion of the proof of
    `spec_trtranslation__adequate_translation`. The fact that our implementation
    matches the interface is stated by `TR_implementation`.
 *  The “Credit Exhaustion” lemma is `simulation_exec_failure_now`.
 *  The “Soundness of Iris^⧗ ” lemma is `abstract_spec_trtranslation__adequate`.
