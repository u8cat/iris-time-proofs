This is the artifact for the POPL 2024 paper "Thunks and Debits in
Separation Logic with Time Credits".

The artifact is provided both as a VirtualBox virtual machine and as a
.tar.gz file.  They both contain the same Coq development, accessible
in the following public GitLab repository:

     https://gitlab.inria.fr/cambium/iris-time-proofs

## The virtual machine

The virtual machine contains the content of the archive, fully
compiled, and all the software needed to compile it.  When booting, it
should automatically log in. In case it is necessary, it can be logged
in using the user "vagrant" and the password "vagrant".

The relevant files are in the directory coq-iris-time on the
desktop. They can be seen using Coqide, which can be run using the
icon on the desktop.

## Building the artifact from the archive

The archive can be compiled by following the instructions below.

### Step 1: Creating an opam switch

[opam](http://opam.ocaml.org/) (version ≥ 2.0) is needed.
Please proceed as follows:

* If opam is not already installed, [install it][install-opam] first,
  then run the following commands:

      opam init
      eval $(opam env)

  (This will create a `~/.opam` directory.)

* Extract the archive, and move down into the `coq-iris-time`
  directory:

      tar -xzvf coq-iris-time.tar.gz
      cd coq-iris-time

* If opam is already installed, create a local switch for the
  project in the current directory:

      opam update
      opam switch create --no-install . ocaml-base-compiler.4.14.1
      eval $(opam env)

### Step 2: Installing the dependencies

In an opam switch as created above, the commands

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
    opam update
    opam pin add -n coq 8.16.1
    make builddep

will pin and install the dependencies at the correct version.

If you want to browse the Coq development using CoqIDE (a graphical,
interactive toplevel for Coq), install it as well:

    opam install coqide

### Step 3: Compiling the proof scripts

When all required libraries can be found (e.g. in an opam switch as
configured above), compile the proof scripts with:

    make -j

Other recipes are available, such as `all`, `clean` and `userinstall`.

[install-opam]: https://opam.ocaml.org/doc/Install.html

## Supporting the claims of the paper

### Piggy banks

The piggy bank construction is formalized in file
`theories/thunks/PiggyBank.v`. Each rule in Figure 2 of the paper is
formalized by a lemma in this file, named after the rule.

### Thunks

The common interface of thunks, base thunks and proxy thunks is
defined as the `CommonThunkAPI` type class in the file
`theories/thunks/ThunksAPI.v`.
The lemma `base_thunk_api` shows that base
thunks implement this API
(this is the second claim in Theorem 4.1).

Base thunks and the `ThunkVal` predicate are defined in file
`theories/thunks/ThunksBase.v`. Each rule in Figure 7 is proved
by a lemma in the same file, named after the rule
(this is the last claim in Theorem 4.1).
The rule Thunk-Create for base thunks is proved by lemma
`base_thunk_create`
(this is the first claim in Theorem 4.1).

Proxy thunks are defined in the file
`theories/thunks/ThunksStep.v`.
Theorem 4.2 is proved
by the lemma `proxythunk_consequence`
and by the instance declaration `step_thunk_api`.

Thunks are defined in the file `theories/thunks/ThunksFull.v`.
Theorem 4.3
is proved by
the lemmas `thunk_create` and `thunk_consequence`.
and by the instance declaration `thunk_api`.

### Height-indexed thunks

Height-indexed thunks are defined in the file
`theories/thunks/HThunks.v`. The rules in Figure 11 are formalized by
lemmas whose name should be self-explanatory, except for rule
`HThunk-Inc-Height-Debit`, which is split into two lemmas,
named `hthunk_covariant_in_h` and
`hthunk_increase_debt`.

### Streams

The code of the stream library is given in the file
`theories/streams/StreamsCode.v`, and its specification is formalized in
file `theories/streams/Streams.v`.

The rules of Figure 13 are formalized by lemmas with the same name, except
for `Stream-Increase-Height`, which is proved by the lemma
`stream_covariant`.

The rules of Figure 14 are constructors of
the inductive predicate `subdebits`.

Rule `Sub-Variance` is split into two lemmas,
`subdebits_covariant_in_slack`
and `subdebits_contravariant_in_rest`.

Rule `Sub-Refl` is backed by lemma `subdebits_reflexive`.

Rule `Sub-Trans` is backed by lemma `subdebits_transitive`.

Rule `Sub-Append` is backed by lemma `subdebits_app`.

Rule `Sub-Add-Slack` is backed by lemma `subdebits_add_slack`.

Rule `Sub-Repeat` is backed by lemma `subdebits_repeat`.

Lemma 6.1 is backed by lemma `subdebits_alternate_characterization`.

### Banker's queue

The code of the banker's queue is in the file
`theories/bqueue/Code.v`. Its specification is in the file
`theories/bqueue/Proof.v`.

Rule `Banker-Persistent` is proved by lemma `is_queue_persistent`.

Rule `Banker-Empty` is proved by lemma `empty_spec`.

Rule `Banker-Snoc` is proved by lemma `snoc_spec`.

Rule `Banker-Extract` is proved by lemma `extract_spec`.

Rule `Banker-Check` is proved by lemma `check_spec`.

### The physicist's queue, implicit queues.

The physicist's queue is formalized in the directory `theories/pqueue`.

Implicit queues are formalized in the directory `theories/iqueue`.
