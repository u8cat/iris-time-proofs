## Building

### Step 1: Creating an opam switch

_If opam is not already installed:_ See instructions [there][install-opam] to
install it; then:

    opam init
    eval $(opam env)

(This will create a `~/.opam` directory.)

_If opam (≥ 2.0) is already installed:_ Create a local switch for the project in the current directory:

    opam update
    opam switch create --no-install . ocaml-base-compiler.5.1.0
    eval $(opam env)

### Step 2: Installing the dependencies

In an opam switch as created above, the commands

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev git+https://gitlab.mpi-sws.org/iris/opam.git
    opam update
    opam pin add -n coq 8.17.1
    make builddep

will pin and install the dependencies at the correct version.

If you want to browse the Coq development using CoqIDE (a graphical, interactive
toplevel for Coq), install it as well:

    opam install coqide

### Step 3: Compiling the proof scripts

When all required libraries can be found (e.g. in an opam switch as configured
above), compile the proof scripts with:

    make -j

Other recipes are available, such as `all`, `clean` and `userinstall`.

[install-opam]: https://opam.ocaml.org/doc/Install.html
