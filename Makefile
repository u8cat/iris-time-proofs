# This prevents Coq from producing stack backtraces.
export OCAMLRUNPARAM=

# Generate and include Makefile.coq.
-include Makefile.coq

# This recipe generates Makefile.coq.
Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

# To clean up everything, trust git.
# Do not remove the local opam switch, though.
.PHONY: clean
clean::
	@ git clean -fX --exclude="!_opam"

# This cleans up everything including the local opam switch.
.PHONY: realclean
realclean:
	@ git clean -fX
