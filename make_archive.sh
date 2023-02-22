#!/bin/sh

ARCHIVE=iris-time-proofs.tar.gz
rm -f ${ARCHIVE}
find theories/ -type f -name '*.v' -exec \
	tar -czvf ${ARCHIVE} Makefile README.md _CoqProject setup.sh {} \+
