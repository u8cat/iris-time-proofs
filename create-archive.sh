#!/bin/bash
set -euo pipefail
IFS=$'\n\t'

if command -v gnutar >/dev/null ; then
  # On MacOS, run "sudo port install gnutar" to obtain gnutar.
  TAR=gnutar
else
  TAR=tar
fi

ARCHIVE=coq-iris-time

rm -rf ${ARCHIVE} ${ARCHIVE}.tar.gz

mkdir ${ARCHIVE}

cp -r \
  .gitignore \
  Makefile \
  README.md \
  theories \
  setup.sh \
  _CoqProject \
  ${ARCHIVE}

$TAR cvfz ${ARCHIVE}.tar.gz \
  --exclude-ignore-recursive=.gitignore \
  --owner=0 --group=0 \
  ${ARCHIVE}

rm -rf ${ARCHIVE}
