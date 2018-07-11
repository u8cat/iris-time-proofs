ARCHIVE=iris-time-proofs.tar.gz
rm -f $ARCHIVE
tar -czvf $ARCHIVE README.md src/Makefile src/_CoqProject src/*.v
