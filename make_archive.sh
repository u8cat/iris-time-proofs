ARCHIVE=iris-time-proofs.tar.gz
rm -f $ARCHIVE
tar -czvf $ARCHIVE README.md Makefile _CoqProject theories/*.v
