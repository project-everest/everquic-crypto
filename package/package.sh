#!/bin/bash

set -e

NAME=quic-crypto
ARCHIVE=$NAME.tar

ln -s .. $NAME
tar cf $ARCHIVE $NAME/src/QUIC*.fst $NAME/src/QUIC*.fsti $NAME/test/* $NAME/Makefile* $NAME/README.md $NAME/package/fstar.sh $NAME/package/*.el
rm $NAME
ln -s . $NAME
tar rf $ARCHIVE $NAME/Dockerfile
rm $NAME
bzip2 $ARCHIVE
