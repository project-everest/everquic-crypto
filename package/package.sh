#!/bin/bash

set -e

NAME=quic-crypto
ARCHIVE=$NAME.tar.bz2

ln -s .. $NAME
tar cjf $ARCHIVE $NAME/Dockerfile $NAME/src/QUIC*.fst $NAME/src/QUIC*.fsti $NAME/src/Makefile $NAME/test/* $NAME/Makefile* $NAME/README.md $NAME/package/fstar.sh $NAME/package/*.el
rm $NAME
