#!/bin/bash

set -e

NAME=quic-crypto
ARCHIVE=$NAME.tar

ln -s .. $NAME
tar cf $ARCHIVE $NAME/src/QUIC*.fst $NAME/src/QUIC*.fsti $NAME/test/* $NAME/Makefile*
rm $NAME
ln -s . $NAME
tar rf $ARCHIVE $NAME/Dockerfile $NAME/README
rm $NAME
bzip2 $ARCHIVE
