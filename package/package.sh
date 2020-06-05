#!/bin/bash

set -e

NAME=quic-crypto
ARCHIVE=$NAME.tar.bz2

ln -s .. $NAME
tar cjf $ARCHIVE \
    $NAME/Dockerfile \
    $NAME/install-everest.sh \
    $NAME/src/*.fst \
    $NAME/src/*.fsti \
    $NAME/src/Makefile \
    $NAME/test/* \
    $NAME/Makefile* \
    $NAME/README.md \
    $NAME/package/package.sh \
    $NAME/package/fstar.sh \
    $NAME/package/*.el \
    $NAME/noheader.txt \
    $NAME/dist/EverQuic.c \
    $NAME/dist/EverQuic.h \
    $NAME/hints/* \
    $(for f in $NAME/dist/*.c $NAME/dist/*.h $NAME/dist/*.def $NAME/dist/Makefile.* ; do if [[ -e $f ]] ; then echo $f ; fi ; done)
rm $NAME
