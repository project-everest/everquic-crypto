#!/bin/bash
set -e
set -x
git clone --branch taramana_krml_rename https://github.com/project-everest/everest.git
old_pwd="$PWD"
everest_home="$old_pwd/everest"
cd "$everest_home"
git checkout b0d4d92bff399618e751881771f5b49f57069cbe
./everest --yes opam
./everest --yes reset
./everest --yes z3
export PATH=$everest_home/z3/bin:$PATH
export FSTAR_HOME=$everest_home/FStar
export KRML_HOME=$everest_home/karamel
export EVERPARSE_HOME=$everest_home/everparse
export HACL_HOME=$everest_home/hacl-star
export MLCRYPTO_HOME=$everest_home/MLCrypto
export VALE_HOME=$everest_home/vale
if [[ -z "$EVEREST_THREADS" ]]
then
    EVEREST_THREADS=1
fi
OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS FStar make karamel make everparse make
OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2+1)) -C hacl-star vale-fst
OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2+1)) -C hacl-star compile-gcc-compatible
cd "$old_pwd"
cat >everest-env.sh <<EOF
export PATH=$everest_home/z3/bin:\$PATH
export FSTAR_HOME=$FSTAR_HOME
export KRML_HOME=$KRML_HOME
export EVERPARSE_HOME=$EVERPARSE_HOME
export HACL_HOME=$HACL_HOME
export MLCRYPTO_HOME=$MLCRYPTO_HOME
export VALE_HOME=$VALE_HOME
EOF
echo Please set up your environment by running:
echo source everest-env.sh
