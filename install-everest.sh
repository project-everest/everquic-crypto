#!/bin/bash
set -e
git clone https://github.com/project-everest/everest.git
old_pwd="$pwd"
everest_home="$pwd/everest"
cd "$everest_home"
./everest --yes opam
./everest --yes pull
./everest --yes z3
export PATH=$everest_home/z3/bin:$PATH
export FSTAR_HOME=$everest_home/FStar
export KREMLIN_HOME=$everest_home/kremlin
export QD_HOME=$everest_home/quackyducky
export HACL_HOME=$everest_home/hacl-star
export MLCRYPTO_HOME=$everest_home/MLCrypto
export VALE_HOME=$everest_home/vale
if [[ -z "$EVEREST_THREADS" ]]
then
    EVEREST_THREADS=1
fi
OTHERFLAGS='--admit_smt_queries true' ./everest -j $EVEREST_THREADS FStar make kremlin make quackyducky make
OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star vale-fst
OTHERFLAGS='--admit_smt_queries true' make -j $(($EVEREST_THREADS/2)) -C hacl-star compile-gcc-compatible
cd "$old_pwd"
cat >everest-env.sh <<EOF
export PATH=$everest_home/z3/bin:\$PATH
export FSTAR_HOME=$FSTAR_HOME
export KREMLIN_HOME=$KREMLIN_HOME
export QD_HOME=$QD_HOME
export HACL_HOME=$HACL_HOME
export MLCRYPTO_HOME=$MLCRYPTO_HOME
export VALE_HOME=$VALE_HOME
EOF
echo Please set up your environment by running:
echo source everest-env.sh
