#!/usr/bin/env bash

#set -x

target=$1
out_file=$2
threads=$3
branchname=$4

function export_home() {
    if command -v cygpath >/dev/null 2>&1; then
        export $1_HOME=$(cygpath -m "$2")
    else
        export $1_HOME="$2"
    fi
}

function raise () {
    return $1
}

function exec_build() {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false >$status_file

    export CC=gcc-6
    make -j $threads &&
    { echo -n true >$status_file ; }

    if [[ $(cat $status_file) != "true" ]]; then
        echo "Build failed"
        echo Failure >$result_file
    else
        echo "Build succeeded"
        echo Success >$result_file
    fi
}

# Some environment variables we want
export OCAMLRUNPARAM=b
export OTHERFLAGS="--print_z3_statistics --query_stats"
export MAKEFLAGS="$MAKEFLAGS -Otarget"

cd everquic-crypto
rootPath=$(pwd)
exec_build
cd ..
