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

function fetch_qd() {
    if [ ! -d qd ]; then
        git clone https://github.com/project-everest/everparse qd
    fi

    cd qd
    git fetch origin
    local ref=$(jq -c -r '.RepoVersions["qd_version"]' "$rootPath/.docker/build/config.json" )
    if [[ $ref == "" || $ref == "null" ]]; then
        echo "Unable to find RepoVersions.qd_version on $rootPath/.docker/build/config.json"
        return -1
    fi

    echo Switching to EverParse $ref
    git reset --hard $ref
    cd ..
    export_home QD "$(pwd)/qd"
}

function fetch_and_make_qd() {
    fetch_qd

    # Default build target is all (quackyducky lowparse), unless specified otherwise
    local target
    if [[ $1 == "" ]]; then
        target="all"
    else
        target="$1"
    fi

    OTHERFLAGS='--admit_smt_queries true' make -C qd -j $threads $target
}

function exec_build() {

    result_file="../result.txt"
    local status_file="../status.txt"
    echo -n false >$status_file

    export CC=gcc-6
    fetch_and_make_qd &&
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
