#!/bin/bash
set -e

if [ $# -lt 1 ]
then
    echo "Usage : $0 config-name [release]"
    echo "    release    Use release mode binary"
    exit
fi

FORMULA_SAMPLE_RATIO=1
STATE_SAMPLE_RATIO=1
STATE_GROUP_SIZE=5
case "$1" in
    flat)
        STATES=500
        NESTING=0
        VARS=3
        ;;
    flattest)
        STATES=20
        NESTING=0
        VARS=2
        ;;
    nested)
        STATES=500
        NESTING=1
        VARS=2
        STATE_SAMPLE_RATIO=0.2
        FORMULA_SAMPLE_RATIO=0.04
        ;;
    *)
        echo "Unknown configuration '$1'"
        exit 1
        ;;
esac

CONFIGURATION="Debug"
case "$2" in
    release)
        echo "Using Release binary."
        CONFIGURATION="Release"
        ;;
    *)
        CONFIGURATION="Debug"
        ;;
esac

DOTNET_PREFIX=""
if `command -v xbuild &>/dev/null`; then
    DOTNET_PREFIX="mono "
    xbuild "/p:Configuration=${CONFIGURATION}"
else
    MSBuild "/p:Configuration=${CONFIGURATION}"
fi

CMD="--debug ../bin/${CONFIGURATION}/Platypus.exe"
ARGS="--variable-number ${VARS} --ds-nest-level ${NESTING} --states-per-formula ${STATES} --group-size ${STATE_GROUP_SIZE}"

time ${DOTNET_PREFIX} ${CMD} ${ARGS} --create-formulas
time ${DOTNET_PREFIX} ${CMD} ${ARGS} --sample-ratio ${FORMULA_SAMPLE_RATIO} --create-states
time ${DOTNET_PREFIX} ${CMD} ${ARGS} --sample-ratio ${STATE_SAMPLE_RATIO} --create-dataset
time ${DOTNET_PREFIX} ${CMD} ${ARGS} --combine-dataset
time ${DOTNET_PREFIX} ${CMD} ${ARGS} --train-model
