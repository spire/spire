#!/bin/bash

# Evaluate a spire source file and save the pretty printed output.
#
# This output is supposed to be valid input to the type checker, and
# should be invariant under further evaluations.
#
# (This should be a command line switch to ./spire, but this is easier
# for now ...)

if [[ $# -ne 1 ]]; then
  echo "usage: $0 SPIRE_SOURCE_FILE" > /dev/stderr
  exit 2
fi

infile=$1
outfile=/tmp/$(basename $infile).evaluated

./spire $infile \
  | sed -nre '/Pretty printed:/,$p' \
  | tail -n +3 \
  > $outfile

echo $outfile:
echo
cat $outfile
