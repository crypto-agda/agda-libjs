#!/bin/bash -eu
GITHUB="$HOME"/.agda-pkg/github

STDLIB="$GITHUB"/agda/agda-stdlib/src
INCL=(-i. -ilib -i"$STDLIB")

# You might want to comment these out if you try examples
# outside of crypto-agda
# NPLIB="$GITHUB"/crypto-agda/agda-nplib/lib
# INCL=("${INCL[@]}" -i"$NPLIB")

# You might want to comment these out if you try examples
# outside of crypto-agda
# CRYPTO_AGDA="$GITHUB"/crypto-agda/crypto-agda
# INCL=("${INCL[@]}" -i"$CRYPTO_AGDA")

coffee -b -c run.coffee libagda.coffee proc.coffee
main="${1:-runningtest}"
shift
agda --js "${INCL[@]}" "$main".agda
node run.js jAgda."$main" "$@"
