#!/bin/bash
set -eu
GITHUB="$HOME"/.agda-pkg/github

STDLIB="$GITHUB"/agda/agda-stdlib
INCL=(-i. -ilib -i"$STDLIB"/src)

# You might want to comment these out if you try examples
# outside of crypto-agda
# NPLIB="$GITHUB"/crypto-agda/agda-nplib
# INCL=("${INCL[@]}" -i"$NPLIB"/lib)

# You might want to comment these out if you try examples
# outside of crypto-agda
# CRYPTO_AGDA="$GITHUB"/crypto-agda/crypto-agda
# INCL=("${INCL[@]}" -i"$CRYPTO_AGDA")

coffee -b -c run.coffee libagda.coffee proc.coffee
main="${1:-example1}"
if [ ! -e "$main".agda ]; then
  echo "$main.agda does not exists." >>/dev/stderr
  exit 1
fi
shift || :
agda --js "${INCL[@]}" "$main".agda
node run.js jAgda."$main" "$@"
