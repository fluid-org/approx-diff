#!/usr/bin/env bash
# Compile the example.render.relations program and run it; the binary writes
# test-baselines/relations.txt via Agda IO.

set -euo pipefail

cd "$(dirname "$0")/.."

mkdir -p test-baselines

run=${AGDA_WATCH_DIR:-$HOME/.claude/run}
mkdir -p "$run"
log=$run/agda-watch.log
pidfile=$run/agda-watch.pid
echo $$ > "$pidfile"
trap 'rm -f "$pidfile"' EXIT

# The binary is linked with -rtsopts so GHCRTS applies at run time: a hard heap cap, so exhaustion
# fails fast instead of thrashing, and -s for a GC summary on stderr. Override via DUMP_GHCRTS.
# GHC compiles its make-mode graph in parallel; DUMP_FAST=1 additionally drops to -O0 for quicker
# iteration builds at some cost to the binary's speed.
compile() {
  ( cd agda && agda --compile --compile-dir=_build --ghc-flag=-rtsopts \
      --ghc-flag=-j10 ${DUMP_FAST:+--ghc-flag=-O0} \
      src/example/render/relations.agda > "$log" 2>&1 )
}
run() {
  GHCRTS="${DUMP_GHCRTS:--M1G -s}" agda/_build/relations
}

compile
# Agda regenerates Haskell only for modules whose interfaces changed, and the result can be
# inconsistent with the older object code; the binary then aborts with a GHC internal error.
# Rebuild all the generated Haskell once before giving up.
status=0
run || status=$?
if [ "$status" -eq 134 ]; then
  echo "relations aborted; rebuilding the generated Haskell" >&2
  rm -rf agda/_build/MAlonzo
  compile
  run
elif [ "$status" -ne 0 ]; then
  exit "$status"
fi

echo "wrote test-baselines/relations.txt"
