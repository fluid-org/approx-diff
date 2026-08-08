#!/usr/bin/env bash
# Compile the dump-tables Agda program and run it; the binary writes
# test-baselines/dependency.txt via Agda IO.

set -euo pipefail

cd "$(dirname "$0")/.."

mkdir -p test-baselines

log=${TMPDIR:-/tmp}/agda-watch.log
pidfile=${TMPDIR:-/tmp}/agda-watch.pid
echo $$ > "$pidfile"
trap 'rm -f "$pidfile"' EXIT

# The binary is linked with -rtsopts so GHCRTS applies at run time: a hard heap cap, so exhaustion
# fails fast instead of thrashing, and -s for a GC summary on stderr. Override via DUMP_GHCRTS.
# GHC compiles its make-mode graph in parallel; DUMP_FAST=1 additionally drops to -O0 for quicker
# iteration builds at some cost to the binary's speed.
( cd agda && agda --compile --compile-dir=_build --ghc-flag=-rtsopts \
    --ghc-flag=-j10 ${DUMP_FAST:+--ghc-flag=-O0} \
    src/graph-viz/dump-tables.agda > "$log" 2>&1 )
GHCRTS="${DUMP_GHCRTS:--M1G -s}" agda/_build/dump-tables

echo "wrote test-baselines/dependency.txt"
