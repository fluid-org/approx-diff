#!/usr/bin/env bash
# Compile the example.render.probe program and run it: scale numbers on stdout, tick marks on
# stderr.

set -euo pipefail

cd "$(dirname "$0")/.."

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
t0=$SECONDS
( cd agda && agda --compile --compile-dir=_build --ghc-flag=-rtsopts \
    --ghc-flag=-j10 ${DUMP_FAST:+--ghc-flag=-O0} \
    src/example/render/probe.agda > "$log" 2>&1 )
t1=$SECONDS
GHCRTS="${DUMP_GHCRTS:--M2G}" agda/_build/probe
t2=$SECONDS
line="$(date '+%Y-%m-%d %H:%M') probe compile $((t1-t0))s run $((t2-t1))s"
echo "$line" >> agda/_build/timings.log
echo "$line" >&2
