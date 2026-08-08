#!/usr/bin/env bash
# Compile the dump-dep-graph Agda program and run it; the binary writes dot/*.dot directly
# via Agda IO. Use script/gen-svg.sh to render to SVGs.

set -euo pipefail

cd "$(dirname "$0")/.."

mkdir -p dot

( cd agda && agda --compile --compile-dir=_build src/graph-viz/dump-dep-graph.agda >/dev/null )
agda/_build/dump-dep-graph

for f in dot/*.dot; do
  echo "wrote $f"
done
