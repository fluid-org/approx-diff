#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v dot >/dev/null 2>&1; then
  echo "graphviz 'dot' not found; install with 'brew install graphviz'" >&2
  exit 1
fi

mkdir -p dot

( cd agda && agda --compile --compile-dir=_build src/example/graph-viz/dump-dep-graph.agda >/dev/null )
agda/_build/dump-dep-graph

for f in dot/*.dot; do
  echo "wrote $f"
  dot -Tsvg "$f" > "${f%.dot}.svg"
  echo "wrote ${f%.dot}.svg"
done
