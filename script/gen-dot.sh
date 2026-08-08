#!/usr/bin/env bash
# Compile the dump-dep-graph Agda program and run it; the binary writes dot/*.dot directly via
# Agda IO. Each is then rendered to a sibling SVG, which is skipped rather than fatal when
# graphviz is absent, so the artefact check does not require it.

set -euo pipefail

cd "$(dirname "$0")/.."

mkdir -p dot

( cd agda && agda --compile --compile-dir=_build src/graph-viz/dump-dep-graph.agda >/dev/null )
agda/_build/dump-dep-graph

if command -v dot >/dev/null 2>&1; then
  render=yes
else
  render=no
  echo "graphviz 'dot' not found; skipping SVGs (install with 'brew install graphviz')" >&2
fi

for f in dot/*.dot; do
  echo "wrote $f"
  if [ "$render" = yes ]; then
    dot -Tsvg "$f" > "${f%.dot}.svg"
    echo "wrote ${f%.dot}.svg"
  fi
done
