#!/usr/bin/env bash
# Render every .dot file under dot/ to a sibling .svg via graphviz.

set -euo pipefail

cd "$(dirname "$0")/.."

if ! command -v dot >/dev/null 2>&1; then
  echo "graphviz 'dot' not found; install with 'brew install graphviz'" >&2
  exit 1
fi

find dot -type f -name '*.dot' | while read -r f; do
  dot -Tsvg "$f" > "${f%.dot}.svg"
  echo "wrote ${f%.dot}.svg"
done
