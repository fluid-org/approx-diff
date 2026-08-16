#!/usr/bin/env bash
# Regenerate every artefact and compare it with the committed baseline.

set -euo pipefail

cd "$(dirname "$0")/.."

script/gen-relations.sh >/dev/null
script/gen-dot.sh >/dev/null

if ! git diff --exit-code --stat -- test-baselines dot; then
  echo "Error: regenerated artefacts differ from the baselines." >&2
  exit 1
fi

echo "Artefacts agree with the baselines."
