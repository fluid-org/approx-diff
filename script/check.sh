#!/usr/bin/env bash
# Regenerate every artefact and compare it with the committed baseline.

set -euo pipefail

cd "$(dirname "$0")/.."

script/gen-rooted-tables.sh >/dev/null
script/gen-free-tables.sh >/dev/null
script/gen-slices.sh >/dev/null
script/gen-dot.sh >/dev/null

if ! git diff --exit-code --stat -- test-baselines dot; then
  echo "Error: regenerated artefacts differ from the baselines." >&2
  exit 1
fi

if ! diff -u test-baselines/rooted-dependency.txt test-baselines/free-dependency.txt; then
  echo "Error: the free and rooted models disagree." >&2
  exit 1
fi

echo "Artefacts agree with the baselines, and the two models agree."
