#!/usr/bin/env bash
# Regenerate every artefact and compare it with the committed baseline.

set -euo pipefail

cd "$(dirname "$0")/.."

script/gen-dot.sh >/dev/null
script/gen-latex.sh >/dev/null

if ! git diff --exit-code --stat -- test-baselines dot; then
  echo "Error: regenerated artefacts differ from the baselines." >&2
  exit 1
fi

untracked=$(git ls-files --others --exclude-standard -- test-baselines dot)
if [ -n "$untracked" ]; then
  printf 'Error: untracked artefacts:\n%s\n' "$untracked" >&2
  exit 1
fi

echo "Artefacts agree with the baselines."
