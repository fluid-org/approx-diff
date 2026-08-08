#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."
script/gen-rooted-tables.sh >/dev/null

if ! git diff --exit-code --stat -- test-baselines/rooted-dependency.txt; then
  echo "Error: regenerated dependency tables differ from the baseline." >&2
  exit 1
fi
echo "Dependency tables agree with the baseline."
