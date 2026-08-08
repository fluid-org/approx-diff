#!/usr/bin/env bash
# The tables of the model with free positions, against their own baseline and against the rooted
# ones: the two models must agree entry for entry.

set -euo pipefail

cd "$(dirname "$0")/.."
script/gen-free-tables.sh >/dev/null

if ! git diff --exit-code --stat -- test-baselines/free-dependency.txt; then
  echo "Error: regenerated free dependency tables differ from the baseline." >&2
  exit 1
fi

if ! diff -u test-baselines/rooted-dependency.txt \
            test-baselines/free-dependency.txt; then
  echo "Error: the free and rooted models disagree." >&2
  exit 1
fi
echo "Free dependency tables agree with the baseline and with the rooted model."
