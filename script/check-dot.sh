#!/usr/bin/env bash

set -euo pipefail

cd "$(dirname "$0")/.."
script/gen-dot.sh >/dev/null

if ! git diff --exit-code --stat -- dot/*.dot; then
  echo "Error: regenerated dot files differ from baselines." >&2
  exit 1
fi
echo "Dot files agree with baselines."
