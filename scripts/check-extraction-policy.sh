#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

if git grep -n -E '^[[:space:]]*Extract[[:space:]]+(Constant|Inductive)([[:space:]]|$)' -- '*.v'; then
  echo "extraction policy: unapproved custom extraction directive" >&2
  exit 1
fi

echo "extraction policy: no custom Extract Constant/Inductive directives"
