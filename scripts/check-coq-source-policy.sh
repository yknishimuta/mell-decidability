#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

pattern='(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.'
if git grep -n -E "$pattern" -- '*.v'; then
  echo "Coq source policy: forbidden proof escape or axiom declaration" >&2
  exit 1
fi

echo "Coq source policy: no Axiom, Admitted, admit, or Abort in tracked .v sources"
