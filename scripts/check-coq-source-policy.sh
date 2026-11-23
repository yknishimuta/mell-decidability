#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

sources=()
while IFS= read -r source; do
  sources+=("$source")
done < <(git ls-files -- '*.v' ':(exclude)vendor/**')
if [[ ${#sources[@]} -eq 0 ]]; then
  echo "Coq source policy: no tracked project-managed .v sources" >&2
  exit 1
fi

exec python3 scripts/check_coq_audit.py source-policy "${sources[@]}"
