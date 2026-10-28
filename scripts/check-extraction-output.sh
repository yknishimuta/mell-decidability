#!/usr/bin/env bash
set -euo pipefail

output_dir=${1:?usage: check-extraction-output.sh OUTPUT_DIR [EXPECTED_OBJ_MAGIC]}
expected_obj_magic=${2:-10}

shopt -s nullglob
outputs=("$output_dir"/*.ml "$output_dir"/*.mli)
if [[ ${#outputs[@]} -eq 0 ]]; then
  echo "extraction output: no generated OCaml files" >&2
  exit 1
fi

if grep -R -F 'AXIOM TO BE REALIZED' "$output_dir" --include='*.ml' --include='*.mli'; then
  echo "extraction output: unrealized axiom found" >&2
  exit 1
fi

obj_magic_count=$(grep -R -o -F 'Obj.magic' "$output_dir" --include='*.ml' | wc -l | tr -d ' ')
if [[ $obj_magic_count -ne $expected_obj_magic ]]; then
  echo "extraction output: expected $expected_obj_magic audited Obj.magic occurrences, found $obj_magic_count" >&2
  exit 1
fi

echo "extraction output: no unrealized axiom; audited Obj.magic count=$obj_magic_count"
