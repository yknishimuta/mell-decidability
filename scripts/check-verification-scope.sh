#!/usr/bin/env bash
set -euo pipefail

repo_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repo_root"

require_vo=false
if [[ ${1:-} == "--require-vo" ]]; then
  require_vo=true
elif [[ $# -ne 0 ]]; then
  echo "usage: $0 [--require-vo]" >&2
  exit 2
fi

scratch=$(mktemp -d "${TMPDIR:-/tmp}/mell-scope.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

git ls-files '*.v' | LC_ALL=C sort > "$scratch/tracked"
awk '/^[^#].*\.v$/{print $NF}' _CoqProject | LC_ALL=C sort > "$scratch/registered"

if [[ $(wc -l < "$scratch/registered") -ne $(sort -u "$scratch/registered" | wc -l) ]]; then
  echo "verification scope: duplicate _CoqProject source entry" >&2
  comm -23 "$scratch/registered" <(sort -u "$scratch/registered") >&2 || true
  exit 1
fi

if ! cmp -s "$scratch/tracked" "$scratch/registered"; then
  echo "verification scope: tracked Coq sources and _CoqProject differ" >&2
  echo "tracked but not registered:" >&2
  comm -23 "$scratch/tracked" "$scratch/registered" >&2 || true
  echo "registered but not tracked:" >&2
  comm -13 "$scratch/tracked" "$scratch/registered" >&2 || true
  exit 1
fi

required=(
  theories/Audit/PaperFidelityBridges.v
  theories/Audit/PaperFidelityExamples.v
  theories/Audit/DecisionPathAudit.v
  theories/Audit/DecisionPathExamples.v
  theories/Audit/ExtractionDifferentialExamples.v
)
for source in "${required[@]}"; do
  if ! grep -Fqx "$source" "$scratch/registered"; then
    echo "verification scope: required audit source is missing: $source" >&2
    exit 1
  fi
done

if [[ $require_vo == true ]]; then
  missing=0
  while IFS= read -r source; do
    object=${source%.v}.vo
    vos=${source%.v}.vos
    if [[ ! -f $object ]]; then
      if [[ -f $vos ]]; then
        echo "verification scope: .vos is not complete evidence: $vos" >&2
      else
        echo "verification scope: missing compiled object: $object" >&2
      fi
      missing=1
    fi
  done < "$scratch/registered"
  if [[ $missing -ne 0 ]]; then
    exit 1
  fi
fi

echo "verification scope: $(wc -l < "$scratch/tracked" | tr -d ' ') tracked sources match _CoqProject"
if [[ $require_vo == true ]]; then
  echo "verification scope: every registered source has a normal .vo"
fi
