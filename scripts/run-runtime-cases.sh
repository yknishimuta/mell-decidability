#!/usr/bin/env bash
set -euo pipefail

runner=${1:?usage: run-runtime-cases.sh RUNNER MANIFEST TIMEOUT EXPECTED_COUNT REQUIRED_NAMES}
manifest=${2:?usage: run-runtime-cases.sh RUNNER MANIFEST TIMEOUT EXPECTED_COUNT REQUIRED_NAMES}
case_timeout=${3:?usage: run-runtime-cases.sh RUNNER MANIFEST TIMEOUT EXPECTED_COUNT REQUIRED_NAMES}
expected_count=${4:?usage: run-runtime-cases.sh RUNNER MANIFEST TIMEOUT EXPECTED_COUNT REQUIRED_NAMES}
required_names=${5:?usage: run-runtime-cases.sh RUNNER MANIFEST TIMEOUT EXPECTED_COUNT REQUIRED_NAMES}

scratch=$(mktemp -d "${TMPDIR:-/tmp}/mell-runtime-cases.XXXXXX")
trap 'rm -rf "$scratch"' EXIT
awk -F '\t' '!/^#/ && NF { print $1 }' "$manifest" | LC_ALL=C sort > "$scratch/actual-names"
grep -Ev '^[[:space:]]*(#|$)' "$required_names" | LC_ALL=C sort > "$scratch/required-names"
if [[ $(wc -l < "$scratch/actual-names") -ne $(sort -u "$scratch/actual-names" | wc -l) ]]; then
  echo "runtime gate: duplicate case name in manifest" >&2
  exit 1
fi
if ! cmp -s "$scratch/actual-names" "$scratch/required-names"; then
  echo "runtime gate: manifest case names differ from required set" >&2
  echo "missing cases:" >&2
  comm -13 "$scratch/actual-names" "$scratch/required-names" >&2 || true
  echo "unexpected cases:" >&2
  comm -23 "$scratch/actual-names" "$scratch/required-names" >&2 || true
  exit 1
fi

count=0
while IFS=$'\t' read -r case_name expected extra; do
  [[ -z $case_name || ${case_name:0:1} == "#" ]] && continue
  if [[ -n ${extra:-} ]]; then
    echo "runtime gate: malformed manifest row for $case_name" >&2
    exit 1
  fi

  set +e
  actual=$(LC_ALL=C perl -e '$seconds = shift; alarm $seconds; exec @ARGV' \
    "$case_timeout" "$runner" "$case_name")
  status=$?
  set -e

  if [[ $status -ne 0 ]]; then
    if [[ $status -eq 142 ]]; then
      echo "$case_name=TIMEOUT" >&2
    else
      echo "$case_name=RUNTIME_ERROR($status)" >&2
    fi
    exit "$status"
  fi
  echo "$case_name=$actual"
  if [[ $actual != "$expected" ]]; then
    echo "runtime gate: expected $case_name=$expected" >&2
    exit 1
  fi
  count=$((count + 1))
done < "$manifest"

if [[ $count -ne $expected_count ]]; then
  echo "runtime gate: expected $expected_count cases, executed $count" >&2
  exit 1
fi
echo "runtime gate: $count/$expected_count cases passed"
