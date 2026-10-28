#!/usr/bin/env bash
set -euo pipefail

audit_log=${1:?usage: check-assumption-allowlist.sh AUDIT_LOG}
allowed=Classical_Prop.classic

unexpected=$(awk '
  /^[[:alnum:]_.]+[[:space:]]*:/ && $1 != "Axioms:" { print $1 }
' "$audit_log" | LC_ALL=C sort -u | grep -Fvx "$allowed" || true)

if [[ -n $unexpected ]]; then
  echo "assumption allowlist: unexpected dependency" >&2
  echo "$unexpected" >&2
  exit 1
fi

echo "assumption allowlist: only $allowed (or closed terms)"
