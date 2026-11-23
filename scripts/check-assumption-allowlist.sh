#!/usr/bin/env bash
set -euo pipefail

audit_log=${1:?usage: check-assumption-allowlist.sh AUDIT_LOG}
repo_root=$(cd "$(dirname "$0")/.." && pwd)

exec python3 "$repo_root/scripts/check_coq_audit.py" assumptions \
  "$audit_log" "$repo_root/scripts/audit-assumptions-manifest.txt"
