#!/usr/bin/env bash
set -euo pipefail

source_root=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d "${TMPDIR:-/tmp}/mell-qa2-negative.XXXXXX")
case "$scratch" in
  "${TMPDIR:-/tmp}"/mell-qa2-negative.*) ;;
  *) echo "refusing unsafe temporary path: $scratch" >&2; exit 2 ;;
esac
trap 'rm -rf "$scratch"' EXIT

clone="$scratch/repo"
logs="$scratch/logs"
mkdir -p "$logs"
git clone --no-hardlinks --quiet "$source_root" "$clone"

# Before the QA-2 commit exists, test the proposed verification harness by
# overlaying verification-only files.  Mathematical sources always come from
# the cloned HEAD.  After commit these copies are byte-identical no-ops.
cp "$source_root/Makefile" "$clone/Makefile"
mkdir -p "$clone/scripts" "$clone/docs/review/extraction"
cp "$source_root/_CoqProject" "$clone/_CoqProject"
cp "$source_root"/scripts/*.sh "$clone/scripts/"
cp "$source_root/theories/Audit/ExtractionDifferentialExamples.v" \
  "$clone/theories/Audit/ExtractionDifferentialExamples.v"
git -C "$clone" add theories/Audit/ExtractionDifferentialExamples.v
cp "$source_root/docs/review/extraction/runtime-cases.tsv" \
  "$clone/docs/review/extraction/runtime-cases.tsv"
cp "$source_root/docs/review/extraction/decision-path-cases.tsv" \
  "$clone/docs/review/extraction/decision-path-cases.tsv"
cp "$source_root/docs/review/extraction/runtime-case-names.txt" \
  "$clone/docs/review/extraction/runtime-case-names.txt"
cp "$source_root/docs/review/extraction/decision-path-case-names.txt" \
  "$clone/docs/review/extraction/decision-path-case-names.txt"
ln -s "$source_root/_opam" "$clone/_opam"

cd "$clone"
tests=0
detections=0

run_phase() {
  local expected=$1
  local case_name=$2
  local phase=$3
  shift 3
  local log="$logs/${case_name}-${phase}.log"
  local status
  set +e
  "$@" >"$log" 2>&1
  status=$?
  set -e
  printf 'QA2|%s|%s|exit=%d\n' "$case_name" "$phase" "$status"
  tail -n 4 "$log" | sed 's/^/  | /'
  if [[ $expected == pass && $status -ne 0 ]]; then
    echo "QA2: expected PASS for $case_name/$phase" >&2
    exit 1
  fi
  if [[ $expected == fail && $status -eq 0 ]]; then
    echo "QA2: expected FAIL for $case_name/$phase" >&2
    exit 1
  fi
}

detect_case() {
  local case_name=$1
  local fault_command=$2
  local recovery_command=$3
  shift 3
  tests=$((tests + 1))
  run_phase pass "$case_name" baseline "$@"
  bash -euo pipefail -c "$fault_command"
  run_phase fail "$case_name" fault "$@"
  bash -euo pipefail -c "$recovery_command"
  run_phase pass "$case_name" recovery "$@"
  detections=$((detections + 1))
  echo "QA2|$case_name|DETECTED"
}

bash scripts/check-verification-scope.sh
opam exec --switch . -- make Makefile.coq

cp _CoqProject "$scratch/CoqProject.baseline"
detect_case manifest-omission \
  "grep -Fvx 'theories/Audit/PaperFidelityBridges.v' _CoqProject > '$scratch/CoqProject.changed'; cp '$scratch/CoqProject.changed' _CoqProject" \
  "cp '$scratch/CoqProject.baseline' _CoqProject" \
  bash scripts/check-verification-scope.sh

tests=$((tests + 1))
run_phase pass tracked-orphan baseline bash scripts/check-verification-scope.sh
printf 'From Coq Require Import Init.Prelude.\n' > theories/Audit/QA2Orphan.v
git add theories/Audit/QA2Orphan.v
run_phase fail tracked-orphan fault bash scripts/check-verification-scope.sh
git update-index --force-remove theories/Audit/QA2Orphan.v
rm -f theories/Audit/QA2Orphan.v
run_phase pass tracked-orphan recovery bash scripts/check-verification-scope.sh
detections=$((detections + 1))
echo 'QA2|tracked-orphan|DETECTED'

build_target=theories/Audit/DecisionPathAudit.vo
run_phase pass coq-type-error baseline make check-final
cp theories/Audit/DecisionPathAudit.v "$scratch/DecisionPathAudit.baseline"
printf '\nCheck (0 : bool).\n' >> theories/Audit/DecisionPathAudit.v
tests=$((tests + 1))
run_phase fail coq-type-error fault make check-final
cp "$scratch/DecisionPathAudit.baseline" theories/Audit/DecisionPathAudit.v
touch theories/Audit/DecisionPathAudit.v
run_phase pass coq-type-error recovery make check-final
detections=$((detections + 1))
echo 'QA2|coq-type-error|DETECTED'

run_phase pass full-build-baseline baseline \
  opam exec --switch . -- make -f Makefile.coq -j2

tests=$((tests + 1))
run_phase pass missing-vo baseline bash scripts/check-verification-scope.sh --require-vo
rm -f "$build_target"
run_phase fail missing-vo fault bash scripts/check-verification-scope.sh --require-vo
opam exec --switch . -- make -f Makefile.coq "$build_target" >/dev/null
run_phase pass missing-vo recovery bash scripts/check-verification-scope.sh --require-vo
detections=$((detections + 1))
echo 'QA2|missing-vo|DETECTED'

tests=$((tests + 1))
run_phase pass vos-only baseline bash scripts/check-verification-scope.sh --require-vo
mv "$build_target" "${build_target%.vo}.vos"
run_phase fail vos-only fault bash scripts/check-verification-scope.sh --require-vo
mv "${build_target%.vo}.vos" "$build_target"
run_phase pass vos-only recovery bash scripts/check-verification-scope.sh --require-vo
detections=$((detections + 1))
echo 'QA2|vos-only|DETECTED'

examples=theories/Audit/PaperFidelityExamples.v
cp "$examples" "$scratch/PaperFidelityExamples.baseline"

tests=$((tests + 1))
run_phase pass used-axiom baseline make audit-final
cat > QA2ExternalAxiom.v <<'EOF'
Axiom qa2_forbidden_used : False.
EOF
opam exec --switch . -- coqc QA2ExternalAxiom.v
cat >> theories/Audit/Statements.v <<'EOF'
Require Import QA2ExternalAxiom.
Theorem qa2_uses_forbidden_axiom : False.
Proof. exact qa2_forbidden_used. Qed.
Print Assumptions qa2_uses_forbidden_axiom.
EOF
run_phase fail used-axiom fault make audit-final
git show HEAD:theories/Audit/Statements.v > theories/Audit/Statements.v
rm -f QA2ExternalAxiom.v QA2ExternalAxiom.vo QA2ExternalAxiom.glob QA2ExternalAxiom.vok QA2ExternalAxiom.vos
touch theories/Audit/Statements.v
run_phase pass used-axiom recovery make audit-final
detections=$((detections + 1))
echo 'QA2|used-axiom|DETECTED'

tests=$((tests + 1))
run_phase pass unused-axiom baseline make audit-final
printf '\nAxiom qa2_forbidden_unused : True.\n' >> "$examples"
run_phase pass unused-axiom-kernel-accepts fault-kernel \
  opam exec --switch . -- make -f Makefile.coq theories/Audit/PaperFidelityExamples.vo
run_phase fail unused-axiom fault make audit-final
cp "$scratch/PaperFidelityExamples.baseline" "$examples"
touch "$examples"
run_phase pass unused-axiom recovery make audit-final
detections=$((detections + 1))
echo 'QA2|unused-axiom|DETECTED'

responses="$scratch/runtime-responses.tsv"
cp docs/review/extraction/runtime-cases.tsv "$responses"
fake_runner="$scratch/fake-runner.sh"
cat > "$fake_runner" <<EOF
#!/usr/bin/env bash
set -euo pipefail
case \${1:-} in
  qa2-crash) exit 7 ;;
  qa2-hang) sleep 5; echo false; exit 0 ;;
  qa2-none) echo None; exit 0 ;;
esac
awk -F '\t' -v key="\${1:-}" '\$1 == key { print \$2; found=1 } END { if (!found) exit 9 }' '$responses'
EOF
chmod +x "$fake_runner"
runtime_manifest=docs/review/extraction/runtime-cases.tsv
cp "$runtime_manifest" "$scratch/runtime-cases.baseline"
runtime_names=docs/review/extraction/runtime-case-names.txt
runtime_gate=(bash scripts/run-runtime-cases.sh "$fake_runner" "$runtime_manifest" 2 22 "$runtime_names")

detect_case runtime-yes-mismatch \
  "perl -0pi -e 's/mell-one\\ttrue/mell-one\\tfalse/' '$runtime_manifest'" \
  "cp '$scratch/runtime-cases.baseline' '$runtime_manifest'" \
  "${runtime_gate[@]}"

detect_case runtime-no-mismatch \
  "perl -0pi -e 's/mell-empty\\tfalse/mell-empty\\ttrue/' '$runtime_manifest'" \
  "cp '$scratch/runtime-cases.baseline' '$runtime_manifest'" \
  "${runtime_gate[@]}"

detect_case runtime-case-omission \
  "grep -Fv 'signed-action-negative' '$runtime_manifest' > '$scratch/runtime-cases.changed'; cp '$scratch/runtime-cases.changed' '$runtime_manifest'" \
  "cp '$scratch/runtime-cases.baseline' '$runtime_manifest'" \
  "${runtime_gate[@]}"

detect_case runtime-case-substitution \
  "grep -Fv 'signed-action-negative' '$runtime_manifest' > '$scratch/runtime-cases.changed'; printf 'mell-one\\ttrue\\n' >> '$scratch/runtime-cases.changed'; cp '$scratch/runtime-cases.changed' '$runtime_manifest'" \
  "cp '$scratch/runtime-cases.baseline' '$runtime_manifest'" \
  "${runtime_gate[@]}"

tiny_manifest="$scratch/tiny.tsv"
printf 'mell-one\ttrue\n' > "$tiny_manifest"
tiny_names="$scratch/tiny.names"
printf 'mell-one\n' > "$tiny_names"
tiny_gate=(bash scripts/run-runtime-cases.sh "$fake_runner" "$tiny_manifest" 1 1 "$tiny_names")

tests=$((tests + 1))
run_phase pass runtime-abnormal-exit baseline "${tiny_gate[@]}"
printf 'qa2-crash\tfalse\n' > "$tiny_manifest"
printf 'qa2-crash\n' > "$tiny_names"
run_phase fail runtime-abnormal-exit fault "${tiny_gate[@]}"
printf 'mell-one\ttrue\n' > "$tiny_manifest"
printf 'mell-one\n' > "$tiny_names"
run_phase pass runtime-abnormal-exit recovery "${tiny_gate[@]}"
detections=$((detections + 1))
echo 'QA2|runtime-abnormal-exit|DETECTED'

tests=$((tests + 1))
run_phase pass runtime-timeout baseline "${tiny_gate[@]}"
printf 'qa2-hang\tfalse\n' > "$tiny_manifest"
printf 'qa2-hang\n' > "$tiny_names"
run_phase fail runtime-timeout fault "${tiny_gate[@]}"
printf 'mell-one\ttrue\n' > "$tiny_manifest"
printf 'mell-one\n' > "$tiny_names"
run_phase pass runtime-timeout recovery "${tiny_gate[@]}"
detections=$((detections + 1))
echo 'QA2|runtime-timeout|DETECTED'

tests=$((tests + 1))
run_phase pass runtime-none-is-not-no baseline "${tiny_gate[@]}"
printf 'qa2-none\tfalse\n' > "$tiny_manifest"
printf 'qa2-none\n' > "$tiny_names"
run_phase fail runtime-none-is-not-no fault "${tiny_gate[@]}"
printf 'mell-one\ttrue\n' > "$tiny_manifest"
printf 'mell-one\n' > "$tiny_names"
run_phase pass runtime-none-is-not-no recovery "${tiny_gate[@]}"
detections=$((detections + 1))
echo 'QA2|runtime-none-is-not-no|DETECTED'

extract_source=theories/Decision/Extract.v
cp "$extract_source" "$scratch/Extract.baseline"
tests=$((tests + 1))
run_phase pass extraction-directive baseline bash scripts/check-extraction-policy.sh
printf '\nExtract Constant qa2_unapproved => "fun _ -> true".\n' >> "$extract_source"
run_phase fail extraction-directive fault bash scripts/check-extraction-policy.sh
cp "$scratch/Extract.baseline" "$extract_source"
run_phase pass extraction-directive recovery bash scripts/check-extraction-policy.sh
detections=$((detections + 1))
echo 'QA2|extraction-directive|DETECTED'

run_phase pass extraction-baseline baseline make extract-final
generated=docs/review/extraction/final/MELL.ml
cp "$generated" "$scratch/MELL.baseline.ml"

tests=$((tests + 1))
run_phase pass unrealized-axiom baseline bash scripts/check-extraction-output.sh docs/review/extraction/final 10
printf '\n(* AXIOM TO BE REALIZED: qa2 *)\n' >> "$generated"
run_phase fail unrealized-axiom fault bash scripts/check-extraction-output.sh docs/review/extraction/final 10
cp "$scratch/MELL.baseline.ml" "$generated"
run_phase pass unrealized-axiom recovery bash scripts/check-extraction-output.sh docs/review/extraction/final 10
detections=$((detections + 1))
echo 'QA2|unrealized-axiom|DETECTED'

tests=$((tests + 1))
run_phase pass new-obj-magic baseline bash scripts/check-extraction-output.sh docs/review/extraction/final 10
printf '\nlet qa2_unreviewed_cast = Obj.magic 0\n' >> "$generated"
run_phase fail new-obj-magic fault bash scripts/check-extraction-output.sh docs/review/extraction/final 10
cp "$scratch/MELL.baseline.ml" "$generated"
run_phase pass new-obj-magic recovery bash scripts/check-extraction-output.sh docs/review/extraction/final 10
detections=$((detections + 1))
echo 'QA2|new-obj-magic|DETECTED'

tests=$((tests + 1))
run_phase pass stale-extraction baseline make extract-final
printf '\n(* QA2_STALE_SENTINEL *)\n' >> "$generated"
{ printf 'Check (0 : bool).\n'; cat "$scratch/Extract.baseline"; } > "$extract_source"
run_phase fail stale-extraction fault make extract-final
if [[ -f $generated ]] && grep -Fq QA2_STALE_SENTINEL "$generated"; then
  echo 'QA2: stale extraction sentinel survived failed regeneration' >&2
  exit 1
fi
cp "$scratch/Extract.baseline" "$extract_source"
run_phase pass stale-extraction recovery make extract-final
detections=$((detections + 1))
echo 'QA2|stale-extraction|DETECTED'

echo "QA2 SUMMARY: $detections/$tests injected faults detected"
test "$tests" -eq 18
test "$detections" -eq "$tests"
