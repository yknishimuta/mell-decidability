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
mkdir -p "$clone/scripts" "$clone/tests" "$clone/docs/review/extraction"
cp "$source_root/_CoqProject" "$clone/_CoqProject"
cp "$source_root"/scripts/*.sh "$clone/scripts/"
cp "$source_root/scripts/check_coq_audit.py" "$clone/scripts/"
cp "$source_root/scripts/audit-assumptions-manifest.txt" "$clone/scripts/"
cp "$source_root/tests/test_check_coq_audit.py" "$clone/tests/"
cp "$source_root/theories/Audit/Statements.v" "$clone/theories/Audit/Statements.v"
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
export PATH="$clone/_opam/bin:$PATH"
make() {
  command make OPAMEXEC= "$@"
}
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

run_phase_diagnostic() {
  local expected=$1
  local case_name=$2
  local phase=$3
  local diagnostic=$4
  shift 4
  run_phase "$expected" "$case_name" "$phase" "$@"
  if [[ $expected == fail ]] && ! grep -Fq "$diagnostic" "$logs/${case_name}-${phase}.log"; then
    echo "QA2: $case_name/$phase failed without expected diagnostic: $diagnostic" >&2
    exit 1
  fi
}

run_phase pass audit-parser-unit baseline python3 -m unittest tests.test_check_coq_audit

assumption_manifest="$scratch/assumption.manifest"
assumption_log="$scratch/assumption.log"
printf 'target\n' > "$assumption_manifest"
classic_block='MELL_AUDIT_BEGIN target
Axioms:
Classical_Prop.classic : forall P : Prop, P \/ ~ P
MELL_AUDIT_END target
'
closed_block='MELL_AUDIT_BEGIN target
Closed under the global context
MELL_AUDIT_END target
'
assumption_gate=(python3 scripts/check_coq_audit.py assumptions "$assumption_log" "$assumption_manifest")

printf '%s' "$classic_block" > "$assumption_log"
run_phase pass assumption-classic baseline "${assumption_gate[@]}"
printf '%s' "$closed_block" > "$assumption_log"
run_phase pass assumption-closed baseline "${assumption_gate[@]}"

assumption_fault() {
  local case_name=$1
  local diagnostic=$2
  local content=$3
  tests=$((tests + 1))
  printf '%s' "$classic_block" > "$assumption_log"
  run_phase pass "$case_name" baseline "${assumption_gate[@]}"
  printf '%s' "$content" > "$assumption_log"
  run_phase_diagnostic fail "$case_name" fault "$diagnostic" "${assumption_gate[@]}"
  printf '%s' "$classic_block" > "$assumption_log"
  run_phase pass "$case_name" recovery "${assumption_gate[@]}"
  detections=$((detections + 1))
  echo "QA2|$case_name|DETECTED"
}

assumption_fault assumption-apostrophe "AuditGateProbe.forbidden'" 'MELL_AUDIT_BEGIN target
Axioms:
AuditGateProbe.forbidden'\'' : False
MELL_AUDIT_END target
'
assumption_fault assumption-parameter Other.forbidden 'MELL_AUDIT_BEGIN target
Axioms:
Other.forbidden : False
MELL_AUDIT_END target
'
assumption_fault assumption-guard 'assumed to be guarded' 'MELL_AUDIT_BEGIN target
Axioms:
nonterminating is assumed to be guarded.
MELL_AUDIT_END target
'
assumption_fault assumption-empty 'audit log is empty' ''
assumption_fault assumption-truncated 'unterminated assumption block' 'MELL_AUDIT_BEGIN target
Axioms:
Classical_Prop.classic : Prop
'
assumption_fault assumption-missing-theorem 'expected target' 'MELL_AUDIT_BEGIN other
Closed under the global context
MELL_AUDIT_END other
'
assumption_fault assumption-unknown 'unrecognized dependency output' 'MELL_AUDIT_BEGIN target
Axioms:
<unknown>
MELL_AUDIT_END target
'

tests=$((tests + 1))
printf '%s' "$classic_block" > "$assumption_log"
run_phase pass assumption-missing-log baseline "${assumption_gate[@]}"
rm -f "$assumption_log"
run_phase_diagnostic fail assumption-missing-log fault 'does not exist' "${assumption_gate[@]}"
printf '%s' "$classic_block" > "$assumption_log"
run_phase pass assumption-missing-log recovery "${assumption_gate[@]}"
detections=$((detections + 1))
echo 'QA2|assumption-missing-log|DETECTED'

coqchk_log="$scratch/coqchk.log"
valid_coqchk='CONTEXT SUMMARY
===============
* Constants/Inductives relying on type-in-type: <none>
* Constants/Inductives relying on unsafe (co)fixpoints: <none>
* Inductives whose positivity is assumed: <none>
'
coqchk_gate=(python3 scripts/check_coq_audit.py coqchk "$coqchk_log")
printf '%s' "$valid_coqchk" > "$coqchk_log"
run_phase pass coqchk-unsafe baseline "${coqchk_gate[@]}"
tests=$((tests + 1))
printf '%s' "$valid_coqchk" | sed 's/unsafe (co)fixpoints: <none>/unsafe (co)fixpoints:\n    Probe.nonterminating/' > "$coqchk_log"
run_phase_diagnostic fail coqchk-unsafe fault 'unsafe (co)fixpoints' "${coqchk_gate[@]}"
printf '%s' "$valid_coqchk" > "$coqchk_log"
run_phase pass coqchk-unsafe recovery "${coqchk_gate[@]}"
detections=$((detections + 1))
echo 'QA2|coqchk-unsafe|DETECTED'

tests=$((tests + 1))
run_phase pass coqchk-missing-section baseline "${coqchk_gate[@]}"
grep -Fv 'positivity is assumed' "$coqchk_log" > "$scratch/coqchk.missing"
cp "$scratch/coqchk.missing" "$coqchk_log"
run_phase_diagnostic fail coqchk-missing-section fault 'missing positivity assumed section' "${coqchk_gate[@]}"
printf '%s' "$valid_coqchk" > "$coqchk_log"
run_phase pass coqchk-missing-section recovery "${coqchk_gate[@]}"
detections=$((detections + 1))
echo 'QA2|coqchk-missing-section|DETECTED'

source_fixture="$scratch/SourceFixture.v"
source_gate=(python3 scripts/check_coq_audit.py source-policy "$source_fixture")
safe_source='Module Type Signature. Parameter carrier : Type. End Signature.
Definition documentary_string := "Unset Guard Checking.".
(* Set Type in Type. *)
'
source_fault() {
  local case_name=$1
  local diagnostic=$2
  local content=$3
  tests=$((tests + 1))
  printf '%s' "$safe_source" > "$source_fixture"
  run_phase pass "$case_name" baseline "${source_gate[@]}"
  printf '%s' "$content" > "$source_fixture"
  run_phase_diagnostic fail "$case_name" fault "$diagnostic" "${source_gate[@]}"
  printf '%s' "$safe_source" > "$source_fixture"
  run_phase pass "$case_name" recovery "${source_gate[@]}"
  detections=$((detections + 1))
  echo "QA2|$case_name|DETECTED"
}
source_fault source-parameter 'global Parameter' 'Parameter forbidden : False.\n'
source_fault source-axiom 'global Axiom' 'Axiom forbidden : False.\n'
source_fault source-guard 'Unset Guard Checking.' 'Unset Guard Checking.\n'
source_fault source-positivity 'Unset Positivity Checking.' 'Unset Positivity Checking.\n'
source_fault source-universe 'Unset Universe Checking.' 'Unset Universe Checking.\n'
source_fault source-type-in-type 'Set Type in Type.' 'Set Type in Type.\n'

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
make Makefile.coq

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
  make -f Makefile.coq -j2

tests=$((tests + 1))
run_phase pass missing-vo baseline bash scripts/check-verification-scope.sh --require-vo
rm -f "$build_target"
run_phase fail missing-vo fault bash scripts/check-verification-scope.sh --require-vo
make -f Makefile.coq "$build_target" >/dev/null
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
cp theories/Audit/Statements.v "$scratch/Statements.baseline"
cp scripts/audit-assumptions-manifest.txt "$scratch/assumptions-manifest.baseline"
cp _CoqProject "$scratch/CoqProject.audit-baseline"

restore_audit_probe() {
  local probe=${1:?probe path required}
  git update-index --force-remove "$probe" 2>/dev/null || true
  rm -f "$probe" "${probe%.v}.vo" "${probe%.v}.glob" "${probe%.v}.vok" "${probe%.v}.vos"
  cp "$scratch/Statements.baseline" theories/Audit/Statements.v
  cp "$scratch/assumptions-manifest.baseline" scripts/audit-assumptions-manifest.txt
  cp "$scratch/CoqProject.audit-baseline" _CoqProject
  touch theories/Audit/Statements.v _CoqProject
}

tests=$((tests + 1))
run_phase pass integrated-apostrophe baseline make audit-final
apostrophe_probe=theories/Audit/AuditGateApostropheProbe.v
cat > "$apostrophe_probe" <<'EOF'
From Coq Require Import Init.Prelude.
Parameter forbidden' : False.
Theorem forged_claim : False.
Proof. exact forbidden'. Qed.
EOF
git add "$apostrophe_probe"
printf '%s\n' "$apostrophe_probe" >> _CoqProject
cat >> theories/Audit/Statements.v <<'EOF'
From Mell.Audit Require Import AuditGateApostropheProbe.
Goal True. idtac "MELL_AUDIT_BEGIN forged_claim". exact I. Qed.
Print Assumptions forged_claim.
Goal True. idtac "MELL_AUDIT_END forged_claim". exact I. Qed.
EOF
printf 'forged_claim\n' >> scripts/audit-assumptions-manifest.txt
run_phase_diagnostic fail integrated-apostrophe fault "Coq audit: forged_claim: unauthorized assumption: forbidden'" make audit-final
restore_audit_probe "$apostrophe_probe"
run_phase pass integrated-apostrophe recovery make audit-final
detections=$((detections + 1))
echo 'QA2|integrated-apostrophe|DETECTED'

tests=$((tests + 1))
run_phase pass integrated-guard baseline make audit-final
guard_probe=theories/Audit/AuditGateGuardProbe.v
cat > "$guard_probe" <<'EOF'
From Coq Require Import Init.Prelude.
Unset Guard Checking.
Fixpoint nonterminating (x : unit) : False := nonterminating x.
Set Guard Checking.
Definition inherited_false : False := nonterminating tt.
EOF
git add "$guard_probe"
printf '%s\n' "$guard_probe" >> _CoqProject
cat >> theories/Audit/Statements.v <<'EOF'
From Mell.Audit Require Import AuditGateGuardProbe.
Goal True. idtac "MELL_AUDIT_BEGIN inherited_false". exact I. Qed.
Print Assumptions inherited_false.
Goal True. idtac "MELL_AUDIT_END inherited_false". exact I. Qed.
EOF
printf 'inherited_false\n' >> scripts/audit-assumptions-manifest.txt
run_phase_diagnostic fail integrated-guard fault 'Coq audit: inherited_false: unrecognized dependency output: nonterminating is assumed to be guarded.' make audit-final
restore_audit_probe "$guard_probe"
run_phase pass integrated-guard recovery make audit-final
detections=$((detections + 1))
echo 'QA2|integrated-guard|DETECTED'

tests=$((tests + 1))
run_phase pass used-axiom baseline make audit-final
cat > QA2ExternalAxiom.v <<'EOF'
Axiom qa2_forbidden_used : False.
EOF
coqc QA2ExternalAxiom.v
cat >> theories/Audit/Statements.v <<'EOF'
Require Import QA2ExternalAxiom.
Theorem qa2_uses_forbidden_axiom : False.
Proof. exact qa2_forbidden_used. Qed.
Goal True. idtac "MELL_AUDIT_BEGIN qa2_uses_forbidden_axiom". exact I. Qed.
Print Assumptions qa2_uses_forbidden_axiom.
Goal True. idtac "MELL_AUDIT_END qa2_uses_forbidden_axiom". exact I. Qed.
EOF
printf 'qa2_uses_forbidden_axiom\n' >> scripts/audit-assumptions-manifest.txt
run_phase_diagnostic fail used-axiom fault 'Coq audit: qa2_uses_forbidden_axiom: unauthorized assumption: qa2_forbidden_used' make audit-final
cp "$scratch/Statements.baseline" theories/Audit/Statements.v
cp "$scratch/assumptions-manifest.baseline" scripts/audit-assumptions-manifest.txt
rm -f QA2ExternalAxiom.v QA2ExternalAxiom.vo QA2ExternalAxiom.glob QA2ExternalAxiom.vok QA2ExternalAxiom.vos
touch theories/Audit/Statements.v
run_phase pass used-axiom recovery make audit-final
detections=$((detections + 1))
echo 'QA2|used-axiom|DETECTED'

tests=$((tests + 1))
run_phase pass unused-axiom baseline make audit-final
printf '\nAxiom qa2_forbidden_unused : True.\n' >> "$examples"
run_phase pass unused-axiom-kernel-accepts fault-kernel \
  make -f Makefile.coq theories/Audit/PaperFidelityExamples.vo
run_phase_diagnostic fail unused-axiom fault 'global Axiom' make audit-final
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
test "$tests" -eq 36
test "$detections" -eq "$tests"
