SHELL := /bin/bash
.SHELLFLAGS := -eu -o pipefail -c

OPAMEXEC := opam exec --switch . --
COQMAKEFILE := Makefile.coq
CORE_LOG_DIR := docs/review/logs
RUNTIME_CASE_TIMEOUT ?= 60

.PHONY: all check-core audit-core check-logic audit-logic check-bvas-core audit-bvas-core check-search audit-search extract-search check-codecs audit-codecs check-repairs-local audit-repairs check-presburger audit-presburger extract-presburger check-bvas-conditional audit-conditional check-bridges audit-bridges check-t10-g audit-t10-g check-t10-a0-l audit-t10-a0-l check-t10-a0-qf audit-t10-a0-qf check-t10-a0-qe-adapter audit-t10-a0-qe-adapter check-t10-a audit-t10-a check-t10-b audit-t10-b check-t10-c1-hl audit-t10-c1-hl check-t10-c1-qe1 audit-t10-c1-qe1 check-t10-c1-qe2 audit-t10-c1-qe2 check-t10-c1-assembly audit-t10-c1-assembly check-t10-c2-g0 audit-t10-c2-g0 check-t10-c2-g1-i audit-t10-c2-g1-i check-t10-c2-g1-hilbert audit-t10-c2-g1-hilbert check-t10-c2-g1-pullback audit-t10-c2-g1-pullback check-t10-c2-g1-main audit-t10-c2-g1-main check-t10-c2-l0 audit-t10-c2-l0 check-t10-c2-l0-r audit-t10-c2-l0-r check-t10-c2-l1 audit-t10-c2-l1 check-t10-c2-l2 audit-t10-c2-l2 check-t10-c3-0 audit-t10-c3-0 check-t10-c3-1a audit-t10-c3-1a check-t10-c3-1b audit-t10-c3-1b check-t10-c3-2a audit-t10-c3-2a check-t10-c3-2b audit-t10-c3-2b check-t10-c3-3 audit-t10-c3-3 check-t10-c4-0 audit-t10-c4-0 check-t10-c4-1 audit-t10-c4-1 check-t10-c4-2a audit-t10-c4-2a check-t10-c4-2b audit-t10-c4-2b check-t10-c4-3a audit-t10-c4-3a check-t10-c4-3b-0 audit-t10-c4-3b-0 check-t10-c4-3b-1-hrep-a0 audit-t10-c4-3b-1-hrep-a0 check-t10-c4-3b-1-hrep-a1 audit-t10-c4-3b-1-hrep-a1 check-t10-c4-3b-1-hrep-a2 audit-t10-c4-3b-1-hrep-a2 check-t10-c4-3b-1-hrep-b audit-t10-c4-3b-1-hrep-b check-t10-c4-3b-1-hrep-c audit-t10-c4-3b-1-hrep-c check-t10-c4-3b-1-hrep-d audit-t10-c4-3b-1-hrep-d check-t10-c4-3b-1-b1 audit-t10-c4-3b-1-b1 check-t10-c4-3b-1-b2 audit-t10-c4-3b-1-b2 check-t10-c4-3b-1-b3 audit-t10-c4-3b-1-b3 check-t10-c4-3b-1-b4 audit-t10-c4-3b-1-b4 check-t10-d-task1 audit-t10-d-task1 check-t10-d-task2a audit-t10-d-task2a check-t10-d-task2b audit-t10-d-task2b check-t10-d-task3a audit-t10-d-task3a check-t10-d-task3b audit-t10-d-task3b check-t10-d-task4a audit-t10-d-task4a check-t10-d-task4b audit-t10-d-task4b check-t10-d-task5a audit-t10-d-task5a check-t10-d-task5b audit-t10-d-task5b check-t10-d-task5c audit-t10-d-task5c check-t10-d-task6a audit-t10-d-task6a check-t10-d-task6b audit-t10-d-task6b check-t10-d-task6c audit-t10-d-task6c check-t10-e3 audit-t10-e3 clean

all: check-core

$(COQMAKEFILE): _CoqProject
	$(OPAMEXEC) coq_makefile -f _CoqProject -o $(COQMAKEFILE)

check-core: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Audit/Imports.vo theories/Audit/Assumptions.vo 2>&1 | tee $(CORE_LOG_DIR)/check-core.log
	test -f theories/Audit/Imports.vo
	test -f theories/Audit/Assumptions.vo

audit-core: check-core audit-bvas-core
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/Assumptions.v 2>&1 | tee $(CORE_LOG_DIR)/audit-core.log

check-logic: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Logic/Syntax.vo theories/Logic/Calculus.vo theories/Logic/YallaBridge.vo theories/Audit/LogicExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-logic.log
	test -f theories/Logic/Syntax.vo
	test -f theories/Logic/Calculus.vo
	test -f theories/Logic/YallaBridge.vo
	test -f theories/Audit/LogicExamples.vo

audit-logic: check-logic
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/LogicExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-logic.log

check-bvas-core: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Core/Vector.vo theories/Core/FiniteTree.vo theories/BVAS/System.vo theories/BVAS/Runs.vo theories/BVAS/Certificates.vo theories/Audit/RunExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-bvas-core.log
	test -f theories/Core/Vector.vo
	test -f theories/Core/FiniteTree.vo
	test -f theories/BVAS/System.vo
	test -f theories/BVAS/Runs.vo
	test -f theories/BVAS/Certificates.vo
	test -f theories/Audit/RunExamples.vo

audit-bvas-core: check-bvas-core
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/RunExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-bvas-core.log

check-search: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR) docs/review/extraction
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) theories/Core/Search.vo theories/Audit/SearchExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-search.log
	test -f theories/Core/Search.vo
	test -f theories/Audit/SearchExamples.vo

audit-search: check-search
	mkdir -p $(CORE_LOG_DIR) docs/review/extraction
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/SearchExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-search.log

extract-search: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR) docs/review/extraction
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/SearchExamples.v 2>&1 | tee $(CORE_LOG_DIR)/extract-search-driver.log
	test -s docs/review/extraction/search.ml
	! grep -E 'AXIOM TO BE REALIZED|Obj\\.magic' docs/review/extraction/search.ml
	grep -E 'let constructive_indefinite_ground_description_nat|let rec linear_search_conform|let parity_search|let rec search_fuel' docs/review/extraction/search.ml | tee $(CORE_LOG_DIR)/extract-search.log

check-codecs: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Core/Code.vo theories/Logic/Code.vo theories/BVAS/Code.vo theories/Semilinear/Presentation.vo theories/Semilinear/Code.vo theories/Audit/CodeExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-codecs.log
	test -f theories/Audit/CodeExamples.vo

audit-codecs: check-codecs
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/CodeExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-codecs.log

check-repairs-local: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/MathCompBridge.vo theories/Geometry/Periodic.vo theories/Geometry/Cone.vo theories/BVAS/Contexts.vo theories/BVAS/RunOrder.vo theories/BVAS/Amalgamation.vo theories/Audit/RepairExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-repairs-local.log
	test -f theories/Audit/RepairExamples.vo

audit-repairs: check-repairs-local
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -l theories/Audit/RepairExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-repairs.log

check-presburger: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR) docs/review/extraction/presburger
	$(OPAMEXEC) $(MAKE) -B -f $(COQMAKEFILE) -j2 theories/Presburger/Syntax.vo theories/Presburger/Semantics.vo theories/Presburger/QE.vo theories/Presburger/Decide.vo theories/Audit/PresburgerExamples.vo > $(CORE_LOG_DIR)/check-presburger.log 2>&1
	sed -n '1,$$p' $(CORE_LOG_DIR)/check-presburger.log
	test -f theories/Audit/PresburgerExamples.vo

audit-presburger: check-presburger
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/PresburgerExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-presburger.log
	diff -u docs/review/expected/presburger-assumptions.txt $(CORE_LOG_DIR)/audit-presburger.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' vendor/minicooper theories/Presburger theories/Audit/PresburgerExamples.v --include='*.v'

extract-presburger: check-presburger
	test -s docs/review/extraction/presburger/Decide.ml
	! grep -R -E 'AXIOM TO BE REALIZED|Obj\.magic|failwith|raise|assert false|(^|[[:space:]])external[[:space:]]' docs/review/extraction/presburger --include='*.ml'
	grep -R -E 'let presburger_decide|let rec qe|let cooper' docs/review/extraction/presburger --include='*.ml' | tee $(CORE_LOG_DIR)/extract-presburger.log
	task_tmp=$$(mktemp -d /tmp/mell-presburger-ocaml.XXXXXX); trap 'rm -rf "$$task_tmp"' EXIT; cp docs/review/extraction/presburger/*.ml docs/review/extraction/presburger/*.mli "$$task_tmp"; cd "$$task_tmp"; opam exec --switch "$(CURDIR)" -- ocamldep -sort *.mli *.ml | xargs opam exec --switch "$(CURDIR)" -- ocamlc -c

check-bvas-conditional: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Semilinear/Formula.vo theories/Decision/Invariant.vo theories/Decision/Stage.vo theories/Decision/BVASOfSeparator.vo theories/Audit/InvariantExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-bvas-conditional.log
	test -f theories/Audit/InvariantExamples.vo

audit-conditional: check-bvas-conditional
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/InvariantExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-conditional.log
	$(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Semilinear.Formula Mell.Decision.Invariant Mell.Decision.Stage Mell.Decision.BVASOfSeparator Mell.Audit.InvariantExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-bvas-conditional.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Semilinear/Formula.v theories/Decision theories/Audit/InvariantExamples.v --include='*.v'

check-bridges: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/Stateful.vo theories/BVASS/ContextInsertion.vo theories/BVASS/OrderedBridge.vo theories/Reduction/StateErasure.vo theories/Order/AlmostFullBridge.vo theories/Order/FiniteBasis.vo theories/Audit/BridgeExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-bridges.log
	test -f theories/Audit/BridgeExamples.vo

audit-bridges: check-bridges
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/BridgeExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-bridges.log
	$(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.Stateful Mell.BVASS.ContextInsertion Mell.BVASS.OrderedBridge Mell.Reduction.StateErasure Mell.Order.AlmostFullBridge Mell.Order.FiniteBasis Mell.Audit.BridgeExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-bridges.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/Stateful.v theories/BVASS/ContextInsertion.v theories/BVASS/OrderedBridge.v theories/Reduction/StateErasure.v theories/Order/AlmostFullBridge.v theories/Order/FiniteBasis.v theories/Audit/BridgeExamples.v

check-t10-g: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Audit/FiniteCoverAssumptions.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-g.log
	test -f theories/Audit/FiniteCoverAssumptions.vo

audit-t10-g: check-t10-g
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FiniteCoverAssumptions.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-g.log
	! sed -n '/T10_G_CONCRETE_ASSUMPTIONS/,$$p' $(CORE_LOG_DIR)/audit-t10-g.log | grep -F 'ClassicalEpsilon.constructive_indefinite_description'
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVAS.Code Mell.BVASS.Code Mell.Order.CountableFiniteBasis Mell.Order.FiniteBasis Mell.Audit.FiniteCoverAssumptions 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-g.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVAS/Code.v theories/BVASS/Code.v theories/Order/CountableFiniteBasis.v theories/Order/FiniteBasis.v theories/Audit/FiniteCoverAssumptions.v

check-t10-a0-l: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Audit/LinearEquationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-a0-l.log
	test -f theories/Audit/LinearEquationExamples.vo

audit-t10-a0-l: check-t10-a0-l
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LinearEquationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-a0-l.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-a0-l.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-a0-l.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Semilinear.LinearEquations Mell.Audit.LinearEquationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-a0-l.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Semilinear/LinearEquations.v theories/Audit/LinearEquationExamples.v

check-t10-a0-qf: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Audit/QFSemilinearExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-a0-qf.log
	test -f theories/Audit/QFSemilinearExamples.vo

audit-t10-a0-qf: check-t10-a0-qf
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QFSemilinearExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-a0-qf.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-a0-qf.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-a0-qf.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Semilinear.QuantifierFree Mell.Audit.QFSemilinearExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-a0-qf.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Semilinear/QuantifierFree.v theories/Audit/QFSemilinearExamples.v

check-t10-a0-qe-adapter: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Audit/PresburgerNatSemilinearExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-a0-qe-adapter.log
	test -f theories/Audit/PresburgerNatSemilinearExamples.vo

audit-t10-a0-qe-adapter: check-t10-a0-qe-adapter
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/PresburgerNatSemilinearExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-a0-qe-adapter.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-a0-qe-adapter.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-a0-qe-adapter.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Presburger.NatSemilinear Mell.Audit.PresburgerNatSemilinearExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-a0-qe-adapter.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Presburger/NatSemilinear.v theories/Audit/PresburgerNatSemilinearExamples.v

check-t10-a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalDefinability.vo theories/Audit/SemilinearClosureStatements.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-a.log
	test -f theories/Audit/SemilinearClosureStatements.vo

audit-t10-a: check-t10-a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/SemilinearClosureStatements.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-a.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-a.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Semilinear.Closure Mell.Geometry.RationalDefinability Mell.Audit.SemilinearClosureStatements 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Semilinear/Closure.v theories/Geometry/RationalDefinability.v theories/Audit/SemilinearClosureStatements.v

check-t10-b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Order/PeriodicOrder.vo theories/Audit/PeriodicOrderStatements.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-b.log

audit-t10-b: check-t10-b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/PeriodicOrderStatements.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-b.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-b.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Order.PeriodicOrder Mell.Audit.PeriodicOrderStatements 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Order/PeriodicOrder.v theories/Audit/PeriodicOrderStatements.v

check-t10-c1-hl: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QConeCore.vo theories/Geometry/RationalHToV.vo theories/Audit/RationalHToVExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c1-hl.log
	test -f theories/Audit/RationalHToVExamples.vo

audit-t10-c1-hl: check-t10-c1-hl
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalHToVExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c1-hl.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c1-hl.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c1-hl.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c1-hl.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QConeCore Mell.Geometry.RationalHToV Mell.Audit.RationalHToVExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c1-hl.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QConeCore.v theories/Geometry/RationalHToV.v theories/Audit/RationalHToVExamples.v

check-t10-c1-qe1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalQEOne.vo theories/Audit/RationalQEOneExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c1-qe1.log
	test -f theories/Audit/RationalQEOneExamples.vo

audit-t10-c1-qe1: check-t10-c1-qe1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalQEOneExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c1-qe1.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c1-qe1.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c1-qe1.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c1-qe1.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.RationalQEOne Mell.Audit.RationalQEOneExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c1-qe1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/RationalQEOne.v theories/Audit/RationalQEOneExamples.v

check-t10-c1-qe2: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalQENormalForm.vo theories/Audit/RationalQENormalFormExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c1-qe2.log
	test -f theories/Audit/RationalQENormalFormExamples.vo

audit-t10-c1-qe2: check-t10-c1-qe2
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalQENormalFormExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c1-qe2.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c1-qe2.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c1-qe2.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c1-qe2.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c1-qe2.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.RationalQENormalForm Mell.Audit.RationalQENormalFormExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c1-qe2.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/RationalQENormalForm.v theories/Audit/RationalQENormalFormExamples.v

check-t10-c1-assembly: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalConeAssembly.vo theories/Audit/RationalConeAssemblyExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c1-assembly.log
	test -f theories/Audit/RationalConeAssemblyExamples.vo

audit-t10-c1-assembly: check-t10-c1-assembly
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalConeAssemblyExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c1-assembly.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.RationalConeAssembly Mell.Audit.RationalConeAssemblyExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c1-assembly.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/RationalConeAssembly.v theories/Audit/RationalConeAssemblyExamples.v

check-t10-c2-g0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/LatticeGordanH.vo theories/Audit/LatticeGordanHExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-g0.log
	test -f theories/Audit/LatticeGordanHExamples.vo

audit-t10-c2-g0: check-t10-c2-g0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LatticeGordanHExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-g0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.LatticeGordanH Mell.Audit.LatticeGordanHExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-g0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/LatticeGordanH.v theories/Audit/LatticeGordanHExamples.v

check-t10-c2-g1-i: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/LatticeGordanInterface.vo theories/Audit/LatticeGordanInterfaceExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-g1-i.log
	test -f theories/Audit/LatticeGordanInterfaceExamples.vo

audit-t10-c2-g1-i: check-t10-c2-g1-i
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LatticeGordanInterfaceExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	grep -F 'lattice_gordan_contract =' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-i.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.LatticeGordanInterface Mell.Audit.LatticeGordanInterfaceExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-g1-i.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/LatticeGordanInterface.v theories/Audit/LatticeGordanInterfaceExamples.v

check-t10-c2-g1-hilbert: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/LatticeGordanV.vo theories/Audit/LatticeGordanVExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-g1-hilbert.log
	test -f theories/Audit/LatticeGordanVExamples.vo

audit-t10-c2-g1-hilbert: check-t10-c2-g1-hilbert
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LatticeGordanVExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	grep -F 'qcone_generated_aligned_coefficients' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	grep -F 'integer_points_vcone_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-hilbert.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.LatticeGordanV Mell.Audit.LatticeGordanVExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-g1-hilbert.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/LatticeGordanV.v theories/Audit/LatticeGordanVExamples.v

check-t10-c2-g1-pullback: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/LatticeGordanPullback.vo theories/Audit/LatticeGordanPullbackExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-g1-pullback.log
	test -f theories/Audit/LatticeGordanPullbackExamples.vo

audit-t10-c2-g1-pullback: check-t10-c2-g1-pullback
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LatticeGordanPullbackExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	grep -F 'vcone_pullback_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-pullback.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.LatticeGordanPullback Mell.Audit.LatticeGordanPullbackExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-g1-pullback.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/LatticeGordanPullback.v theories/Audit/LatticeGordanPullbackExamples.v

check-t10-c2-g1-main: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/LatticeGordanMain.vo theories/Audit/LatticeGordanMainExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-g1-main.log
	test -f theories/Audit/LatticeGordanMainExamples.vo

audit-t10-c2-g1-main: check-t10-c2-g1-main
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/LatticeGordanMainExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	grep -F 'lattice_gordan' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-g1-main.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.LatticeGordanMain Mell.Audit.LatticeGordanMainExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-g1-main.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/LatticeGordanMain.v theories/Audit/LatticeGordanMainExamples.v

check-t10-c2-l0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/ClosedLinearization.vo theories/Audit/ClosedLinearizationL0Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-l0.log
	test -f theories/Audit/ClosedLinearizationL0Examples.vo

audit-t10-c2-l0: check-t10-c2-l0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/ClosedLinearizationL0Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	grep -F 'difference_group_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-l0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.ClosedLinearization Mell.Audit.ClosedLinearizationL0Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-l0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/ClosedLinearization.v theories/Audit/ClosedLinearizationL0Examples.v

check-t10-c2-l0-r: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/ClosedLinearization.vo theories/Audit/ClosedLinearizationL0Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-l0-r.log
	test -f theories/Audit/ClosedLinearizationL0Examples.vo

audit-t10-c2-l0-r: check-t10-c2-l0-r
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/ClosedLinearizationL0Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	grep -F 'FullPeriodic =' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	grep -F 'PolyhedralFullPeriodic =' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	grep -F 'full_periodic_iff_linearization_fixed' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-l0-r.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.ClosedLinearization Mell.Audit.ClosedLinearizationL0Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-l0-r.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/ClosedLinearization.v theories/Audit/ClosedLinearizationL0Examples.v

check-t10-c2-l1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalClosure.vo theories/Audit/RationalClosureExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-l1.log
	test -f theories/Audit/RationalClosureExamples.vo

audit-t10-c2-l1: check-t10-c2-l1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalClosureExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'qclosure_qdefinable' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'qclosure_is_cone' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'qclosure_topologically_closed' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'QClosure =' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'QDefinable =' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	grep -F 'RationalCone' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-l1.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.RationalClosure Mell.Audit.RationalClosureExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-l1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/RationalClosure.v theories/Audit/RationalClosureExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/RationalClosure.v theories/Audit/RationalClosureExamples.v

check-t10-c2-l2: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/ClosedLinearizationL2.vo theories/Audit/ClosedLinearizationL2Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c2-l2.log
	test -f theories/Audit/ClosedLinearizationL2Examples.vo

audit-t10-c2-l2: check-t10-c2-l2
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/ClosedLinearizationL2Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	grep -F 'closed_linearization_full' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	grep -F 'closed_linearization_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c2-l2.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.ClosedLinearizationL2 Mell.Audit.ClosedLinearizationL2Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c2-l2.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/ClosedLinearizationL2.v theories/Audit/ClosedLinearizationL2Examples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/ClosedLinearizationL2.v theories/Audit/ClosedLinearizationL2Examples.v

check-t10-c3-0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/Center.vo theories/Audit/CenterExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-0.log
	test -f theories/Audit/CenterExamples.vo

audit-t10-c3-0: check-t10-c3-0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/CenterExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-0.log
	grep -F 'center_in_difference' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	grep -F 'center_add' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.Center Mell.Audit.CenterExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/Center.v theories/Audit/CenterExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/Center.v theories/Audit/CenterExamples.v

check-t10-c3-1a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/RationalSpan.vo theories/Audit/RationalSpanExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-1a.log
	test -f theories/Audit/RationalSpanExamples.vo

audit-t10-c3-1a: check-t10-c3-1a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/RationalSpanExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	grep -F 'finite_p_spanning' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-1a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.RationalSpan Mell.Audit.RationalSpanExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-1a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/RationalSpan.v theories/Audit/RationalSpanExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/RationalSpan.v theories/Audit/RationalSpanExamples.v

check-t10-c3-1b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/CenterCharacterization.vo theories/Audit/CenterCharacterizationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-1b.log
	test -f theories/Audit/CenterCharacterizationExamples.vo

audit-t10-c3-1b: check-t10-c3-1b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/CenterCharacterizationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	grep -F 'center_characterization' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-1b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.CenterCharacterization Mell.Audit.CenterCharacterizationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-1b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/CenterCharacterization.v theories/Audit/CenterCharacterizationExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/CenterCharacterization.v theories/Audit/CenterCharacterizationExamples.v

check-t10-c3-2a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/SpanPerturbation.vo theories/Audit/SpanPerturbationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-2a.log
	test -f theories/Audit/SpanPerturbationExamples.vo

audit-t10-c3-2a: check-t10-c3-2a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/SpanPerturbationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	grep -F 'qspan_uniform_small_coefficients' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-2a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.SpanPerturbation Mell.Audit.SpanPerturbationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-2a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/SpanPerturbation.v theories/Audit/SpanPerturbationExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/SpanPerturbation.v theories/Audit/SpanPerturbationExamples.v

check-t10-c3-2b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/CenterAbsorption.vo theories/Audit/CenterAbsorptionExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-2b.log
	test -f theories/Audit/CenterAbsorptionExamples.vo

audit-t10-c3-2b: check-t10-c3-2b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/CenterAbsorptionExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	grep -F 'center_add_closed_linearization' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	grep -F 'center_absorbs_closed_linearization' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-2b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.CenterAbsorption Mell.Audit.CenterAbsorptionExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-2b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/CenterAbsorption.v theories/Audit/CenterAbsorptionExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/CenterAbsorption.v theories/Audit/CenterAbsorptionExamples.v

check-t10-c3-3: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/CenterPushIn.vo theories/Audit/CenterPushInExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c3-3.log
	test -f theories/Audit/CenterPushInExamples.vo

audit-t10-c3-3: check-t10-c3-3
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/CenterPushInExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c3-3.log
	grep -F 'center_anchor' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	grep -F 'closed_linearization_push_in_offset' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	grep -F 'closed_linearization_push_in' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c3-3.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.CenterPushIn Mell.Audit.CenterPushInExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c3-3.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/CenterPushIn.v theories/Audit/CenterPushInExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/CenterPushIn.v theories/Audit/CenterPushInExamples.v

check-t10-c4-0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/Faces.vo theories/Audit/FacesExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-0.log
	test -f theories/Audit/FacesExamples.vo

audit-t10-c4-0: check-t10-c4-0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FacesExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-0.log
	grep -F 'face_generator_filter' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	grep -F 'polyhedral_face_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.Faces Mell.Audit.FacesExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/Faces.v theories/Audit/FacesExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/Faces.v theories/Audit/FacesExamples.v

check-t10-c4-1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FiniteFaces.vo theories/Audit/FiniteFacesExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-1.log
	test -f theories/Audit/FiniteFacesExamples.vo

audit-t10-c4-1: check-t10-c4-1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FiniteFacesExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'all_sublists_complete' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'all_sublists_length' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'face_has_sublist_generators' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'polyhedral_faces_finite_bounded' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'polyhedral_faces_finite' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-1.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FiniteFaces Mell.Audit.FiniteFacesExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FiniteFaces.v theories/Audit/FiniteFacesExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/FiniteFaces.v theories/Audit/FiniteFacesExamples.v

check-t10-c4-2a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FaceOrder.vo theories/Audit/FaceOrderExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-2a.log
	test -f theories/Audit/FaceOrderExamples.vo

audit-t10-c4-2a: check-t10-c4-2a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceOrderExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	grep -F 'deduplicate_same_set' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	grep -F 'polyhedral_faces_linearized' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-2a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FaceOrder Mell.Audit.FaceOrderExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-2a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FaceOrder.v theories/Audit/FaceOrderExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/FaceOrder.v theories/Audit/FaceOrderExamples.v

check-t10-c4-2b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QcLinearAlgebra.vo theories/Geometry/FaceDimension.vo theories/Audit/FaceDimensionExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-2b.log
	test -f theories/Audit/FaceDimensionExamples.vo

audit-t10-c4-2b: check-t10-c4-2b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceDimensionExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	grep -F 'qspan_of_cone_difference' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	grep -F 'proper_face_span_strict' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	grep -F 'proper_face_dimension_lt' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	grep -F 'linearized_proper_faces_index_and_dimension' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-2b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QcLinearAlgebra Mell.Geometry.FaceDimension Mell.Audit.FaceDimensionExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-2b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QcLinearAlgebra.v theories/Geometry/FaceDimension.v theories/Audit/FaceDimensionExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/QcLinearAlgebra.v theories/Geometry/FaceDimension.v theories/Audit/FaceDimensionExamples.v

check-t10-c4-3a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FaceStrippingExtract.vo theories/Audit/FaceStrippingExtractExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3a.log
	test -f theories/Audit/FaceStrippingExtractExamples.vo

audit-t10-c4-3a: check-t10-c4-3a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceStrippingExtractExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	grep -F 'face_periodic_finitely_generated' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	grep -F 'extract_face_cylindric' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	grep -F 'extract_remainder_cylindric' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-3a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FaceStrippingExtract Mell.Audit.FaceStrippingExtractExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FaceStrippingExtract.v theories/Audit/FaceStrippingExtractExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/FaceStrippingExtract.v theories/Audit/FaceStrippingExtractExamples.v

check-t10-c4-3b-0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FaceStrippingFinitary.vo theories/Audit/FaceStrippingFinitaryExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-0.log
	test -f theories/Audit/FaceStrippingFinitaryExamples.vo

audit-t10-c4-3b-0: check-t10-c4-3b-0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceStrippingFinitaryExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	grep -F 'slice_finite_cover' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	grep -F 'finitary_qcylindric_sub' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	grep -F 'extract_remainder_finitary' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	! grep -F 'Eqdep.Eq_rect_eq.eq_rect_eq' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	! grep -F 'FunctionalExtensionality.functional_extensionality_dep' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	! grep -F 'Eqdep_dec.UIP_dec' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	! grep -F 'eq_rect_eq_dec' $(CORE_LOG_DIR)/audit-t10-c4-3b-0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FaceStrippingFinitary Mell.Audit.FaceStrippingFinitaryExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FaceStrippingFinitary.v theories/Audit/FaceStrippingFinitaryExamples.v
	! grep -R -E 'UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description' theories/Geometry/FaceStrippingFinitary.v theories/Audit/FaceStrippingFinitaryExamples.v

check-t10-c4-3b-1-hrep-a0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QratAdapter.vo theories/Audit/QratAdapterExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-a0.log
	test -f theories/Audit/QratAdapterExamples.vo

audit-t10-c4-3b-1-hrep-a0: check-t10-c4-3b-1-hrep-a0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QratAdapterExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log
	grep -F 'q_to_rat_eq_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log
	grep -F 'rat_to_q_to_rat' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log
	grep -F 'q_to_rat_to_q' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log)" -eq 3
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QratAdapter Mell.Audit.QratAdapterExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-a0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QratAdapter.v theories/Audit/QratAdapterExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QratAdapter.v theories/Audit/QratAdapterExamples.v

check-t10-c4-3b-1-hrep-a1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QratAdapter.vo theories/Audit/QratArithmeticExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-a1.log
	test -f theories/Audit/QratArithmeticExamples.vo

audit-t10-c4-3b-1-hrep-a1: check-t10-c4-3b-1-hrep-a1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QratArithmeticExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	grep -F 'q_to_rat_add' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	grep -F 'q_to_rat_inv' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	grep -F 'q_to_rat_le_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	grep -F 'q_to_rat_lt_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	grep -F 'rat_to_q_nonnegative' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log)" -eq 30
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a1.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QratAdapter Mell.Audit.QratArithmeticExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-a1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QratAdapter.v theories/Audit/QratArithmeticExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QratAdapter.v theories/Audit/QratArithmeticExamples.v

check-t10-c4-3b-1-hrep-a2: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QratVectorAdapter.vo theories/Audit/QratVectorAdapterExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-a2.log
	test -f theories/Audit/QratVectorAdapterExamples.vo

audit-t10-c4-3b-1-hrep-a2: check-t10-c4-3b-1-hrep-a2
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QratVectorAdapterExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	grep -F 'qvec_to_rat_col_eq_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	grep -F 'qvec_to_rat_linear_combination' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	grep -F 'q_to_rat_qinner' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	grep -F 'rat_cols_of_list_surjective' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log)" -eq 37
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-a2.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QratVectorAdapter Mell.Audit.QratVectorAdapterExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-a2.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QratVectorAdapter.v theories/Audit/QratVectorAdapterExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QratVectorAdapter.v theories/Audit/QratVectorAdapterExamples.v

check-t10-c4-3b-1-hrep-b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QratConeAdapter.vo theories/Audit/QratConeAdapterExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-b.log
	test -f theories/Audit/QratConeAdapterExamples.vo

audit-t10-c4-3b-1-hrep-b: check-t10-c4-3b-1-hrep-b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QratConeAdapterExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	grep -F 'rat_fset_of_generators' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	grep -F 'rat_columns_polyhedra_cone' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	grep -F 'qcone_generated_polyhedra_cone' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log)" -eq 15
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QratConeAdapter Mell.Audit.QratConeAdapterExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QratConeAdapter.v theories/Audit/QratConeAdapterExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QratConeAdapter.v theories/Audit/QratConeAdapterExamples.v

check-t10-c4-3b-1-hrep-c: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QratHomogeneousAdapter.vo theories/Audit/QratHomogeneousAdapterExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-c.log
	test -f theories/Audit/QratHomogeneousAdapterExamples.vo

audit-t10-c4-3b-1-hrep-c: check-t10-c4-3b-1-hrep-c
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QratHomogeneousAdapterExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	grep -F 'rat_cone_finite_base' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	grep -F 'rat_cone_homogeneous_base' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	grep -F 'polyhedra_cone_homogeneous_base' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log)" -eq 9
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-c.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QratHomogeneousAdapter Mell.Audit.QratHomogeneousAdapterExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-c.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QratHomogeneousAdapter.v theories/Audit/QratHomogeneousAdapterExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QratHomogeneousAdapter.v theories/Audit/QratHomogeneousAdapterExamples.v

check-t10-c4-3b-1-hrep-d: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/QIntegerHRep.vo theories/Audit/QIntegerHRepExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-hrep-d.log
	test -f theories/Audit/QIntegerHRepExamples.vo

audit-t10-c4-3b-1-hrep-d: check-t10-c4-3b-1-hrep-d
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/QIntegerHRepExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	grep -F 'qnormal_clear_denominators' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	grep -F 'qnormal_integer_nonnegative_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	grep -F 'polyhedral_cone_integer_hrep' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log)" -eq 5
	! grep -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	! grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-hrep-d.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.QIntegerHRep Mell.Audit.QIntegerHRepExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-hrep-d.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/QIntegerHRep.v theories/Audit/QIntegerHRepExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/QIntegerHRep.v theories/Audit/QIntegerHRepExamples.v

check-t10-c4-3b-1-b1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FaceStrippingBases.vo theories/Audit/FaceStrippingBasesB1Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-b1.log
	test -f theories/Audit/FaceStrippingBasesB1Examples.vo

audit-t10-c4-3b-1-b1: check-t10-c4-3b-1-b1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceStrippingBasesB1Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log
	grep -F 'integer_affine_inequalities_finitary' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log
	grep -F 'affine_group_inequalities_finitary' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log
	test "$$(grep -c -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log)" -eq 2
	test "$$(grep -c -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log)" -eq 2
	test "$$(grep -c -E '^[[:alnum:]_.]+[[:space:]]+:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log)" -eq 2
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b1.log)" -eq 2
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FaceStrippingBases Mell.Audit.FaceStrippingBasesB1Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-b1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FaceStrippingBases.v theories/Audit/FaceStrippingBasesB1Examples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/FaceStrippingBases.v theories/Audit/FaceStrippingBasesB1Examples.v

check-t10-c4-3b-1-b2: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/CommonIntegerFaceNormals.vo theories/Audit/CommonIntegerFaceNormalsExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-b2.log
	test -f theories/Audit/CommonIntegerFaceNormalsExamples.vo

audit-t10-c4-3b-1-b2: check-t10-c4-3b-1-b2
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/CommonIntegerFaceNormalsExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log
	grep -F 'integer_face_witness' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log
	grep -F 'face_active_integer_normals' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log
	grep -F 'polyhedral_common_integer_face_normals' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log
	test "$$(grep -c -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log)" -eq 3
	test "$$(grep -c -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log)" -eq 3
	test "$$(grep -c -E '^[[:alnum:]_.]+[[:space:]]+:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log)" -eq 3
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b2.log)" -eq 3
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.CommonIntegerFaceNormals Mell.Audit.CommonIntegerFaceNormalsExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-b2.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/CommonIntegerFaceNormals.v theories/Audit/CommonIntegerFaceNormalsExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/CommonIntegerFaceNormals.v theories/Audit/CommonIntegerFaceNormalsExamples.v

check-t10-c4-3b-1-b3: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/FaceZeroPatternWitness.vo theories/Audit/FaceZeroPatternWitnessExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-b3.log
	test -f theories/Audit/FaceZeroPatternWitnessExamples.vo

audit-t10-c4-3b-1-b3: check-t10-c4-3b-1-b3
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/FaceZeroPatternWitnessExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log
	grep -F 'inactive_supporting_normal_positive_on_face' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log
	grep -F 'inactive_normals_positive_sum' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log
	grep -F 'face_zero_pattern_witness' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log
	grep -F 'periodic_polyhedral_common_zero_pattern_normals' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log
	test "$$(grep -c -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log)" -eq 4
	test "$$(grep -c -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log)" -eq 4
	test "$$(grep -c -E '^[[:alnum:]_.]+[[:space:]]+:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log)" -eq 4
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b3.log)" -eq 1
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.FaceZeroPatternWitness Mell.Audit.FaceZeroPatternWitnessExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-b3.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/FaceZeroPatternWitness.v theories/Audit/FaceZeroPatternWitnessExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/FaceZeroPatternWitness.v theories/Audit/FaceZeroPatternWitnessExamples.v

check-t10-c4-3b-1-b4: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Geometry/Corollary67Finitary.vo theories/Audit/Corollary67FinitaryExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-c4-3b-1-b4.log
	test -f theories/Audit/Corollary67FinitaryExamples.vo

audit-t10-c4-3b-1-b4: check-t10-c4-3b-1-b4
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/Corollary67FinitaryExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	grep -F 'integer_ge_rational_iff_ceiling' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	grep -F 'integer_eq_rational_iff_two_ceilings' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	grep -F 'rational_slice_affine_group_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	grep -F 'homogeneous_group_face_period_iff' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	grep -F 'corollary_6_7_finitary' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log
	test "$$(grep -c -F 'Axioms:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log)" -eq 1
	test "$$(grep -c -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log)" -eq 1
	test "$$(grep -c -E '^[[:alnum:]_.]+[[:space:]]+:' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log)" -eq 1
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-c4-3b-1-b4.log)" -eq 4
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Geometry.Corollary67Finitary Mell.Audit.Corollary67FinitaryExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-c4-3b-1-b4.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Geometry/Corollary67Finitary.v theories/Audit/Corollary67FinitaryExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Geometry/Corollary67Finitary.v theories/Audit/Corollary67FinitaryExamples.v

check-t10-d-task1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/Runs.vo theories/VAS/JancarOrder.vo theories/Audit/VASJancarExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task1.log
	test -f theories/Audit/VASJancarExamples.vo

audit-t10-d-task1: check-t10-d-task1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASJancarExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task1.log
	grep -F 'vas_reach_run_iff' $(CORE_LOG_DIR)/audit-t10-d-task1.log
	grep -F 'vas_reach_monotone' $(CORE_LOG_DIR)/audit-t10-d-task1.log
	grep -F 'jancar_run_le_iff_higman' $(CORE_LOG_DIR)/audit-t10-d-task1.log
	grep -F 'jancar_run_wqo' $(CORE_LOG_DIR)/audit-t10-d-task1.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-d-task1.log)" -eq 4
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.Runs Mell.VAS.JancarOrder Mell.Audit.VASJancarExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/Runs.v theories/VAS/JancarOrder.v theories/Audit/VASJancarExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/Runs.v theories/VAS/JancarOrder.v theories/Audit/VASJancarExamples.v

check-t10-d-task2a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/Transformer.vo theories/VAS/TransformerJancar.vo theories/Audit/VASTransformerExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task2a.log
	test -f theories/Audit/VASTransformerExamples.vo

audit-t10-d-task2a: check-t10-d-task2a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASTransformerExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'capacity_transformer_periodic' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'periodic_nrelation_compose' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'transformer_along_run_periodic' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'jancar_run_le_transformer' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'transformer_realized_by_jancar_extension' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	grep -F 'transformer_along_run_iff_jancar_extension' $(CORE_LOG_DIR)/audit-t10-d-task2a.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-d-task2a.log)" -eq 6
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.Transformer Mell.VAS.TransformerJancar Mell.Audit.VASTransformerExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task2a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/Transformer.v theories/VAS/TransformerJancar.v theories/Audit/VASTransformerExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/Transformer.v theories/VAS/TransformerJancar.v theories/Audit/VASTransformerExamples.v

check-t10-d-task2b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/RelationCone.vo theories/VAS/AsymptoticRelation.vo theories/Audit/VASAsymptoticRelationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task2b.log
	test -f theories/Audit/VASAsymptoticRelationExamples.vo

audit-t10-d-task2b: check-t10-d-task2b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASAsymptoticRelationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'periodic_cone_positive_multiple_iff' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'periodic_relation_cone_compose' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'qdefinable_relation_compose' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'lemma_5_1_asymptotic_relation_compose' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'lemma_5_1_nrelation_compose' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	grep -F 'transformer_along_run_asymptotic_of_capacities' $(CORE_LOG_DIR)/audit-t10-d-task2b.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-d-task2b.log)" -eq 6
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.RelationCone Mell.VAS.AsymptoticRelation Mell.Audit.VASAsymptoticRelationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task2b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/RelationCone.v theories/VAS/AsymptoticRelation.v theories/Audit/VASAsymptoticRelationExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/RelationCone.v theories/VAS/AsymptoticRelation.v theories/Audit/VASAsymptoticRelationExamples.v

check-t10-d-task3a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/Intraproductions.vo theories/Audit/VASIntraproductionsExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task3a.log
	test -f theories/Audit/VASIntraproductionsExamples.vo

audit-t10-d-task3a: check-t10-d-task3a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASIntraproductionsExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'qgamma_iff_occurs_in_omega' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'intraproduction_periodic' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'lemma_5_5_qgamma_add_intraproduction' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'lemma_5_6_intraproduction_dominates' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'finite_gamma_coordinate_values_iff_bounded' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	grep -F 'bounded_coordinate_intraproduction_zero' $(CORE_LOG_DIR)/audit-t10-d-task3a.log
	test "$$(grep -c -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-d-task3a.log)" -eq 6
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.Intraproductions Mell.Audit.VASIntraproductionsExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task3a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/Intraproductions.v theories/Audit/VASIntraproductionsExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/Intraproductions.v theories/Audit/VASIntraproductionsExamples.v

check-t10-d-task3b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/IntraproductionsLemma57.vo theories/Audit/VASIntraproductionsLemma57Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task3b.log
	test -f theories/Audit/VASIntraproductionsLemma57Examples.vo

audit-t10-d-task3b: check-t10-d-task3b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASIntraproductionsLemma57Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	grep -F 'qgamma_unbounded_strict_comparable_pair' $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	grep -F 'unbounded_coordinate_positive_intraproduction' $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	grep -F 'intraproduction_positive_on_all_unbounded' $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	grep -F 'lemma_5_7_bounded_coordinates_intraproduction' $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	test "$$(grep -c -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-d-task3b.log)" -eq 4
	! grep -F 'ClassicalEpsilon.constructive_indefinite_description' $(CORE_LOG_DIR)/audit-t10-d-task3b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.IntraproductionsLemma57 Mell.Audit.VASIntraproductionsLemma57Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task3b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/IntraproductionsLemma57.v theories/Audit/VASIntraproductionsLemma57Examples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/IntraproductionsLemma57.v theories/Audit/VASIntraproductionsLemma57Examples.v

check-t10-d-task4a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/ProductionGraph.vo theories/VAS/ProductionGraphPaths.vo theories/Audit/VASProductionGraphExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task4a.log
	test -f theories/Audit/VASProductionGraphExamples.vo

audit-t10-d-task4a: check-t10-d-task4a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASProductionGraphExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'corollary_5_9_omega_endpoints_special' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'corollary_5_10_production_graph_strongly_connected' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'corollary_5_11_projected_states_antichain' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'production_graph_states_finite' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'production_graph_transitions_finite' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	grep -F 'finite_production_graph_exists' $(CORE_LOG_DIR)/audit-t10-d-task4a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.ProductionGraph Mell.VAS.ProductionGraphPaths Mell.Audit.VASProductionGraphExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task4a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/ProductionGraph.v theories/VAS/ProductionGraphPaths.v theories/Audit/VASProductionGraphExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/ProductionGraph.v theories/VAS/ProductionGraphPaths.v theories/Audit/VASProductionGraphExamples.v

check-t10-d-task4b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/ProductionGraphFiniteness.vo theories/Audit/VASProductionGraphFinitenessExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task4b.log
	test -f theories/Audit/VASProductionGraphFinitenessExamples.vo

audit-t10-d-task4b: check-t10-d-task4b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASProductionGraphFinitenessExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	grep -F 'fixed_mask_simple_path_uniform_bound' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	grep -F 'fixed_capacity_production_states_uniform_finite' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	grep -F 'fixed_capacity_production_transitions_uniform_finite' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	grep -F 'graph_signature_witness_independent' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	grep -F 'corollary_5_12_production_graph_class_finite' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	! grep -E -i 'ClassicalEpsilon|constructive_indefinite_description|dependent.choice|countable.choice|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|oracle' $(CORE_LOG_DIR)/audit-t10-d-task4b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.ProductionGraphFiniteness Mell.Audit.VASProductionGraphFinitenessExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task4b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/ProductionGraphFiniteness.v theories/Audit/VASProductionGraphFinitenessExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/ProductionGraphFiniteness.v theories/Audit/VASProductionGraphFinitenessExamples.v

check-t10-d-task5a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/GraphParikh.vo theories/VAS/Kirchhoff.vo theories/VAS/EulerCycles.vo theories/Audit/VASKirchhoffExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task5a.log
	test -f theories/Audit/VASKirchhoffExamples.vo

audit-t10-d-task5a: check-t10-d-task5a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASKirchhoffExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	grep -F 'graph_cycle_parikh_kirchhoff' $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	grep -F 'positive_kirchhoff_euler_total_cycle' $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	grep -F 'production_graph_positive_kirchhoff_realized' $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	! grep -E -i 'ClassicalEpsilon|constructive_indefinite_description|dependent.choice|countable.choice|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|oracle' $(CORE_LOG_DIR)/audit-t10-d-task5a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.GraphParikh Mell.VAS.Kirchhoff Mell.VAS.EulerCycles Mell.Audit.VASKirchhoffExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task5a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/GraphParikh.v theories/VAS/Kirchhoff.v theories/VAS/EulerCycles.v theories/Audit/VASKirchhoffExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/GraphParikh.v theories/VAS/Kirchhoff.v theories/VAS/EulerCycles.v theories/Audit/VASKirchhoffExamples.v

check-t10-d-task5b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/KirchhoffRelation.vo theories/VAS/KirchhoffDefinability.vo theories/VAS/KirchhoffLemma514.vo theories/Audit/VASKirchhoffRelationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task5b.log
	test -f theories/Audit/VASKirchhoffRelationExamples.vo

audit-t10-d-task5b: check-t10-d-task5b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASKirchhoffRelationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	grep -F 'kirchhoff_relation_for_edges_qdefinable' $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	grep -F 'kirchhoff_relation_exact_edges_independent' $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	grep -F 'production_kirchhoff_relation_qdefinable' $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	grep -F 'production_graph_total_cycle_scaled_gamma_displacement' $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	grep -F 'lemma_5_14_gamma_in_kirchhoff_relation' $(CORE_LOG_DIR)/audit-t10-d-task5b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.KirchhoffRelation Mell.VAS.KirchhoffDefinability Mell.VAS.KirchhoffLemma514 Mell.Audit.VASKirchhoffRelationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task5b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/KirchhoffRelation.v theories/VAS/KirchhoffDefinability.v theories/VAS/KirchhoffLemma514.v theories/Audit/VASKirchhoffRelationExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/KirchhoffRelation.v theories/VAS/KirchhoffDefinability.v theories/VAS/KirchhoffLemma514.v theories/Audit/VASKirchhoffRelationExamples.v

check-t10-d-task5c: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/GraphCyclePumping.vo theories/VAS/KirchhoffScaling.vo theories/VAS/KirchhoffLemma515.vo theories/Audit/VASKirchhoffLemma515Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task5c.log
	test -f theories/Audit/VASKirchhoffLemma515Examples.vo

audit-t10-d-task5c: check-t10-d-task5c
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASKirchhoffLemma515Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'positive_rational_kirchhoff_uniform_scaling' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'positive_residual_kirchhoff' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'production_graph_cycle_realizable_after_pumping' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'pumped_graph_cycle_iterated_run' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'pumped_graph_cycle_iterated' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	grep -F 'lemma_5_15_kirchhoff_in_capacity_cone' $(CORE_LOG_DIR)/audit-t10-d-task5c.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.GraphCyclePumping Mell.VAS.KirchhoffScaling Mell.VAS.KirchhoffLemma515 Mell.Audit.VASKirchhoffLemma515Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task5c.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/GraphCyclePumping.v theories/VAS/KirchhoffScaling.v theories/VAS/KirchhoffLemma515.v theories/Audit/VASKirchhoffLemma515Examples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/GraphCyclePumping.v theories/VAS/KirchhoffScaling.v theories/VAS/KirchhoffLemma515.v theories/Audit/VASKirchhoffLemma515Examples.v

check-t10-d-task5d: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/FiniteKirchhoffRelations.vo theories/VAS/KirchhoffCorollary516.vo theories/Audit/VASKirchhoffCorollary516Examples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task5d.log
	test -f theories/Audit/VASKirchhoffCorollary516Examples.vo

audit-t10-d-task5d: check-t10-d-task5d
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASKirchhoffCorollary516Examples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	grep -F 'capacity_cone_union_kirchhoff' $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	grep -F 'finite_production_kirchhoff_relation_representatives' $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	grep -F 'capacity_transformer_cone_qdefinable' $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	grep -F 'corollary_5_16_capacity_transformer_asymptotically_definable' $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	grep -F 'transformer_along_run_asymptotically_definable' $(CORE_LOG_DIR)/audit-t10-d-task5d.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.FiniteKirchhoffRelations Mell.VAS.KirchhoffCorollary516 Mell.Audit.VASKirchhoffCorollary516Examples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task5d.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/FiniteKirchhoffRelations.v theories/VAS/KirchhoffCorollary516.v theories/Audit/VASKirchhoffCorollary516Examples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/FiniteKirchhoffRelations.v theories/VAS/KirchhoffCorollary516.v theories/Audit/VASKirchhoffCorollary516Examples.v

check-t10-d-task6a: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/LinearReachRelation.vo theories/VAS/MinimalRunFiniteBasis.vo theories/Audit/VASMinimalRunExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task6a.log
	test -f theories/Audit/VASMinimalRunExamples.vo

audit-t10-d-task6a: check-t10-d-task6a
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASMinimalRunExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task6a.log
	grep -F 'decorated_linear_run_wqo' $(CORE_LOG_DIR)/audit-t10-d-task6a.log
	grep -F 'decorated_linear_run_finite_cover' $(CORE_LOG_DIR)/audit-t10-d-task6a.log
	grep -F 'linear_omega_finite_cover' $(CORE_LOG_DIR)/audit-t10-d-task6a.log
	grep -F 'linear_run_le_transformer_period_witness' $(CORE_LOG_DIR)/audit-t10-d-task6a.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.LinearReachRelation Mell.VAS.MinimalRunFiniteBasis Mell.Audit.VASMinimalRunExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task6a.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/LinearReachRelation.v theories/VAS/MinimalRunFiniteBasis.v theories/Audit/VASMinimalRunExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/LinearReachRelation.v theories/VAS/MinimalRunFiniteBasis.v theories/Audit/VASMinimalRunExamples.v

check-t10-d-task6b: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/MinimalRunDecomposition.vo theories/Audit/VASMinimalRunDecompositionExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task6b.log
	test -f theories/Audit/VASMinimalRunDecompositionExamples.vo

audit-t10-d-task6b: check-t10-d-task6b
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASMinimalRunDecompositionExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'linear_reach_restricted_iff_omega_run' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'linear_run_transformer_component_sound' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'linear_finite_cover_component_complete' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'linear_reach_finite_basis_decomposition' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'lemma_6_1_linear_reach_decomposition' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	grep -F 'linear_transformer_period_intersection_periodic' $(CORE_LOG_DIR)/audit-t10-d-task6b.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.MinimalRunDecomposition Mell.Audit.VASMinimalRunDecompositionExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task6b.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/MinimalRunDecomposition.v theories/Audit/VASMinimalRunDecompositionExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/MinimalRunDecomposition.v theories/Audit/VASMinimalRunDecompositionExamples.v

check-t10-d-task6c: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/PeriodicIntersection.vo theories/VAS/AlmostSemilinear.vo theories/VAS/LinearReachAlmostSemilinear.vo theories/Audit/VASAlmostSemilinearExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task6c.log
	test -f theories/Audit/VASAlmostSemilinearExamples.vo

audit-t10-d-task6c: check-t10-d-task6c
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASAlmostSemilinearExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'periodic_cone_intersection' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'lemma_6_2_asymptotically_definable_intersection' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'asymptotically_definable_nrelation_intersection' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'generated_period_pair_asymptotically_definable' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'linear_transformer_period_intersection_asymptotically_definable' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'linear_run_transformer_component_almost_semilinear' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'almost_semilinear_nrelation_finite_union' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	grep -F 'linear_reach_restricted_almost_semilinear' $(CORE_LOG_DIR)/audit-t10-d-task6c.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.PeriodicIntersection Mell.VAS.AlmostSemilinear Mell.VAS.LinearReachAlmostSemilinear Mell.Audit.VASAlmostSemilinearExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task6c.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/PeriodicIntersection.v theories/VAS/AlmostSemilinear.v theories/VAS/LinearReachAlmostSemilinear.v theories/Audit/VASAlmostSemilinearExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/PeriodicIntersection.v theories/VAS/AlmostSemilinear.v theories/VAS/LinearReachAlmostSemilinear.v theories/Audit/VASAlmostSemilinearExamples.v

check-t10-d-task6d: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/VAS/SemilinearRelationDecomposition.vo theories/VAS/AlmostSemilinearProjection.vo theories/VAS/Corollary63.vo theories/VAS/StatefulVAS.vo theories/VAS/AlmostSemilinearCoordinateProjection.vo theories/VAS/StatefulAlmostSemilinear.vo theories/Audit/VASCorollary63StatefulExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-d-task6d.log
	test -f theories/Audit/VASCorollary63StatefulExamples.vo

audit-t10-d-task6d: check-t10-d-task6d
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/VASCorollary63StatefulExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-d-task6d.log
	grep -F 'semilinear_nrelation_finite_linear_decomposition' $(CORE_LOG_DIR)/audit-t10-d-task6d.log
	grep -F 'corollary_6_3_plain_post_inter_almost_semilinear' $(CORE_LOG_DIR)/audit-t10-d-task6d.log
	grep -F 'vas_reach_relation_inter_semilinear' $(CORE_LOG_DIR)/audit-t10-d-task6d.log
	grep -F 'vas_post_inter_semilinear' $(CORE_LOG_DIR)/audit-t10-d-task6d.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.VAS.SemilinearRelationDecomposition Mell.VAS.AlmostSemilinearProjection Mell.VAS.Corollary63 Mell.VAS.StatefulVAS Mell.VAS.AlmostSemilinearCoordinateProjection Mell.VAS.StatefulAlmostSemilinear Mell.Audit.VASCorollary63StatefulExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-d-task6d.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/VAS/SemilinearRelationDecomposition.v theories/VAS/AlmostSemilinearProjection.v theories/VAS/Corollary63.v theories/VAS/StatefulVAS.v theories/VAS/AlmostSemilinearCoordinateProjection.v theories/VAS/StatefulAlmostSemilinear.v theories/Audit/VASCorollary63StatefulExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/VAS/SemilinearRelationDecomposition.v theories/VAS/AlmostSemilinearProjection.v theories/VAS/Corollary63.v theories/VAS/StatefulVAS.v theories/VAS/AlmostSemilinearCoordinateProjection.v theories/VAS/StatefulAlmostSemilinear.v theories/Audit/VASCorollary63StatefulExamples.v

.PHONY: check-t10-e0 audit-t10-e0

check-t10-e0: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/StatefulAmalgamation.vo theories/Audit/StatefulAmalgamationExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-e0.log
	test -f theories/Audit/StatefulAmalgamationExamples.vo

audit-t10-e0: check-t10-e0
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/StatefulAmalgamationExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-e0.log
	grep -F 'stateful_context_order_amalgamation' $(CORE_LOG_DIR)/audit-t10-e0.log
	grep -F 'stateful_context_transfer_lemma_8' $(CORE_LOG_DIR)/audit-t10-e0.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.StatefulAmalgamation Mell.Audit.StatefulAmalgamationExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-e0.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/StatefulAmalgamation.v theories/Audit/StatefulAmalgamationExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/BVASS/StatefulAmalgamation.v theories/Audit/StatefulAmalgamationExamples.v

.PHONY: check-t10-e1 audit-t10-e1

check-t10-e1: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/Extend.vo theories/Audit/BVASSExtendExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-e1.log
	test -f theories/Audit/BVASSExtendExamples.vo

audit-t10-e1: check-t10-e1
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/BVASSExtendExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-e1.log
	grep -F 'extend_bvass_reach_iff' $(CORE_LOG_DIR)/audit-t10-e1.log
	grep -F 'extend_local_root_shortening' $(CORE_LOG_DIR)/audit-t10-e1.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.Extend Mell.Audit.BVASSExtendExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-e1.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/Extend.v theories/Audit/BVASSExtendExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/BVASS/Extend.v theories/Audit/BVASSExtendExamples.v

.PHONY: check-t10-e2 audit-t10-e2

check-t10-e2: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/BoundedBranching.vo theories/Audit/BoundedBranchingExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-e2.log
	test -f theories/Audit/BoundedBranchingExamples.vo

audit-t10-e2: check-t10-e2
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/BoundedBranchingExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-e2.log
	grep -F 'finite_basis_bounded_branching_depth' $(CORE_LOG_DIR)/audit-t10-e2.log
	grep -F 'lemma_9_uniform_bounded_branching' $(CORE_LOG_DIR)/audit-t10-e2.log
	grep -F 'lemma_9_reach_bounded_branching_iff' $(CORE_LOG_DIR)/audit-t10-e2.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-e2.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.BoundedBranching Mell.Audit.BoundedBranchingExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-e2.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/BoundedBranching.v theories/Audit/BoundedBranchingExamples.v
	! grep -R -E -i 'ClassicalEpsilon|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/BVASS/BoundedBranching.v theories/Audit/BoundedBranchingExamples.v

.PHONY: check-t10-e3 audit-t10-e3 check-t10-e4 audit-t10-e4

check-t10-e3: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/VASSSection.vo theories/BVASS/BoundedVASSSection.vo theories/Audit/BoundedVASSSectionExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-e3.log
	test -f theories/Audit/BoundedVASSSectionExamples.vo

audit-t10-e3: check-t10-e3
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/BoundedVASSSectionExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-e3.log
	grep -F 'compile_rule_image_correct' $(CORE_LOG_DIR)/audit-t10-e3.log
	grep -F 'bounded_vass_section_correct' $(CORE_LOG_DIR)/audit-t10-e3.log
	grep -F 'lemma_11_bounded_depth_vass_section' $(CORE_LOG_DIR)/audit-t10-e3.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-e3.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.VASSSection Mell.BVASS.BoundedVASSSection Mell.Audit.BoundedVASSSectionExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-e3.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/VASSSection.v theories/BVASS/BoundedVASSSection.v theories/Audit/BoundedVASSSectionExamples.v
	! grep -R -E -i 'ClassicalEpsilon|ClassicalChoice|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/BVASS/VASSSection.v theories/BVASS/BoundedVASSSection.v theories/Audit/BoundedVASSSectionExamples.v

check-t10-e4: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/BVASS/AlmostSemilinear.vo theories/Audit/BVASSAlmostSemilinearExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-e4.log
	test -f theories/Audit/BVASSAlmostSemilinearExamples.vo

audit-t10-e4: check-t10-e4
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/BVASSAlmostSemilinearExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-e4.log
	grep -F 'bvass_reach_is_vass_section' $(CORE_LOG_DIR)/audit-t10-e4.log
	grep -F 'bvass_reach_inter_semilinear' $(CORE_LOG_DIR)/audit-t10-e4.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-e4.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-e4.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.BVASS.AlmostSemilinear Mell.Audit.BVASSAlmostSemilinearExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-e4.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/BVASS/AlmostSemilinear.v theories/Audit/BVASSAlmostSemilinearExamples.v
	! grep -R -E -i 'ClassicalEpsilon|ClassicalChoice|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/BVASS/AlmostSemilinear.v theories/Audit/BVASSAlmostSemilinearExamples.v

.PHONY: check-t10-f audit-t10-f

check-t10-f: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Reduction/ILZ.vo theories/Reduction/MELLToABVASS.vo theories/Reduction/MELLToABVASSCompleteness.vo theories/Reduction/ZeroTest.vo theories/Reduction/Main.vo theories/Audit/MELLReductionExamples.vo 2>&1 | tee $(CORE_LOG_DIR)/check-t10-f.log
	test -f theories/Audit/MELLReductionExamples.vo

audit-t10-f: check-t10-f
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/MELLReductionExamples.v 2>&1 | tee $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'ilz_machine_correct' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'remove_zero_tests_correct' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'reduce_mell_correct' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'reduce_mell_code_correct' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'reduce_mell_many_one' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'Closed under the global context' $(CORE_LOG_DIR)/audit-t10-f.log
	grep -F 'Classical_Prop.classic' $(CORE_LOG_DIR)/audit-t10-f.log
	set -o pipefail; $(OPAMEXEC) coqchk -silent -Q theories Mell -Q vendor/minicooper MiniCooper Mell.Reduction.Main Mell.Audit.MELLReductionExamples 2>&1 | tee $(CORE_LOG_DIR)/coqchk-t10-f.log
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Reduction/ILZ.v theories/Reduction/MELLToABVASS.v theories/Reduction/MELLToABVASSCompleteness.v theories/Reduction/ZeroTest.v theories/Reduction/Main.v theories/Audit/MELLReductionExamples.v
	! grep -R -E -i 'ClassicalEpsilon|ClassicalChoice|UIP|K_dec|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Reduction/ILZ.v theories/Reduction/MELLToABVASS.v theories/Reduction/MELLToABVASSCompleteness.v theories/Reduction/ZeroTest.v theories/Reduction/Main.v theories/Audit/MELLReductionExamples.v

.PHONY: check-final audit-final extract-final check-runtime-mell check-decision-paths check-extraction-differential check-verification-scope check-verification-artifacts audit-verification-gates

check-verification-scope:
	bash scripts/check-verification-scope.sh

check-verification-artifacts:
	bash scripts/check-verification-scope.sh --require-vo

check-final: $(COQMAKEFILE)
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) -j2 theories/Decision/BVAS.vo theories/Decision/MELL.vo theories/Audit/ZeroTestFreeExamples.vo theories/Audit/FiniteSaturationExamples.vo theories/Audit/MultiplicativeWeightExamples.vo theories/Audit/UnitFragmentExamples.vo theories/Audit/DecisionPathAudit.vo theories/Audit/DecisionPathExamples.vo theories/Audit/Regression.vo theories/Audit/Statements.vo 2>&1 | tee $(CORE_LOG_DIR)/check-final.log

audit-final: check-final check-verification-scope
	set -o pipefail; $(OPAMEXEC) coqtop -quiet -batch -Q theories Mell -Q vendor/minicooper MiniCooper -l theories/Audit/Statements.v 2>&1 | tee $(CORE_LOG_DIR)/audit-final.log
	bash scripts/check-assumption-allowlist.sh $(CORE_LOG_DIR)/audit-final.log
	bash scripts/check-coq-source-policy.sh
	bash scripts/check-extraction-policy.sh
	! grep -R -E '(^|[[:space:]])Admitted\.|(^|[[:space:]])admit([.;[:space:]]|$$)|^[[:space:]]*Axiom[[:space:]]|^[[:space:]]*Abort\.' theories/Reduction/FullZeroSystem.v theories/Reduction/ILZRuntime.v theories/Reduction/ILZ.v theories/Reduction/MELLToABVASSRuntime.v theories/Reduction/MELLToABVASS.v theories/Reduction/MELLToABVASSCompleteness.v theories/Reduction/ZeroTest.v theories/Reduction/ZeroTestFree.v theories/Reduction/Main.v theories/BVASS/FiniteSaturation.v theories/Logic/MultiplicativeWeight.v theories/Logic/UnitFragment.v theories/Decision theories/Audit/ZeroTestFreeExamples.v theories/Audit/FiniteSaturationExamples.v theories/Audit/MultiplicativeWeightExamples.v theories/Audit/UnitFragmentExamples.v theories/Audit/DecisionPathAudit.v theories/Audit/DecisionPathExamples.v theories/Audit/Regression.v theories/Audit/Statements.v
	! grep -R -E -i 'ClassicalEpsilon|ClassicalChoice|(^|[^[:alnum:]_])UIP([^[:alnum:]_]|$$)|(^|[^[:alnum:]_])K_dec([^[:alnum:]_]|$$)|eq_rect_eq|Eq_rect_eq|functional_extensionality|constructive_indefinite_description|oracle' theories/Reduction/FullZeroSystem.v theories/Reduction/ILZRuntime.v theories/Reduction/ILZ.v theories/Reduction/MELLToABVASSRuntime.v theories/Reduction/MELLToABVASS.v theories/Reduction/MELLToABVASSCompleteness.v theories/Reduction/ZeroTest.v theories/Reduction/ZeroTestFree.v theories/Reduction/Main.v theories/BVASS/FiniteSaturation.v theories/Logic/MultiplicativeWeight.v theories/Logic/UnitFragment.v theories/Decision theories/Audit/ZeroTestFreeExamples.v theories/Audit/FiniteSaturationExamples.v theories/Audit/MultiplicativeWeightExamples.v theories/Audit/UnitFragmentExamples.v theories/Audit/DecisionPathAudit.v theories/Audit/DecisionPathExamples.v theories/Audit/Regression.v theories/Audit/Statements.v
	! grep -R -E -i 'Unset[[:space:]]+(Guard|Positivity|Universe)[[:space:]]+Checking|Set[[:space:]]+(Guard|Positivity|Universe)[[:space:]]+Checking[[:space:]]+Off' theories/Reduction/FullZeroSystem.v theories/Reduction/ILZRuntime.v theories/Reduction/ILZ.v theories/Reduction/MELLToABVASSRuntime.v theories/Reduction/MELLToABVASS.v theories/Reduction/MELLToABVASSCompleteness.v theories/Reduction/ZeroTest.v theories/Reduction/ZeroTestFree.v theories/Reduction/Main.v theories/BVASS/FiniteSaturation.v theories/Logic/MultiplicativeWeight.v theories/Logic/UnitFragment.v theories/Decision theories/Audit/ZeroTestFreeExamples.v theories/Audit/FiniteSaturationExamples.v theories/Audit/MultiplicativeWeightExamples.v theories/Audit/UnitFragmentExamples.v theories/Audit/DecisionPathAudit.v theories/Audit/DecisionPathExamples.v theories/Audit/Regression.v theories/Audit/Statements.v

extract-final: check-final
	mkdir -p docs/review/extraction/final
	rm -f docs/review/extraction/final/*.ml docs/review/extraction/final/*.mli
	rm -f theories/Decision/Extract.vo theories/Decision/Extract.vok theories/Decision/Extract.vos theories/Decision/Extract.glob
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) theories/Decision/Extract.vo
	bash scripts/check-extraction-policy.sh
	bash scripts/check-extraction-output.sh docs/review/extraction/final 10
	task_tmp=$$(mktemp -d /tmp/mell-final-ocaml.XXXXXX); trap 'rm -rf "$$task_tmp"' EXIT; cp docs/review/extraction/final/*.ml docs/review/extraction/final/*.mli "$$task_tmp"; cd "$$task_tmp"; files=$$(ocamldep -sort *.ml); for f in $$files; do b=$${f%.ml}; if [[ -f $$b.mli ]]; then ocamlfind ocamlc -package zarith -c $$b.mli; fi; ocamlfind ocamlc -package zarith -c $$f; done

check-runtime-mell: extract-final
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; task_tmp=$$(mktemp -d /tmp/mell-final-runtime.XXXXXX); trap 'rm -rf "$$task_tmp"' EXIT; cp docs/review/extraction/final/*.ml docs/review/extraction/final/*.mli docs/review/extraction/final_runner.ml "$$task_tmp"; cd "$$task_tmp"; files=$$(ocamldep -sort *.ml); for f in $$files; do b=$${f%.ml}; if [[ -f $$b.mli ]]; then ocamlfind ocamlopt -package zarith -c $$b.mli || exit 1; fi; ocamlfind ocamlopt -package zarith -c $$f || exit 1; done; objects=""; for f in $$files; do objects="$$objects $${f%.ml}.cmx"; done; ocamlfind ocamlopt -package zarith -linkpkg $$objects -o final_runner; bash "$(CURDIR)/scripts/run-runtime-cases.sh" ./final_runner "$(CURDIR)/docs/review/extraction/runtime-cases.tsv" "$(RUNTIME_CASE_TIMEOUT)" 22 "$(CURDIR)/docs/review/extraction/runtime-case-names.txt" 2>&1 | tee "$(CURDIR)/$(CORE_LOG_DIR)/check-runtime-mell.log"

check-decision-paths: extract-final
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; task_tmp=$$(mktemp -d /tmp/mell-path-runtime.XXXXXX); trap 'rm -rf "$$task_tmp"' EXIT; cp docs/review/extraction/final/*.ml docs/review/extraction/final/*.mli docs/review/extraction/final_runner.ml "$$task_tmp"; cd "$$task_tmp"; files=$$(ocamldep -sort *.ml); for f in $$files; do b=$${f%.ml}; if [[ -f $$b.mli ]]; then ocamlfind ocamlopt -package zarith -c $$b.mli || exit 1; fi; ocamlfind ocamlopt -package zarith -c $$f || exit 1; done; objects=""; for f in $$files; do objects="$$objects $${f%.ml}.cmx"; done; ocamlfind ocamlopt -package zarith -linkpkg $$objects -o final_runner; bash "$(CURDIR)/scripts/run-runtime-cases.sh" ./final_runner "$(CURDIR)/docs/review/extraction/decision-path-cases.tsv" "$(RUNTIME_CASE_TIMEOUT)" 11 "$(CURDIR)/docs/review/extraction/decision-path-case-names.txt" 2>&1 | tee "$(CURDIR)/$(CORE_LOG_DIR)/check-decision-paths.log"

check-extraction-differential: extract-final
	mkdir -p $(CORE_LOG_DIR)
	$(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) theories/Audit/ExtractionDifferentialExamples.vo
	set -o pipefail; task_tmp=$$(mktemp -d /tmp/mell-differential-runtime.XXXXXX); trap 'rm -rf "$$task_tmp"' EXIT; cp docs/review/extraction/final/*.ml docs/review/extraction/final/*.mli docs/review/extraction/differential_runner.ml "$$task_tmp"; cd "$$task_tmp"; files=$$(ocamldep -sort *.ml); for f in $$files; do b=$${f%.ml}; if [[ -f $$b.mli ]]; then ocamlfind ocamlopt -package zarith -c $$b.mli || exit 1; fi; ocamlfind ocamlopt -package zarith -c $$f || exit 1; done; objects=""; for f in $$files; do objects="$$objects $${f%.ml}.cmx"; done; ocamlfind ocamlopt -package zarith -linkpkg $$objects -o differential_runner; bash "$(CURDIR)/scripts/run-runtime-cases.sh" ./differential_runner "$(CURDIR)/docs/review/extraction/differential-cases.tsv" "$(RUNTIME_CASE_TIMEOUT)" 53 "$(CURDIR)/docs/review/extraction/differential-case-names.txt" 2>&1 | tee "$(CURDIR)/$(CORE_LOG_DIR)/check-extraction-differential.log"

audit-verification-gates:
	mkdir -p $(CORE_LOG_DIR)
	set -o pipefail; bash scripts/audit-verification-gates.sh 2>&1 | tee $(CORE_LOG_DIR)/verification-gate-negative-tests.log

clean:
	if [[ -f $(COQMAKEFILE) ]]; then $(OPAMEXEC) $(MAKE) -f $(COQMAKEFILE) clean; fi
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf
