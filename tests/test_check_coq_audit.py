import importlib.util
import pathlib
import unittest


ROOT = pathlib.Path(__file__).resolve().parents[1]
MODULE_PATH = ROOT / "scripts" / "check_coq_audit.py"


def load_audit_module():
    spec = importlib.util.spec_from_file_location("check_coq_audit", MODULE_PATH)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def block(name: str, body: str, *, end_name: str | None = None) -> str:
    end_name = name if end_name is None else end_name
    return (
        f"MELL_AUDIT_BEGIN {name}\n"
        f"{body.rstrip()}\n"
        f"MELL_AUDIT_END {end_name}\n"
    )


class AssumptionTranscriptTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.audit = load_audit_module()

    def assert_rejected(self, text: str, expected=("target",), contains=None):
        with self.assertRaises(self.audit.AuditError) as caught:
            self.audit.parse_assumption_transcript(text, list(expected))
        if contains is not None:
            self.assertIn(contains, str(caught.exception))

    def test_accepts_closed_term(self):
        parsed = self.audit.parse_assumption_transcript(
            block("target", "Closed under the global context"), ["target"]
        )
        self.assertEqual(parsed, {"target": []})

    def test_accepts_exact_classic_only_with_multiline_type(self):
        text = block(
            "target",
            "Axioms:\nClassical_Prop.classic : forall P : Prop,\n  P \\/ ~ P",
        )
        parsed = self.audit.parse_assumption_transcript(text, ["target"])
        self.assertEqual(parsed, {"target": ["Classical_Prop.classic"]})

    def test_rejects_apostrophe_identifier(self):
        self.assert_rejected(
            block("target", "Axioms:\nAuditGateProbe.forbidden' : False"),
            contains="AuditGateProbe.forbidden'",
        )

    def test_rejects_other_qualified_identifier(self):
        self.assert_rejected(
            block("target", "Axioms:\nOther.Module.forbidden : False"),
            contains="Other.Module.forbidden",
        )

    def test_rejects_guard_assumption(self):
        self.assert_rejected(
            block("target", "Axioms:\nnonterminating is assumed to be guarded."),
            contains="assumed to be guarded",
        )

    def test_rejects_missing_log(self):
        with self.assertRaises(self.audit.AuditError) as caught:
            self.audit.read_required_text(ROOT / "does-not-exist.audit.log", "audit log")
        self.assertIn("does not exist", str(caught.exception))

    def test_rejects_empty_log(self):
        self.assert_rejected("", contains="empty")

    def test_rejects_truncated_block(self):
        self.assert_rejected(
            "MELL_AUDIT_BEGIN target\nAxioms:\nClassical_Prop.classic : Prop\n",
            contains="unterminated",
        )

    def test_rejects_missing_expected_theorem(self):
        self.assert_rejected(
            block("other", "Closed under the global context"),
            expected=("target", "other"),
            contains="expected target",
        )

    def test_rejects_duplicate_block(self):
        text = block("target", "Closed under the global context") * 2
        self.assert_rejected(text, contains="duplicate")

    def test_rejects_wrong_end_marker(self):
        self.assert_rejected(
            block("target", "Closed under the global context", end_name="other"),
            contains="does not match",
        )

    def test_rejects_unknown_dependency_format(self):
        self.assert_rejected(
            block("target", "Axioms:\n<unparsed dependency output>"),
            contains="unrecognized",
        )

    def test_rejects_axioms_heading_without_dependency(self):
        self.assert_rejected(block("target", "Axioms:"), contains="no dependency")


class SourcePolicyTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.audit = load_audit_module()

    def assert_violation(self, source: str, contains: str):
        violations = self.audit.scan_coq_source(source, pathlib.Path("Fixture.v"))
        self.assertTrue(any(contains in violation for violation in violations), violations)

    def test_rejects_global_parameter(self):
        self.assert_violation("Parameter forbidden' : False.\n", "Parameter")

    def test_rejects_global_axiom(self):
        self.assert_violation("Axiom forbidden : False.\n", "Axiom")

    def test_rejects_proof_escapes(self):
        for source, token in [
            ("Theorem bad : True. Admitted.\n", "Admitted"),
            ("Theorem bad : True. Proof. admit. Qed.\n", "admit"),
            ("Theorem bad : True. Proof. Abort.\n", "Abort"),
        ]:
            with self.subTest(token=token):
                self.assert_violation(source, token)

    def test_rejects_unsafe_settings(self):
        settings = [
            "Unset Guard Checking.",
            "Unset Positivity Checking.",
            "Unset Universe Checking.",
            "Set Type in Type.",
        ]
        for setting in settings:
            with self.subTest(setting=setting):
                self.assert_violation(setting + "\n", setting)

    def test_ignores_nested_comments_and_strings(self):
        source = r'''
(* Unset Guard Checking.
   (* Parameter nested : False. *)
*)
Definition documentary_string := "Set Type in Type.".
Theorem safe : True. Proof. exact I. Qed.
'''
        self.assertEqual(self.audit.scan_coq_source(source, pathlib.Path("Fixture.v")), [])

    def test_allows_module_type_signature_parameter(self):
        source = "Module Type Signature.\n  Parameter carrier : Type.\nEnd Signature.\n"
        self.assertEqual(self.audit.scan_coq_source(source, pathlib.Path("Fixture.v")), [])

    def test_rejects_parameter_after_module_type(self):
        source = (
            "Module Type Signature. Parameter carrier : Type. End Signature.\n"
            "Parameter forbidden : False.\n"
        )
        self.assert_violation(source, "Parameter")

    def test_unterminated_comment_fails_closed(self):
        with self.assertRaises(self.audit.AuditError) as caught:
            self.audit.scan_coq_source("(* unfinished", pathlib.Path("Fixture.v"))
        self.assertIn("unterminated comment", str(caught.exception))

    def test_unterminated_string_fails_closed(self):
        with self.assertRaises(self.audit.AuditError) as caught:
            self.audit.scan_coq_source('Definition x := "unfinished', pathlib.Path("Fixture.v"))
        self.assertIn("unterminated string", str(caught.exception))


class CoqchkSummaryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.audit = load_audit_module()

    @staticmethod
    def summary(type_in_type="<none>", unsafe="<none>", positivity="<none>"):
        return f"""
CONTEXT SUMMARY
===============

* Theory: Set is predicative

* Constants/Inductives relying on type-in-type: {type_in_type}

* Constants/Inductives relying on unsafe (co)fixpoints: {unsafe}

* Inductives whose positivity is assumed: {positivity}
"""

    def assert_rejected(self, text: str, contains: str):
        with self.assertRaises(self.audit.AuditError) as caught:
            self.audit.parse_coqchk_summary(text)
        self.assertIn(contains, str(caught.exception))

    def test_accepts_all_three_empty_sections(self):
        self.assertEqual(
            self.audit.parse_coqchk_summary(self.summary()),
            {
                "type-in-type": [],
                "unsafe (co)fixpoints": [],
                "positivity assumed": [],
            },
        )

    def test_rejects_each_populated_section(self):
        cases = [
            (dict(type_in_type="\n    Bad.universe"), "type-in-type"),
            (dict(unsafe="\n    Bad.loop"), "unsafe (co)fixpoints"),
            (dict(positivity="\n    Bad.inductive"), "positivity assumed"),
        ]
        for values, label in cases:
            with self.subTest(label=label):
                self.assert_rejected(self.summary(**values), label)

    def test_rejects_missing_context_summary(self):
        self.assert_rejected("ordinary coqchk output", "CONTEXT SUMMARY")

    def test_rejects_missing_required_section(self):
        text = self.summary().replace(
            "* Inductives whose positivity is assumed: <none>\n", ""
        )
        self.assert_rejected(text, "positivity assumed")

    def test_rejects_duplicate_required_section(self):
        heading = "* Constants/Inductives relying on type-in-type: <none>\n"
        self.assert_rejected(self.summary() + heading, "duplicate")

    def test_rejects_truncated_none_marker(self):
        self.assert_rejected(self.summary(unsafe="<no"), "malformed")

    def test_rejects_extra_text_after_none(self):
        self.assert_rejected(
            self.summary(unsafe="<none>\n    Bad.loop"), "unsafe (co)fixpoints"
        )


if __name__ == "__main__":
    unittest.main()
