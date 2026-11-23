#!/usr/bin/env python3
"""Fail-closed parsers for Coq proof-safety audit output."""

from __future__ import annotations

import argparse
import pathlib
import re
import sys


ALLOWED_ASSUMPTIONS = {"Classical_Prop.classic"}
BEGIN_RE = re.compile(r"^MELL_AUDIT_BEGIN ([A-Za-z_][A-Za-z0-9_'.]*)$")
END_RE = re.compile(r"^MELL_AUDIT_END ([A-Za-z_][A-Za-z0-9_'.]*)$")
IDENTIFIER_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)


class AuditError(ValueError):
    """Raised when audit evidence is absent, incomplete, or unsafe."""


def read_required_text(path: pathlib.Path, label: str) -> str:
    if not path.is_file():
        raise AuditError(f"{label} does not exist: {path}")
    text = path.read_text(encoding="utf-8")
    if not text.strip():
        raise AuditError(f"{label} is empty: {path}")
    return text


def read_manifest(path: pathlib.Path) -> list[str]:
    text = read_required_text(path, "assumption manifest")
    names = [line.strip() for line in text.splitlines() if line.strip() and not line.lstrip().startswith("#")]
    if not names:
        raise AuditError("assumption manifest contains no theorem names")
    if len(names) != len(set(names)):
        raise AuditError("assumption manifest contains duplicate theorem names")
    for name in names:
        if not IDENTIFIER_RE.fullmatch(name):
            raise AuditError(f"invalid theorem name in assumption manifest: {name}")
    return names


def _parse_assumption_body(name: str, lines: list[str]) -> list[str]:
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    if lines == ["Closed under the global context"]:
        return []
    if not lines or lines[0] != "Axioms:":
        got = lines[0] if lines else "<empty>"
        raise AuditError(f"{name}: unrecognized assumption result: {got}")

    dependencies: list[str] = []
    have_entry = False
    for line in lines[1:]:
        if not line.strip():
            continue
        if line[:1].isspace():
            if not have_entry:
                raise AuditError(f"{name}: unrecognized indented dependency output: {line.strip()}")
            continue
        match = re.fullmatch(r"([^\s:]+)\s*:\s*.*", line)
        if not match:
            raise AuditError(f"{name}: unrecognized dependency output: {line}")
        dependency = match.group(1)
        if not IDENTIFIER_RE.fullmatch(dependency):
            raise AuditError(f"{name}: unrecognized dependency name: {dependency}")
        dependencies.append(dependency)
        have_entry = True

    if not dependencies:
        raise AuditError(f"{name}: Axioms heading has no dependency")
    unexpected = [dependency for dependency in dependencies if dependency not in ALLOWED_ASSUMPTIONS]
    if unexpected:
        raise AuditError(f"{name}: unauthorized assumption: {', '.join(unexpected)}")
    return dependencies


def parse_assumption_transcript(text: str, expected: list[str]) -> dict[str, list[str]]:
    if not text.strip():
        raise AuditError("audit log is empty")
    if not expected:
        raise AuditError("expected theorem list is empty")
    if len(expected) != len(set(expected)):
        raise AuditError("expected theorem list contains duplicates")

    blocks: dict[str, list[str]] = {}
    order: list[str] = []
    active_name: str | None = None
    active_lines: list[str] = []
    for line_number, line in enumerate(text.splitlines(), start=1):
        begin = BEGIN_RE.fullmatch(line)
        end = END_RE.fullmatch(line)
        if begin:
            name = begin.group(1)
            if active_name is not None:
                raise AuditError(f"line {line_number}: nested begin marker inside {active_name}")
            if name in blocks:
                raise AuditError(f"line {line_number}: duplicate block for {name}")
            active_name = name
            active_lines = []
            continue
        if end:
            name = end.group(1)
            if active_name is None:
                raise AuditError(f"line {line_number}: end marker without begin for {name}")
            if name != active_name:
                raise AuditError(
                    f"line {line_number}: end marker {name} does not match begin marker {active_name}"
                )
            blocks[name] = list(active_lines)
            order.append(name)
            active_name = None
            active_lines = []
            continue
        if active_name is not None:
            active_lines.append(line)

    if active_name is not None:
        raise AuditError(f"unterminated assumption block for {active_name}")
    if order != expected:
        for index, name in enumerate(expected):
            if index >= len(order) or order[index] != name:
                got = order[index] if index < len(order) else "<missing>"
                raise AuditError(f"expected {name} at block {index + 1}, got {got}")
        raise AuditError(f"unexpected extra assumption blocks: {order[len(expected):]}")

    return {name: _parse_assumption_body(name, blocks[name]) for name in expected}


def _strip_coq_comments_and_strings(text: str, path: pathlib.Path) -> str:
    output = list(text)
    index = 0
    comment_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        if comment_depth:
            if pair == "(*":
                output[index : index + 2] = "  "
                comment_depth += 1
                index += 2
            elif pair == "*)":
                output[index : index + 2] = "  "
                comment_depth -= 1
                index += 2
            else:
                if text[index] != "\n":
                    output[index] = " "
                index += 1
            continue
        if in_string:
            if pair == '""':
                output[index : index + 2] = "  "
                index += 2
            elif text[index] == '"':
                output[index] = " "
                in_string = False
                index += 1
            else:
                if text[index] != "\n":
                    output[index] = " "
                index += 1
            continue
        if pair == "(*":
            output[index : index + 2] = "  "
            comment_depth = 1
            index += 2
        elif text[index] == '"':
            output[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    if comment_depth:
        raise AuditError(f"{path}: unterminated comment")
    if in_string:
        raise AuditError(f"{path}: unterminated string")
    return "".join(output)


def _coq_commands(text: str) -> list[tuple[int, str]]:
    commands: list[tuple[int, str]] = []
    start = 0
    line = 1
    command_line = 1
    for index, character in enumerate(text):
        if character == "\n":
            line += 1
        if character == "." and (index + 1 == len(text) or text[index + 1].isspace()):
            command = text[start : index + 1].strip()
            if command:
                commands.append((command_line, command))
            start = index + 1
            command_line = line
    trailing = text[start:].strip()
    if trailing:
        commands.append((command_line, trailing))
    return commands


def scan_coq_source(text: str, path: pathlib.Path) -> list[str]:
    clean = _strip_coq_comments_and_strings(text, path)
    violations: list[str] = []
    structure: list[str] = []
    unsafe_patterns = (
        (re.compile(r"\bUnset\s+Guard\s+Checking\s*\."), "Unset Guard Checking."),
        (re.compile(r"\bUnset\s+Positivity\s+Checking\s*\."), "Unset Positivity Checking."),
        (re.compile(r"\bUnset\s+Universe\s+Checking\s*\."), "Unset Universe Checking."),
        (re.compile(r"\bSet\s+Type\s+in\s+Type\s*\."), "Set Type in Type."),
    )
    escape_patterns = (
        (re.compile(r"\bAdmitted\s*\."), "Admitted"),
        (re.compile(r"\badmit(?:\s|[.;]|$)"), "admit"),
        (re.compile(r"\bAbort\s*\."), "Abort"),
    )

    for line, command in _coq_commands(clean):
        normalized = " ".join(command.split())
        for pattern, label in unsafe_patterns + escape_patterns:
            if pattern.search(command):
                violations.append(f"{path}:{line}: forbidden {label}")

        if re.match(r"^Module\s+Type\b", normalized):
            structure.append("module-type")
            continue
        if re.match(r"^Module\b", normalized):
            structure.append("module")
            continue
        if re.match(r"^Section\b", normalized):
            structure.append("section")
            continue
        if re.match(r"^End\b", normalized):
            if structure:
                structure.pop()
            continue

        declaration = re.match(r"^(?:(?:Local|Global)\s+)?(Axioms?|Parameters?)\b", normalized)
        inside_module_type = "module-type" in structure
        if declaration and not inside_module_type:
            violations.append(
                f"{path}:{line}: forbidden global {declaration.group(1)} declaration"
            )
    return violations


COQCHK_HEADINGS = {
    "Constants/Inductives relying on type-in-type": "type-in-type",
    "Constants/Inductives relying on unsafe (co)fixpoints": "unsafe (co)fixpoints",
    "Inductives whose positivity is assumed": "positivity assumed",
}


def parse_coqchk_summary(text: str) -> dict[str, list[str]]:
    if text.count("CONTEXT SUMMARY") != 1:
        raise AuditError("coqchk output must contain exactly one CONTEXT SUMMARY")
    lines = text.splitlines()
    sections: dict[str, list[str]] = {}
    index = 0
    while index < len(lines):
        match = re.match(r"^\* ([^:]+):(.*)$", lines[index])
        if not match:
            index += 1
            continue
        heading = match.group(1).strip()
        label = COQCHK_HEADINGS.get(heading)
        if label is None:
            index += 1
            continue
        if label in sections:
            raise AuditError(f"coqchk summary has duplicate {label} section")
        values: list[str] = []
        inline = match.group(2).strip()
        if inline:
            values.append(inline)
        index += 1
        while index < len(lines) and not lines[index].startswith("* "):
            value = lines[index].strip()
            if value:
                values.append(value)
            index += 1
        sections[label] = values

    for label in COQCHK_HEADINGS.values():
        if label not in sections:
            raise AuditError(f"coqchk summary is missing {label} section")
        values = sections[label]
        if values == ["<none>"]:
            sections[label] = []
            continue
        if not values or any(value.startswith("<") for value in values):
            rendered = ", ".join(values) if values else "<empty>"
            raise AuditError(f"coqchk {label} section is malformed: {rendered}")
        raise AuditError(f"coqchk {label} section is nonempty: {', '.join(values)}")
    return sections


def command_assumptions(args: argparse.Namespace) -> None:
    transcript = read_required_text(args.audit_log, "audit log")
    expected = read_manifest(args.manifest)
    parsed = parse_assumption_transcript(transcript, expected)
    dependency_count = sum(len(dependencies) for dependencies in parsed.values())
    print(
        "assumption allowlist: "
        f"{len(parsed)} theorem blocks matched; {dependency_count} dependencies; "
        "only exact Classical_Prop.classic (or closed terms)"
    )


def command_source_policy(args: argparse.Namespace) -> None:
    if not args.sources:
        raise AuditError("source policy received no Coq sources")
    violations: list[str] = []
    for path in args.sources:
        text = read_required_text(path, "Coq source")
        violations.extend(scan_coq_source(text, path))
    if violations:
        raise AuditError("source policy violations:\n" + "\n".join(violations))
    print(
        f"Coq source policy: {len(args.sources)} project-managed tracked .v sources "
        "contain no proof escapes, global axioms/parameters, or unsafe settings"
    )


def command_coqchk(args: argparse.Namespace) -> None:
    summary = read_required_text(args.coqchk_log, "coqchk log")
    parse_coqchk_summary(summary)
    print("coqchk safety: type-in-type, unsafe (co)fixpoints, and positivity assumed are all <none>")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser()
    subparsers = parser.add_subparsers(dest="command", required=True)
    assumptions = subparsers.add_parser("assumptions")
    assumptions.add_argument("audit_log", type=pathlib.Path)
    assumptions.add_argument("manifest", type=pathlib.Path)
    assumptions.set_defaults(func=command_assumptions)
    source_policy = subparsers.add_parser("source-policy")
    source_policy.add_argument("sources", nargs="+", type=pathlib.Path)
    source_policy.set_defaults(func=command_source_policy)
    coqchk = subparsers.add_parser("coqchk")
    coqchk.add_argument("coqchk_log", type=pathlib.Path)
    coqchk.set_defaults(func=command_coqchk)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    try:
        args.func(args)
    except (AuditError, OSError, UnicodeError) as error:
        print(f"Coq audit: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
