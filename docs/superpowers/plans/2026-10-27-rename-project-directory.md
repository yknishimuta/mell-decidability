# Project Directory Rename Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Align active repository URLs and the local checkout directory with `mell-decidability` without changing mathematical sources, package identity, dependencies, or historical records.

**Architecture:** Update only tracked, current public metadata before moving the checkout. Commit those changes independently, then move the normal checkout at the filesystem level, repair linked-worktree and local-opam path metadata, regenerate path-bearing build products, and run the complete verification suite from the new path.

**Tech Stack:** Git, opam 2.x local switch, Coq 8.20.1, OCaml 4.14.2, GNU Make.

**Spec:** User instruction “MELL形式化リポジトリのディレクトリ名統一” (2026-10-27).

## Global Constraints

- Preserve all pre-existing modified and untracked files, including the user-edited `README.md`.
- Do not alter Rocq logical module names, theorem statements, proofs, algorithms, opam package name, dependency versions, vendored code, licenses, or historical audit facts.
- Do not use `git clean`, destructive reset/checkout, `git add -A`, push, merge, tag, or release operations.
- Stage only task-owned tracked files explicitly.
- The filesystem rename is operational state and is not represented as a Git file change.

## Review Focus

- Active GitHub URLs must use `yknishimuta/mell-decidability`, while historical audit evidence remains unchanged.
- The user-owned README diff and all pre-existing untracked files must remain byte-for-byte preserved.
- Linked worktrees must remain registered and repairable after the main checkout moves.
- The repository-local opam switch must resolve from the new path without deleting or rebuilding the existing switch.
- Path-bearing generated makefiles must be regenerated before the post-rename build.

---

### Task 1: Update current tracked metadata

**Files:**
- Modify: `mell-formalization.opam`
- Modify: `mell-formalization.opam.locked`
- Create: `docs/superpowers/plans/2026-10-27-rename-project-directory.md`

**Interfaces:**
- Consumes: the confirmed GitHub repository URL `https://github.com/yknishimuta/mell-decidability`.
- Produces: current public metadata with no active underscore-form repository URL.

- [ ] Record the failing `git grep` showing the two manifests still use the old URL.
- [ ] Replace only the `homepage` and `bug-reports` URLs in both manifests.
- [ ] Run `opam lint` for both manifests and classify the historical audit occurrence as intentionally unchanged.
- [ ] Verify the README diff and pre-existing untracked files are not staged.
- [ ] Commit only the two manifests and this plan.

### Task 2: Move and repair local repository state

**Files:**
- Operational move: `/Users/nishimuta/Downloads/mell_decidability` to `/Users/nishimuta/Downloads/mell-decidability`
- Regenerate, do not commit: `Makefile.coq`, `Makefile.coq.conf`, `Makefile.conf` as applicable
- Local metadata only: Git remote, linked-worktree administration, opam switch registration/environment

**Interfaces:**
- Consumes: committed tracked metadata from Task 1 and the existing `_opam` prefix.
- Produces: a usable checkout and local toolchain rooted at the hyphenated path.

- [ ] Confirm the destination does not exist and record linked-worktree/opam metadata before moving.
- [ ] Update `origin` to the hyphenated GitHub URL.
- [ ] Move the normal checkout from its parent directory.
- [ ] Repair linked-worktree administrative paths and verify `git worktree list --porcelain`.
- [ ] Re-register or repair the moved local opam switch without deleting or rebuilding it; verify `opam switch show` and `opam exec --switch . -- coqc --version`.
- [ ] Regenerate path-bearing makefiles and prove no active generated path still names the old root.

### Task 3: Verify the renamed checkout

**Files:**
- No source modifications expected.

**Interfaces:**
- Consumes: the repaired checkout and local switch from Task 2.
- Produces: verification evidence for the unchanged formalization under the new path.

- [ ] Run `make Makefile.coq`.
- [ ] Run `opam exec --switch . -- make -f Makefile.coq -j2`.
- [ ] Run `opam exec --switch . -- make -f Makefile.coq validate`.
- [ ] Run `opam exec --switch . -- make check-final`.
- [ ] Run `opam exec --switch . -- make audit-final`.
- [ ] Run `opam exec --switch . -- make extract-final`.
- [ ] Run `opam exec --switch . -- make check-runtime-mell` and require 22/22 cases.
- [ ] Run final Git status/diff checks and classify every remaining old-name occurrence.
