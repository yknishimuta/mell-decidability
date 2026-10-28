# T10-C2-G1-Hilbert audit — integer points of a rational V-cone

## Baseline and scope

- Baseline: `962c15a7762478bf4bdf6712d415a07b62c920b7`.
- Contract: `docs/superpowers/plans/2026-10-20-t10-c2-g1-vcone-implementation-plan.md`.
- Contract SHA-256: `f76fd1eb881f078500b779227bd8298a27284887a2736371261f15b227714ae5`.
- Scope: G1-Hilbert only. G1-Pullback, G1-Main, and closed
  linearization remain untouched.

The checked-in plan is preserved byte-for-byte at its required hash.  Its
section 4 still contains the historical G1-I start instruction and baseline
`413803be...`.  The task-specific directive dated 2026-10-20 explicitly says
that G1-I is complete, replaces that old section, fixes the G1-Hilbert baseline
at `962c15a7762478bf4bdf6712d415a07b62c920b7`, and authorizes only the theorem
implemented here.  Thus the old section is retained as source history, not
treated as the active implementation instruction.

## Public theorems

With implicit arguments printed, the coefficient normal form is:

    qcone_generated_aligned_coefficients
      : forall (k : nat) (W : list (QVec k)) (x : QVec k),
          @qcone_generated k W x <->
          exists coefficients : list Q,
            @length Q coefficients = @length (QVec k) W /\
            @List.Forall Q (fun q : Q => 0 <= q) coefficients /\
            @QVecEq k x (@qlinear_combination k W coefficients)

The completed G1-Hilbert theorem is:

    integer_points_vcone_finitely_generated
      : forall (k : nat) (W : list (QVec k)),
          @FinitelyGeneratedPeriodic k
            (fun z : ZVec k =>
              @qcone_generated k W (@zvec_to_qvec k z))

The first theorem is genuinely bidirectional.  Its forward proof inducts on
`QConeCombination`; `qlinear_add_at` selects one witnessed occurrence of an
`In` generator and never compares vectors.  Therefore duplicate generators
remain distinct coefficient positions and no decidable equality on `QVec` is
assumed.

## Mathematical bridge

1. `integerize_vcone` clears a positive denominator separately for every
   rational generator and proves equality of the generated rational cones in
   both directions.
2. `qfloor_fraction_decompose` writes each nonnegative coefficient as its
   natural integer floor plus a fraction in `[0,1)`.  The aligned coefficient
   theorem ensures that floors and fractions stay attached to the correct
   generator occurrences.
3. `integer_remainder_correct` subtracts the integral floor combination from
   an integer point.  The result is still an integer vector and its rational
   image is the fractional combination.
4. `integer_remainder_coordinate_bound` bounds every remainder coordinate by
   the sum of the absolute values of the corresponding integer-generator
   coordinates.  Negative coordinates and lineality require no pointedness
   assumption.
5. `zvec_box` enumerates the finite product of the coordinate intervals.
   `finite_sublist` uses proposition-level classical case analysis to retain
   exactly the box points lying in the cone.  No membership decision procedure
   or extracted oracle is introduced.
6. The integer generators and the finite remainder list are concatenated.
   Soundness follows from cone closure; completeness adds the generated floor
   part and the selected remainder.  Finally `integerize_vcone` transports the
   result back to the original rational generators.

The example `W = [2]` explicitly proves that the integer point `1` belongs to
the cone through coefficient `1/2`; hence the integerized input generator alone
is not treated as a sufficient monoid basis.  Further regressions cover
dimension zero, the empty list, a zero generator, a negative generator,
non-integral generators, opposite generators, and lineality.

## Trust boundary

`Print Assumptions qcone_generated_aligned_coefficients` reports:

    Closed under the global context

`Print Assumptions integer_points_vcone_finitely_generated` reports exactly:

    Axioms:
    Classical_Prop.classic : forall P : Prop, P \/ ~ P

The dependency is introduced only by `finite_sublist`, which selects the
finite subset of an already enumerated box satisfying cone membership.  The
proof does not depend on `ClassicalEpsilon.constructive_indefinite_description`,
UIP/K, `Eqdep.Eq_rect_eq.eq_rect_eq`, functional extensionality, or a new
axiom/oracle.

## Verification

- RED: before `LatticeGordanV.v` existed, compiling
  `LatticeGordanVExamples.v` failed with the expected missing-module error.
- GREEN: `opam exec --switch . -- make audit-t10-c2-g1-hilbert` exited 0.
  It compiled the implementation and boundary examples, replayed the complete
  public types and assumptions, rejected forbidden dependencies and
  declarations, and ran `coqchk -silent` on both modules.
- Full regression: `opam exec --switch . -- make -f Makefile.coq -j2`
  exited 0 (`Nothing to be done for real-all`).
- The task-file diff passes whitespace validation.  A repository-wide
  `git diff --check` still reports pre-existing trailing whitespace in the
  protected, modified audit logs; those files were not changed by this task.
- Independent read-only review replayed both modules and `coqchk`, inspected
  coefficient alignment, integerization, bounded remainders, finite-box
  completeness, and the trust boundary, and reported no Critical, Important,
  or Minor finding.  Its initial documentation concern about the historical
  G1-I paragraph was resolved by the explicit supersession record above; the
  required plan hash remains unchanged.
