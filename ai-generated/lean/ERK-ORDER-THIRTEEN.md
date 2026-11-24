# Explicit order 13 over ordered fields: final proof route

This is a formalization of the existing ordered-field lower bound, not an
improvement of the existing mathematical threshold. The formal target is
`RKCert.explicit_order13_ge20_orderedField`, together with its exact Fin19
exclusion `RKCert.explicit_order13_not_fin19`. No sign, nonzero-weight,
interior-node, or distinct-stage-clock assumption is imposed. The endpoint
does not claim the same conclusion over unordered characteristic-zero
fields or arbitrary characteristic-zero rings.

## Forward chart dispatch

The prior immutable full-odd and marked-structural packets reduce a
hypothetical order-13 explicit Fin19 witness to a genuine marked-prefix
chart. If its first backward defect is nonzero, the exact feature collapse
and ordinary reverse chronology in the full-odd packet already contradict
the witness. In the marked case the endpoint coordinate is explicitly
accounted for; ordinary and marked grade payments are never substituted
for each other.

Rank two, including genuine leakage and delayed terminal entry, reduces
to an early literal pure head using the marked-structural packet. If the
ordinary fourth defect rank is four and the head has rank at least three,
it is cleaned on the true invariant mask core. The whole affordable
square-power run is covered by three successive actual grade-eight
shifts. The numerically distinct head-site bound makes the mesh
factorization literal. At alias width five, the top coefficient in the
mesh relation cannot disappear into the separated sixth grade. Thus the
head factor has the exact clean profile required by the causal masks.

The low fourth-defect rank is three. In head rank three, the actual image
of the quadratic defect is a paid affine level-three head. Otherwise its
ordinary two-dimensional source would give an invariant third-grade
space or an impossible invariant quadratic line. In head rank four with
the quadratic defect outside the core, that defect itself is a paid
affine level-two head. A joint `(clock,multiplier)` block whose multiplier
disagrees with P contributes only to the invariant core. On every
surviving head clock the affine head equality and the mesh equality give
a scalar multiple of `G=P Q` modulo the core; distinct effective clocks
make this literal.

For head rank four with the quadratic defect inside the core, the marked
second grade is exactly the core, and one uses the actual level-three
image of the quadratic defect. For rank five, the core is just the
terminal line and the multiplier is the level-two quadratic defect. The
grade-eight shift purification is reused; in rank five, its result
descends back to grade seven by polynomial-band separation rather than
silently spending one more grade. The mixed representation gives the
literal identity `G L=P Q` with `L` nonzero of degree at most one. If
`L` divides `Q`, cancel it. If not, its unique root satisfies
`Q(t) != 0`, so `L` divides `P` instead; the quotient represents the
head even at `t`, by the original physical mesh equation. This bypasses
all assumptions about simplicity at the mandatory zero of `x·pencil`.

## One scalar test for every clean or joint unaliased factor

Start with two actual chronological detecting masks. They detect distinct
nonzero omitted clocks u and v. Neither the sign of a weight nor
the numerical order of the clocks is used. If the original head factor
contains the zero root, strip one factor of x and use mask 1 instead of x.
The remaining factor R divides `D₆ + θ D₅`. At the already detected
clocks, factor off `(x-u)(x-v)` and take the remaining literal
complementary quotient L to fill R to a quartic F. The positive exact
Jacobi Wronskian guarantees the cofactor is nonzero at the two actual
clocks. No existence or splitting of any other roots is assumed. Multiply
both chronological masks by L; no preceding match is changed, and the
primitive budgets still fit genuine grades six and seven. On a joint
block, the accepted earlier prefix is kept via a matching core vector;
its image is an actual grade-six term, so it cannot affect the grade-seven
leakage coefficient.

The first paid response has zero polynomial leakage. Both high responses
share one scalar τ on the exact `x·D₅` line, since their masks differ by a
multiple of the first test. This gives exactly the three moment equations
consumed by `Pencil13.physical_pair_to_integer`.

The alias case has a separate shorter fixed-factor gate. After scaling
roots by 132 its grid is monic integral. The split prime 181 checks the
first weighted primitive for **every** degree-at-most-three factor of
`x·D₅`, including the zero factor root, at every nonzero grid endpoint.
Only the integral monic scalar factors are reduced; not the tableau.

## Exact scalar arithmetic and reuse

For the free Jacobi pencil, apply two genuine synthetic divisions to
`D₅(u)D₆(x)-D₆(u)D₅(x)`. The three resulting integer bivariate
equations are the omitted-root equation, the first primitive, and the
pair of high primitives with τ eliminated. Nine checked integer
pseudo-remainder identities give the two univariate eliminants. Only
nonzero powers of the already nonzero u and D₅(u), nonzero integer
constants, and two polynomial contents whose nonvanishing has itself
been certified are canceled. The eliminant from the first chain has
degree 40. The two auxiliary contents have degrees 22 and 44; the
second chain’s final eliminant has degree 121. For each pair involving the first
eliminant the chosen prime 17 preserves both full degrees and the
kernel checks an exact Bézout identity. The generic Mathlib-resultant
transfer excludes common zeros over every characteristic-zero field.
No specialization of a free tableau or a free pencil establishes
nonvanishing. SymPy only generates candidate data; every identity is
rechecked in Lean without native/reflection axioms.

Reused dependencies include the published rooted-tree order API;
`OneEscape.chain` and its actual graded closures; existing
`OrderTwelveChronologicalContrast` block localization; the exact finite
midpoint flags; `OrderedGram`; and the canonical
`IntegralFactorGate`, `FactorPrimitiveScale`, and `LobattoFactorTables`
for the alias. The generic coefficient-list operations and degree
preserving resultant transfer are reused from the separate ERK
good-prime and DIRK resultant work. No alternative determinant,
resultant, or polynomial evaluation semantics enter the proof.

The final arbitrary-stage statement appends zero-weight, zero-row and
zero-column suffix stages. The proof matches every rooted-tree output
weight by structural induction; it is not limited to the linear chain.

## Pinned replay

Use Lean 4.36.0 and its pinned Mathlib 4.36.0. This delta is additional
to the immutable p13 full-odd checkpoint (SHA-256
`e6c57376df60a7e215e483dfe6cb19ae915d20f26d360c67ad9b5a54b9760109`)
and marked-structural checkpoint (SHA-256
`3662984550423b2b249bb60710010523ef745bc1ad68aeae259985dc1403ed7c`).
The separate paired-core recovery ZIP is not a third prerequisite:
all of its new leaves are included here.

Use the canonical shared modules byte-for-byte when already present.
The four listed in the shared dependency ledger are included as exact
source snapshots only for integration into a tree that lacks them.
No published baseline source or umbrella module is changed by the delta.
In a pinned checkout run:

```sh
lake build RKCert.ExplicitOrderThirteen
lake env lean AuditERK13Ordered.lean
```

Actual pinned leaf checks completed successfully. All 13 declarations in
the audit have exactly the standard axiom set
`propext, Classical.choice, Quot.sound`. The checked arbitrary-stage
statement is:

```lean
theorem RKCert.explicit_order13_ge20_orderedField
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {s : ℕ} {A : Fin s → Fin s → K} {b : Fin s → K}
    (ha : RKCert.StrictLower A)
    (ho : RKCert.HasTreeOrderAtLeast A b 13) : 20 ≤ s
```
