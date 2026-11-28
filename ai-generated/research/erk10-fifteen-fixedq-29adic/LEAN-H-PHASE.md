# Exact late h-phase condition in Lean

This verifies the first nonlinear closure equation for the
[unbounded fixed-q 29-adic ERK10 construction](README.md). It
uses the literal decic root \(c\), the actual uncancelled
symmetric head solve, the native [origin identity](LEAN-ORIGIN.md),
and the original \(f,g,h\) phase quantities. It is valid in
any commutative ring with a unit-reflecting residue map to
\(\mathbb F_{29}\), assuming \(P(c)=0\) and residue \(c=2\).
In particular the [native inverse-limit model](LEAN-LIMIT.md)
has such a point.

In namespace **RKResearch.Certified.ERK10FixedQ29Adic.Nonlinear**:

- **exactS** and **exactQ** connect the normalized degree-ten
  coordinates to the true head sum and product, including
  the original \(h,f,e\) formulas and the native consequence
  \(Q_\ell=-Q_c\) of origin vanishing.
- **actualD7_factor** and **coeff_actualD7** connect the polynomial
  \(D_7=(Y^2-s_hY+p_h)(Y-d)(Y-e)(Y-f)(Y-g)(Y-h)\) to the coefficient
  recurrence. The verified coefficients of the cardinal polynomial
  are the original divided-difference averages
  \(\widetilde\mu_i=\sum_{j>i}(D_7)_j I[x(x-1)(x-c)x^{j-1-i}]\).
- **exact_phase_alignment** proves, for the actual
  \(\phi(z)=-\widetilde\mu(z)V_c(z)/(zC_\nu)\), the identity
  \[
    (\phi(h)-\phi(f))(6-f)
      =(\phi(6)-\phi(f))(h-f).
  \]
- **exact_h_phase** uses the actual paid unit \(6-f\) to prove
  that the affine \(q_1\) formed from the two literal \(f,6\)
  phase values has \(q_1(h)=\phi(h)\).

The untrusted generator chooses degree-below-ten numerator vectors
and integer denominators not divisible by 29. The kernel checks
each actual formula by signed packed integer congruence at the
decic, with the proved common-denominator and coefficient bounds,
as well as the ambient unit guards. No computer algebra system
axiom or unchecked compiler equality is used. The
[complete axiom audit](lean-h-phase-4.36-audit.txt) records only
standard axioms on Lean/Mathlib 4.36.0. No full build on the other
Lean releases is claimed.

This packet alone makes no assertion about the seven remainder
proportionalities, final physical pivot/decoder reconstruction,
or actual Runge–Kutta rooted order in the 29-adic ring.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicPhaseExact:olean

From this research directory, regenerate the two data files in
an existing empty directory:

    python3 -B generate_phase.py --emit /tmp/erk10-29-h-phase-regen

Verify the manifest from the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/lean-h-phase-sha256.txt
