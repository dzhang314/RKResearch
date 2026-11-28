# Arbitrary late-row retaps cannot shorten this fixed-clock ERK10 chart

These obstructions concern deleting the terminal row from the
[17-stage half-port family](../erk10-seventeen-half-port-family/README.md)
without changing any surviving clock. They do not exclude a different
sixteen-stage tableau.

- Keep the first thirteen physical rows, but allow **arbitrary** retaps
  of the three surviving late rows, including their high-high blocks.
  Allow every output weight to change. The resulting 16 rows cannot
  give order ten in any nontrivial commutative ring paying \(10!\).
- In characteristic eleven the first **twelve** rows can be frozen
  instead. The remaining **four** survivors may be retapped arbitrarily,
  and all weights may change, with the same impossibility. Consequently
  this four-row shortening also fails over \(\mathbb Z[1/210]\), or over
  any paid ring in which 11 is not a unit: reduce modulo a maximal ideal
  containing 11. The latter reduction is mathematical, separate from
  the native characteristic-eleven endpoint.

## Mixed moments

For nonnegative \(j,k\) with \(j+k+2\le 10\), order ten fixes the
weighted sum of the stage vector
\(\boldsymbol c^{\odot j}\odot A\boldsymbol c^{\odot k}\).
The tree is a root with \(j\) leaf children and one \((k+1)\)-vertex
bush child. Its factorial is \((j+k+2)(k+1)\), a unit. The ten ordinary
bush moments also fix the aggregate output mass at each clock:
cardinal polynomials on the ten sites \(j/6\), \(-3\le j\le6\),
have paid denominators since all node gaps are units.

For the first result, put \(P(X)=(6X+1)(6X+2)(6X+3)\) and let
\[
  Q(X,Z)=
  -94 X^2Z+(34-9X+117X^2-108X^3)Z^2-75Z^4+36Z^5.
\]
The row read is \(S_i=\sum_j a_{ij}P(c_i)Q(c_i,c_j)\).
All monomials in this mixed moment have combined degree at most
eight. The mask kills the three arbitrary surviving late rows,
at clocks \(-1/6,-1/3,-1/2\). On every other survivor the read
depends only on its clock, independently of the reference's two
affine parameters. The old clock-one row read differs from the
deleted row's read; their difference times the deleted mass is
\(-96/5\), a paid unit, and cannot be restored by reweighting the
survivors. To see this directly, subtract the weighted sum of the
surviving read extended as a function of the clock. That function
has the same integral for the original and candidate weights,
leaving only the deleted nonzero read.

For the second result use
\[
  P(X)=(6X-2)(6X+2)(6X+3),\qquad
  Q(X,Z)=(16+72X-54X^3)Z^2-75Z^4+36Z^5.
\]
This masks the mutable clocks \(1/3,-1/3,-1/2\).
The unmasked fourth mutable clock \(-1/6\) occurs only once,
so its output weight remains \(33/700=0\) in characteristic 11.
It contributes nothing under either tableau. The same-clock
reads on the other survivors are again identical and unaffected
by the affine parameters; the deleted discrepancy is now
\(-384/35\), a paid unit.

## Native and numeric scope

`ERK10FrozenTailMixedMoments` proves the ordinary rooted invariant
for arbitrary integer mixed-polynomial sums of admissible degrees
and proves aggregate-clock integration equality.
`ERK10FrozenTailCompensation.no_three_tail_retap_literal` and
`.no_four_tail_retap_char11_literal` consume the actual explicit
coefficient fixture, with its checked reference order. Their
family versions `.no_three_tail_retap` and
`.no_four_tail_retap_char11` compute both actual affine directions
but take order ten of that family member as input; all noncentral
orders are known from the separate exact tensor-grid replay.
The formal candidate is padded with any last zero-output row of
clock one, which does not affect the preceding rows of a strictly
explicit candidate. All exact mixed loads and comparison reads are
scaled by \(6^5\) in Lean. The proof does not require any bounds on
the new coefficients or retention of any low-grade stage profiles.

Lean/Mathlib 4.36.0 was checked with standard axioms only.

    python3 -B audit.py
    sha256sum -c sha256.txt
    sha256sum -c lean-sha256.txt
    cd ../../lean
    lake build +RKCert.ReviewedNative.ERK10FrozenTailMixedMoments:olean \
      +RKCert.ReviewedNative.ERK10FrozenTailCompensation:olean
