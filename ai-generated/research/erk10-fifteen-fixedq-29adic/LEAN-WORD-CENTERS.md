# Two complete native word rows at the repeated center

On the physical schedule \(0,a,b,c,c,26,e,f,6,h,15\), the
Lean theorem `RKResearch.Certified.ERK10FixedQ29Adic.Physical.actualK_center`
checks all eight coordinates of the exact chronological \(K\)-action
on both copies of \(c\) (indices 3 and 4, counting from zero).
The inputs are any commutative ring and a local residue homomorphism
to \(\mathbb F_{29}\), with the displayed decic and quadratic root
relations and residues. No characteristic-29 assumption on the ring
is made.

The actual normalized first-center mass and unit null-direction gain
are paid separately. The first center's coefficient on its own
nonpreceding donor is exactly zero; the second center can use that
same donor. In each case the three scaled physical donors give the
five positive coordinates. `actual_G_earliest` and `actual_Z_earliest`
supply the terminal-observer zero inputs, and the paid chronological
minor supplies the actual constant coordinate and uniqueness.
The general five-coordinate center readouts and chronological uniqueness
are in `ERK10FixedQ29AdicCenterReadoutVerified`.

The exact theorem bodies passed Lean 4.36 in one warm server document,
and use only standard axioms. From the root of the Lean package,
the standalone import DAG is `WordB`, `CenterReadoutVerified`,
then `WordCenters` (all with `ERK10FixedQ29Adic` namespace prefix);
the build is `lake build RKCert.ReviewedNative.ERK10FixedQ29AdicWordCenters`.
This receipt certifies the bundled bodies, not a separate standalone
build. The result is a physical exact-word proof, not yet a
full rooted-order proof for the lifted tableau.
