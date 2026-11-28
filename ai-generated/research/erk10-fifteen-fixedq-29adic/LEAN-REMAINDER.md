# Exact nonlinear remainder identities at the same 29-adic point

This extends the checked [late h-phase](LEAN-H-PHASE.md) and
[native scalar inverse limit](LEAN-LIMIT.md). No full tableau
or Runge–Kutta order claim is made by this extension.

Use the previously certified \(D_7,\widetilde\mu,V_c\), and set
\(\Delta=6-f,\ C_\nu=(1-15)V_c(15)\).
Write \(q_1\) for the affine polynomial built from the actual
two phase values at \(f,6\), and
\[
 q_n=\Delta\phi(f)+(\phi(6)-\phi(f))(Y-f)=\Delta q_1,\qquad
 T_4=(Y-15)(Y-f)(Y-6)(Y-h).
\]
The verified \(h\)-phase is \(q_1(h)=\phi(h)\).

The theorem **exact_homogeneous_divisibility** proves
\[
 \widetilde\mu\,[\Delta(Y-1)V_c+\Gamma T_4]
       - C_\nu\,Y(1-Y)q_n = D_7 Q .
\]
Here \(\Gamma\) and the four coefficients of \(Q\) are paid
degree-below-ten rational coordinates at the literal decic.
The kernel verifies each of the eleven possible coefficients
using signed packed integer congruence, and proves both sides
have degree at most ten. The formula is an actual polynomial
identity, not an inference from reductions modulo powers of 29.

Take \(U_0=(Y-1)V_c/C_\nu\) and the actual monic remainders
\[
 E=(\widetilde\mu U_0-Y(1-Y)q_1)\bmod D_7,\qquad
 B=(\widetilde\mu T_4)\bmod D_7 .
\]
The native consumer proves
\(\Delta C_\nu E+\Gamma B=0\) and therefore
\(E_i B_0=B_iE_0\) for every index \(i\). It uses the already
paid \(\Delta\) and \(C_\nu\), not a guessed determinant.
**ResiduePivot.residueB0** computes that the actual constant
coefficient \(B_0\) maps to \(4\) in \(\mathbb F_{29}\).
Its finite residue quotient is \([11,4,20,22]\) and remainder
\([4,11,23,1,25,10,6]\) in ascending order. The checked
**ResiduePivot.paidB0** proves the pivot is a unit.

Thus the actual quotient
\(\sigma=-E_0/B_0\) gives a verified \(U=U_0+\sigma T_4\)
of degree at most four, with \(U(15)=-1\) and
\(\widetilde\mu U\equiv Y(1-Y)q_1\pmod{D_7}\).
The combined **exact_nonlinear_limit** theorem verifies that
this quartic, the \(h\)-phase, the decic and true origin root,
and both head roots and tail residues all hold at one point
of the infinite 29-adic inverse-limit ring. It does not claim
a Lean identification of that ring with the analytic PadicInt.

The remaining work is the physical bridge: the exact weighted
and marked \(\boldsymbol u,\boldsymbol\eta\) pairings and host
cofactor readout, the actual repeated-pair and triangular decoder
pivots in the reconstructed literal \(A,\boldsymbol b\), and then
the full rooted-order and next-tree unit proof. The existing
[unbounded mathematical full-order result](README.md) is separate.

The [axiom audit](lean-remainder-4.36-audit.txt) records the
Lean/Mathlib 4.36.0 kernel checks with standard axioms only.
No full dependency build on other Lean versions is claimed.

From the repository root:

    cd ai-generated/lean
    lake build +RKCert.ReviewedNative.ERK10FixedQ29AdicNonlinearLimit:olean

From this research directory, regenerate the three coordinate
data modules in an existing empty directory:

    python3 -B generate_remainder.py --remainder --emit /tmp/erk10-29-rem-regen

Verify this extension from the repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-fixedq-29adic/lean-remainder-sha256.txt
