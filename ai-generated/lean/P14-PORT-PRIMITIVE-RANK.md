# One fixed determinant for every small marked order-14 Lobatto factor

Let K be any characteristic-zero field, G(X)=X L'₇(X) for the shifted Legendre polynomial normalized at one, D=(X−1)G, and J the polynomial primitive with zero constant term. Suppose Z∈K[X] is a monic divisor of D with deg Z≤5, u≠0 and Z(u)=0, and deg Q≤4. If

    J(X^k ZQ)(1)=0     for k=0,1,2,3,
    J(X Q)(u)=J(X² Q)(u)=0,

then Q=0. In particular the same result holds with the original five global conditions k=0,…,4; k=4 is unnecessary. The marked root may be one, and Z may contain the factor X. There is no order, algebraic-closure, real-root, nonzero-weight or tableau assumption. The public theorems are RKCert.PortRank.lobatto7_marked_factor_quartic (four global equations) and RKCert.PortRank.lobatto7_marked_factor_quartic_five (the five-equation interface used by the physical DIRK reduction).

This is the scalar obstruction used after reduction from a physical tableau. It is **not by itself an unconditional order-14 DIRK stage-count theorem**.

## Clear denominators and isolate a square test

Take c=429, L=360360, x=cu, z=deg Z, W(Y)=c^z Z(Y/c) and w_j=Q_j c^(4−j), 0≤j≤4. The full grid in integral scaled coordinates is F(Y)=Y H(Y), where H(Y)=(Y−429)H₇(Y) and H₇ is the monic integer scaling of L'₇. The already checked native Legendre coefficient identity gives D.scaleRoots(c)=24024 F. Thus W is monic, divides F, has degree ≤5, satisfies W(x)=0, and H(x)=0 since x≠0.

For the five columns j=0,…,4 set

    G_k[j] = Σ_{i=0}^5 [L/(k+i+j+1)] W_i c^(k+i+j+1),
    B_k[j] = [L/(k+j+1)] x^(k+j+1).

All bracketed quotients are integers. Taking the dot product with (w_j) gives respectively L c^(z+4+k+1) J(X^k ZQ)(1) and L c^(4+k+1) J(X^k Q)(u). This is proved coefficientwise from the actual project's primitive, not by numerical quadrature. Form the 5×5 square matrix with rows

    G₀−G₁, G₂, G₃, B₁, B₂.

The six stipulated moments annihilate w. We prove that its determinant is nonzero. In particular, no choice among the 21 possible row minors is needed, and no fifth global equation is used.

## Legitimate reduction and the complete table

Assume the determinant were zero. Both the coefficients of the monic factor W and those of its monic cofactor are integral over ℤ, since their product is the monic integer polynomial F. The marked root x is also integral as a root of monic H. Pass to the integral closure of ℤ in K and reduce at a maximal ideal above 1361. This preserves the monic factorization, degree upper bound, two root equations, and the determinant (the entries are integer polynomials in the scaled coefficients and marked endpoint). The nonzero-root constraint is retained by the independent H equation, not by reducing an inequation. **Neither Q nor an RK tableau is specialized**: a kernel vector may have nonintegral entries, and its nonzero leading coefficient need not be preserved by a residue map. All we reduce is the determinant of the constraint matrix.

Over the field of order 1361 the eight scaled F roots are 0, 51, 378, 429, 478, 609, 1181 and 1312. The H roots are precisely the seven nonzero ones. Exact polynomial factorization is verified in Lean. Every monic divisor over any extension of this residue field is a product over a sublist, even if the coefficient field is larger; the marked root belongs to the chosen sublist and to H. Enumerating all factors of degree at most five and their nonzero marked roots gives precisely

    7 × (1 + 7 + 21 + 35 + 35) = 693

cases. The same displayed determinant is nonzero in all of them. Lean checks the finite arithmetic by the ordinary kernel, using an executable recurrence proved equal to Mathlib's determinant by Laplace expansion. The cases are grouped into small, independently checked blocks to bound verifier memory. The external Python replay uses independent finite-field Gaussian elimination and has no role in the proof. Nonvanishing in the prime field persists in every residue-field extension, contradicting any zero specialized determinant.

Finally if Q≠0, the coordinate j=deg Q of w is nonzero in K. The checked native matrix product says Mw=0, so Mathlib's adjugate lemma forces det M=0. This contradicts the nonvanishing over K and proves Q=0.

## Reuse and scope

The project uses Mathlib's integral-closure factor theorem, maximal-ideal lying-over, prime-field embedding, polynomial scaleRoots, RingHom.map_det, Matrix.det_succ_row_zero and Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors. The executable table and the cleared moment entries are specific to this physical port test. The new general marked-factor specialization adapter is independent of the eight-port grid and imposes no order or realness hypotheses.
