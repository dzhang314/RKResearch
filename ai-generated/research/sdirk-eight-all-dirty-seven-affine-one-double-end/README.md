# The affine seven-clock graph cannot have a doubled endpoint

Assume a strict ten-stage SDIRK tableau over a characteristic-zero field has ordinary order at least eight, all ten literal quadratic residuals nonzero, and exactly seven distinct clock labels. Use the [affine singleton-residual graph](../sdirk-eight-all-dirty-seven-affine-openers/README.md), with type S for a singleton clock and type D for a doubled clock. All signed weights are allowed. If it had just one singleton endpoint, the preceding [arithmetic exclusion](../sdirk-eight-all-dirty-seven-affine-terminal-arithmetic/README.md) and the earlier opener restrictions force the orientation starting at the singleton to be **S,D,D**. This packet rejects that last shape. Thus both endpoint clocks must be singleton. At least one endpoint still needs a literal S,D,D prefix by the [two-singleton restriction](../sdirk-eight-all-dirty-seven-affine-two-singletons/README.md). The affine graph in those remaining chronologies and the unconditional stage interval remain open.

## The complete S,D,D mesh projection

Scale to common diagonal one and let the interval length be \(\ell=1/\gamma\). In this packet use the dimensionless centered clock coordinate \(v=(2x-\ell)/\ell\). Denote the terminal coordinate by \(e=(\ell-2)/\ell\), and the unique affine graph-zero coordinate by \(s\). Then \(e\ne0,1\), the first clock is at \(-e\), and \(K(e,s;1)=0\); \(K\) is the exact divided difference from the affine opener packet. Both \(J_3(s)\) and \(J_4(s)\) are nonzero. The leading coefficient of the D-clock cubic in \(v\) is \(L=-35J_3(s)\ne0\); let \(M\) be the negative of its quadratic coefficient, so its sum of roots is \(M/L\). The forward first label is S, so \(K(-e,s;1)\ne0\); the root of \(R\) cannot be there because that stage has residue \(1/2\).

Write \(\xi,\eta\) for the actual dimensionless second and third clocks. In arithmetic the literal clock equation is \(\eta=2\xi+e\); in star it is \(\eta=2-4e-\xi\). The first three rows have distinct labels. Their D clocks may coincide with the terminal D label, but cannot coincide with each other. Together with \(K(e,s;1)=0\) the following list is exhaustive:

| Literal forward case | Second polynomial test | Nonguard factors projected in \(s\), with their degrees |
|---|---|---|
| Arithmetic, three distinct D labels including terminal | \(K((M/L-2e)/3,s;1)=0\) by the cubic root sum | 8, 18 |
| Star, three distinct D labels including terminal | \(M=(2-3e)L\) by the cubic root sum | 9 |
| Arithmetic, second equals terminal | \(K(3e,s;1)=0\) | 12 |
| Arithmetic, third equals terminal | \(K(0,s;1)=0\) | None |
| Star, either early D equals terminal | \(K(2-5e,s;1)=0\) | 3, 12 |

The projected denominators in the first row come from the nonzero leading coefficient \(L\). The only other resultant factors are \(s\) and \(5s^2-3\), excluded by \(J_3(s)\ne0\). In particular the fourth row has only the \(5s^2-3\) factor; it also follows immediately from \(K(0,s;1)=3(5s^2-3)\). All terminal fibres in \(e\) are linear in the respective exact projected fields. The arithmetic distinct degree-eight factor instead reconstructs a repeated terminal/second label, so does not belong to the distinct case. The degree-three star repeat reconstructs both early D labels equal, contradicting the literal distinction of rows 2 and 3.

In the star distinct degree-nine field the two remaining D labels form an irreducible quadratic over that field, and both orientations are kept. In the other surviving fields, the needed labels either are explicitly reconstructed or follow from the sum of the remaining roots. The resulting list contains **six forward placements**: one arithmetic distinct in degree 18; two star distinct in the degree-18 quadratic tower over degree 9; one arithmetic terminal/second repeat in degree 12; and two star terminal repeats in degree 12. The code verifies both scalar equations and every valid forward guard, including \(\ell=2/(1-e)\ne0\), noncollision with the first label, natural simple roots, and the actual tap phase with both D residuals nonzero and not on \(R\). If \(s=e\), the terminal D clock would be the graph zero, not automatically impossible; the construction uses polynomial \(K\) and does not divide by \(s-e\).

## No reverse phase can fit any of the six meshes

In each exact field the two actual forward D pairs are known, as is the first singleton. Recover the original affine graph in uncentered \(x\) by setting
\[
 a=-(e+s)/(1-e),\qquad b=(s-e)/(1-e),\qquad
 R(x)=(x-1+a)/(2a).
\]
Then \(\ell=2-a-b\), and the actual reverse first row is D with normalized residual \(1/2\). The nonzero scale converting reverse to original residuals is not presumed equal to one.

**Both reverse later labels D.** Try both assignments of the other two D clocks and both literal third read phases. No phase yields the required earlier two clocks and third clock. This uses the genuine chronology, not merely a set containment.

**One reverse later label D, one S.** The chosen D label and phase determine the other clock and both literal normalized residuals; the nonzero residue on the reverse singleton sets the conversion \(\lambda\). With the two actual singleton locations \(1,\sigma\), set \(C=A_2+B R=C_0+t(x-1)(x-\sigma)\), where \(C_0\) is the line interpolating \(L_4/R\) at the singleton rows. For every known D pair \((x,g)\), the quartic equation is exactly one affine condition on \(B,t\):
\[
 g(g-R(x))B+g(x-1)(x-\sigma)t
     =L_4(x-\ell/2)-g C_0(x).
\]
Check the two actual forward and two actual reverse D pairs, including shared labels with distinct residuals. The exact affine rank test retains the possibility of rank one or of inconsistent augmented data, and forbids \(B=0\). Each of its 48 fits (eight per forward placement) fails. The corrected normalized trace could be added here but is not needed.

**Both reverse later labels S.** The reverse must be arithmetic as a star repeats a residual at two different singleton clocks of an affine graph. Put \(v=x'_2-1\); in the original orientation the two singleton locations are \(\ell-1-v,\ell-1-2v\). The same genuine phase-ratio equation as in the arithmetic companion is
\[
 q_{\rm num}(v)(b+v)-\kappa(v)D(v)(b+2v)=0.
\]
After stripping only proven nonzero guards, interpolate \(C\) from the first singleton and these two known reverse singleton coordinates with their \(L_4/R\) values. The script computes the three-point Lagrange numerator and common denominator directly in the polynomial quotient by the phase condition. The known forward second pair determines \(B\) linearly through \(g_2(g_2-R(x_2))\ne0\). The known forward third D pair and the reverse terminal D pair impose two scalar equations. For the latter the original terminal residual is \(-(b+v)/(2a\kappa(v))\). The code checks exact polynomial gcd after multiplying only the nonzero interpolation denominator, the literal nonzero phase/residual guards, and that terminal denominator. The gcd is one in every exact mesh field, even the irreducible quadratic tower. No division by \(R\) at a D label or hidden rank pivot is used.

These three cases cover the reverse second/third pair. The exclusion does not assume positivity or symmetry of the tableau.

## Reproduce

Run `python check_terminal_two_double.py` with SymPy 1.14 and python-flint 0.8. The sibling files regenerate the exact twelve-, nine-, and eighteen-degree fields, reconstruct their labels and audit all projected guards. The SymPy tower adapter uses field inverse modulo the checked irreducible quadratic, not divisibility of representatives in the polynomial ring. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenAffineOneDoubleEnd.lean) checks only the scalar literal root-sum identities on Lean/Mathlib 4.36.0. This packet is an exact mathematical proof and reproducible arithmetic, not an end-to-end native theorem, and makes no finite-characteristic assertion.
