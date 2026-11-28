# Mixed both-singleton prefixes with one shared D: all five star-containing cases

Keep the [nine-case mixed shared-D frame](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md): strict ten stages, ordinary order at least eight, characteristic-zero field, all ten literal quadratic defects nonzero, exactly seven different clocks, and both physical endpoints singleton. Orient with S,D,D first, opposite one later D and one later S. Their D label sets share the later D of the second orientation. This packet excludes all **five phase pairs with at least one genuine star**: A1S, A2S, SA2, SA3, SS. The four arithmetic/arithmetic charts are separate, as are a disjoint D label or two prefixes each with one later D. No ordering or real-only argument is used.

## A rank-safe projective scale and the actual missing D

Use the shared notation \(0,H,p,q,t\) and the actual four scalar paid line coefficients \(A,B_1,C,D_1\), so \(A+\lambda B_1=C+\lambda D_1=0\). The literal rank-zero atlas is independently checked in the companion. Here use the equations homogeneously, without dividing by either scale coefficient.

Fit the true affine \(F_*\) from the two paid D anchors \(p,q\), and let \(M_3=\sum m_i y^i=(L_3-F_*L_4)/[(y-p)(y-q)]\). Both \(m_3,m_0\ne0\) by the true graph decomposition and the endpoint S. The physical later reverse S at \(t\) gives the [affine missing-D identity](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md#two-paid-affine-scale-rows-with-no-guessed-missing-d-copy)
\[
 z(\lambda)=\frac{m_0[H-t+(t-2H\rho_t)\lambda]}{m_3 H t(t-H)}
\]
for the third actual D label. The equations \(M_3(z)=0\) and \(2R(H)=\lambda\) now say
\[
 G(\lambda)=m_0(\lambda-1)
       +H z(\lambda)\bigl[m_2+m_3(z(\lambda)+H)\bigr]=0,\qquad
 J(\lambda)=M_3(z(\lambda))=0 .
\]
The pairwise clock guards audited in the common frame certify that the five named singleton/D labels used in this graph read are literally distinct. There is no assumption that the coefficient of \(\lambda\) in \(z\) is nonzero.

For a scale row \(a+\lambda b=0\), an ordinary polynomial \(F(\lambda)=\sum_{j=0}^n F_j\lambda^j\) has the necessary cleared row
\[
 \mathscr P(F;a,b)=\sum_{j=0}^n F_j(-a)^j b^{n-j}=0 .
\]
At a true candidate this is \(b^n F(\lambda)\), so it is necessary even if \(b=0\), and even if the true polynomial degree drops below the declared degree \(n\). Thus use the determinant \(E=A D_1-C B_1\) and the four rows obtained using \(G,J\) with each physical line. The actual rank-zero argument need not be substituted for a possibly lost pivot. Denominators are checked against the same true tap, distinct-clock, Legendre and graph guards as the earlier frame.

## Exact projections and guarded fibres

Project the determinant separately against those four rows in the reflected D offset \(v\), strip only true \(u\)-only factors, and take the gcd. These are ordinary exact resultants, which vanish for a common \(v\) even if a leading coefficient at the candidate drops. Exact projected degrees and factor profiles are:

| Phase | Guarded projected degrees | Common irreducible \(u\)-factors |
| --- | --- | --- |
| SS | 168,294,138,249 | quadratic, multiplicity 2 |
| SA2 | 375,636,407,684 | none |
| SA3 | 393,663,353,603 | degree 12, multiplicity 4 |
| A1S | 408,685,274,484 | none |
| A2S | 350,596,284,497 | none |

In SS the exact quadratic field leaves linear joint \(v\)-gcd, wholly on the forbidden \(q=t\). With SA3 the exact degree-12 field has a monic degree-17 determinant row in \(v\); removing all its factors supported on the actual nonzero rear tap numerator \(N(v/2)\) leaves degree 15. These quotients occur **before any reduction**, so no characteristic-zero \(v\) is lost.

For that rank-safe SA3 row, the fixed residue \(u=14\) at \(p=37\) is a simple root with the full degree of the \(u\)-factor retained. It therefore gives an embedding of the abstract rational \(u\)-field into \(\mathbb Q_{37}\). The exact monic degree-15 row has integral coefficients at that place, so every actual \(v\) is integral in the extended valued field. The reduced monic row and the four integer projection input rows have joint gcd one over \(\mathbb F_{37}\), ruling out every algebraic residue of \(v\). In particular no inline \(\lambda\)-rank or \(v\)-pivot is assumed to survive modulo 37, and the result is not a lower bound in arbitrary characteristic 37.

Run `SYMPY_GROUND_TYPES=flint python check_star_cases.py` with SymPy 1.14 and python-flint 0.8; optional case IDs allow individual exact replays. The shared [native scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonMixedShareRank.lean) covers scale determinant and secant clearing, not the complete rooted-order reduction or elimination. The general 10–11 stage interval is unchanged.

The publication audit independently re-ran the complete exact elimination. The scalar Lean companion is a draft and was not kernel-checked for this release.
