# Two later-singleton prefixes cannot share their single doubled label

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, all ten literal quadratic defects nonzero, and exactly seven distinct physical clock labels. Suppose both endpoints are singleton and each true first-three prefix has one later S and one later D. The two prefixes **cannot use the same D label**. All six phase pairs up to the true weighted mirror are covered; this does not restrict the cases when the prefixes use disjoint D labels. No ordering of the coefficient field is needed.

## Actual paid pairs, all four S, and the scale rank

Use the diagonal-one coordinate \(y=x-1\), endpoints \(0,H\), \(m=(H+2)/2\), and actual reflected coordinate \(H-y\). Let the shared D be \(p=u\), with reverse D offset \(v\), so \(H=u+v\). The additional forward S is \(s\) and the additional reverse S in original coordinates is \(t\). The five labels \(0,H,p,s,t\) are distinct. They include **all four S labels** in the [seven-clock structure](../sdirk-eight-all-dirty-seven-clock/README.md).

For a side parametrized by its D offset \(a\), the three true phases pay its later S offset \(2a,a/2,2-a\) in A2 (D physically second), A3 (D physically third), and star respectively. In an arithmetic side the actual second gap is \(a\) for A2 or \(a/2\) for A3; the normalized second and third defects are \(\kappa/2,N/(2D)\) at that gap, with the [literal pair polynomials and guards](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md#physical-coordinates-and-all-nine-types). A true star at either physical order uses its corresponding formula and pays the same two equal defects. In particular the star pair-data use \(a\) as the shared D offset, not necessarily the physical second gap. The actual weighted mirror identifies reversed phase pairs, leaving A2A2, A2A3, A2S, A3A3, A3S, SS. None assumes a tableau invariant under swapping rows.

Let \(f_p,f_s\) be normalized forward defects, \(\rho_p,\rho_t\) normalized reverse defects, and \(\lambda\ne0\) convert reverse defects to original. At the shared D, actual Vieta gives
\[
 \beta=B\lambda=-L_4(p)/(f_p\rho_p),\qquad f_p-\lambda\rho_p\ne0
\]
because both literal residual roots are different. The actual quadratic \(T=\lambda A_2\) and the true graph \(R\) have these paid reads:
\[
\begin{array}{c|ll}
y & T(y)&R(y)\\\hline
0&2\lambda L_4(0)-\beta/2&1/2\\
H&2L_4(H)-\beta\lambda/2&\lambda/2\\
p&-\beta(f_p+\lambda\rho_p)&\text{not paid}\\
s&\lambda L_4(s)/f_s-\beta f_s&f_s\\
t&L_4(t)/\rho_t-\beta\lambda\rho_t&\lambda\rho_t .
\end{array}
\]
No other physical copy is assigned a residual. For a quadratic \(K_2\) write \(J(y)=(H-y)K_2(0)+yK_2(H)\). Interpolating from \(0,H,c\) gives the exact cleared condition
\[
 c(c-H)[H K_2(d)-J(d)]-d(d-H)[H K_2(c)-J(c)]=0.
\]
Use this for \(K_2=T\) at \((c,d)=(p,s),(p,t)\), and for \(K_2=R\) at \((s,t)\). This gives **three affine lines in the true \(\lambda\)**, all paid before the two unobserved D clocks are recovered. If the coefficients of \(\lambda\) are all zero, all three constants must be zero as well. Otherwise the actual lines give every \(2\times2\) homogeneous coefficient minor zero. The minors retain all possible losses of one or two row pivots.

## Exact rank-zero and projected factors

Each row is cleared using only true tap, distinct-clock, nonzero half-width, and shared \(L_4(p)\ne0\) guards. The latter follows from consecutive Legendre coprimality. In all six modes neither the six rank-zero rows nor the three minor rows have a common nonconstant bivariate factor. The rank-zero projection uses the smallest row against the rest; five modes have unit projected gcd. A2A2 projects only to \((u^3-3u^2+1)^3\), but over that exact cubic field the six rows already have joint \(v\)-gcd one. Thus rank zero is impossible without prescribing a pivot.

The two ordinary affine \(v\)-resultants of the smallest minor against the other two give this exact profile, after genuine \(u\)-only guard removals:

| Mode | Projected degrees | Common irreducible \(u\) factor degrees (all simple except stated) |
| --- | --- | --- |
| A2A2 | 252,182 | 2,5,6,7,138 and 3 with multiplicity 2 |
| A2A3 | 185,151 | 9,12,15,104 |
| A2S | 95,91 | 10,68 |
| A3A3 | 191,98 | 8,11,12,15,48 |
| A3S | 101,55 | 8,10,33 |
| SS | 38,25 | 5,8,10 |

Ordinary resultants are necessary even at specialized leading-degree drops. All 23 irreducible factors are exhaustive, not a rational or real scan. In 13 fibres an exact linear \(v\)-gcd lies on a true forbidden clock/tap guard (\(H=0\), \(t=0\), \(s=t\), or \(N(v/2)=0\)). In three more fibres the exact g.c.d. is also linear and the genuine scale is recovered by a checked nonzero line coefficient: A3A3 degree 11 and SS degree 5 force **equal actual shared D residuals** \(f_p=\lambda\rho_p\); SS degree 8 forces the paid graph \(R\) to have zero curvature, contradicting the [quadratic graph requirement](../sdirk-eight-all-dirty-seven-affine-final/README.md). These diagnoses are exact over the abstract rational fields, not tests of guard failure modulo a prime.

## Paid graph remainder at six fixed places

The remaining seven factors have full-degree simple good places listed below. The selected root \(u\) gives an embedding of its abstract rational field into \(\mathbb Q_\pi\). At least one minor retains its **nominal positive degree in \(v\)** with unit leading coefficient, so all actual values of \(v\) are integral in the extended valued field. The joint residue gcd of all three minors is linear with the single indicated \(v\) root; it covers all algebraic residue extensions, not merely a prime-field scan. At each indicated pair all paid denominators are units and at least one of the three actual scale coefficients is a unit, so \(\lambda\) specializes integrally with its true value. The exact rank argument did not assume these mod-\(\pi\) units; they are individually certified for the fixed place.

Reconstruct the whole paid quadratic \(R\) from \(0,s,H\), with its leading coefficient a unit at the selected place. The true affine \(F_*\) of the pair decomposition has \(F_*(p)=L_3(p)/L_4(p)\). Thus the remainders modulo \(R\) of
\[
 V=L_4(p)L_3-L_3(p)L_4,\qquad W=(y-p)L_4
\]
must be proportional: their \(2\times2\) scalar determinant is zero. This gate does not need the affine slope to be integral, since the determinant already vanishes in the original field before reduction, and the remainder uses only the checked unit leading coefficient of \(R\). It does not assume \(R\) splits or any hidden D label.

| Mode / factor degree | \((\pi,u,v)\) | Contradiction |
| --- | --- | --- |
| A2A2 / 138 | (19,3,15) | \(R\) remainder determinant nonzero |
| A2A3 / 104 | (47,24,18) | same |
| A2S / 68 | (29,22,11) | same |
| A3A3 / 48 | (19,8,1) | same |
| A3S / 8 | (11,8,9) | same |
| A3S / 33 | (31,15,25) | same |
| SS / 10 | (41,39,16) | actual row-four gate below |

These are statements over characteristic zero via fixed complete-place certificates, not finite-characteristic lower bounds.

## Only SS degree 10 needs the two unobserved D labels

At the last place, \(L_4\) is a unit modulo \(R\), hence the true affine \(F_*=(L_3/L_4)\bmod R\) is recovered integrally. The remaining D quadratic is \((L_3-F_*L_4)/(R(y)(y-p))\). Its leading coefficient is verified a unit, so both actual roots are integral. The first three and last three physical rows already consume all four S labels and both copies at the shared D. Thus the true fourth row must be at one of the two remaining D labels. This census is about actual literal rows and does not require deciding which hidden D comes next.

The paid values at \(0,H,p\) recover \(T\), and the nonzero residue scale and \(\beta\) recover \(A_2=T/\lambda\), \(B=\beta/\lambda\) integrally. Let \(T_2\) be the actual first-three residual interpolant at \(y=0,p,s\), expressed in \(x=y+1\), and let \(b_x,c_x\) be its linear/quadratic coefficients. The [actual fourth read](../sdirk-eight-all-dirty-seven-clock/README.md#literal-fourth-reads-including-singular-pivots) is \(C_4(y)g_4=N_4(y)\), where
\[
 C_4=1-\Lambda+b_x+c_x\Delta,\quad N_4=T_2-JT_2,\quad
 \Lambda=1+(x-1)/\kappa,\quad
 \Delta=\tfrac43+2(\kappa+1)(x-1)/(3\kappa).
\]
Here \(J\) is the primitive from zero, and the actual \(\kappa\) is the same in either forward star order. Eliminate the unknown \(g_4\) from its paid Legendre equation using the **necessary**, denominator-free row \(C_4^2 L_4-A_2 N_4 C_4-B N_4^2=0\). The exact \(p=41\) gcd of this row with the remaining D quadratic is a unit. In particular a singular affine fourth pivot would still be retained by the necessary cleared test. This finishes the only projected factor that needs a hidden-D reconstruction.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_11_share.py` with SymPy 1.14 and python-flint 0.8. This directory's Python replay is self-contained; there is no previous arithmetic cache or compiled C requirement. Optional case IDs split the six exact proofs by phase. The [native Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSShared.lean) verifies the scale/minor, remainder determinant and affine-fourth clearing identities only. The rooted-order reduction and exact elimination are not all native Lean. No general stage bound changes.

The publication audit independently reran the standalone exact elimination. The accompanying scalar Lean statements are draft, not kernel-checked for this release.
