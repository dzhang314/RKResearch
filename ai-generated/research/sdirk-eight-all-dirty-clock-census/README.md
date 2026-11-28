# An all-dirty strict SDIRK8 floor needs at least seven different clocks

Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal \(\gamma\), and suppose every physical quadratic residual is nonzero. **At least seven different numerical clock labels must occur.** The alternative with exactly five doubled labels is impossible; a six-label configuration is already excluded by linear rank. This is a clock-census restriction on the nowhere-zero branch, not a change to the general stage interval 10–11.

## 1. Complete-intersection clock dichotomy

Use the [nowhere-zero complete intersection and weight formula](../clock-localized-tail/tied-stage-floor/SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md). Normalize the diagonal to one, the endpoint to \(2m=1/\gamma\), and write centered clock \(t=x-m\) and normalized quadratic residual \(g\). Its ten distinct physical pairs satisfy
\[
 U=L_4(t)-g[A_2(t)+Bg],\qquad
 V=L_3(t)-g[D_3(t)+F(t)g],
\]
where \(L_4,L_3\) are consecutive monic Legendre modes of the normalized centered interval, \(\deg A_2,\deg D_3,\deg F\le2,3,1\), and \(B\ne0\) by coprime weighted leading forms. Each clock has at most two stages, from the quadratic in \(g\). The known weight formula makes all ten physical weights nonzero.

Six paid moments of the **grouped** weights \(\sum_{i:t_i=t}b_i g_i\) vanish (test \(g\,t^j\), \(0\le j\le5\)). If there are at most six labels, Vandermonde forces all these aggregates zero. No singleton can then occur since \(b_i g_i\ne0\). Thus the only such case is exactly five labels, each doubled.

Write \(P=B D_3-F A_2\), \(Q=B L_3-F L_4\). The identity \(BV-FU=Q-gP\) shows that each doubled label is a common root of \(P,Q\). Hence if \(P\ne0\) there are at most three doubles. If \(P=0\), every label is a root of \(Q\), a nonzero polynomial of degree at most five by consecutive Legendre coprimality; the at-most-two bound then gives exactly five doubled labels. Conversely five doubled labels force \(P=0\), since \(\deg P\le3\). At each such double the ordinary grouped mass is nonzero: its two individual weights cannot cancel in both ordinary sum and \(g\)-weighted sum when the two residuals differ and both weights are nonzero.

## 2. Five doubled labels have a symmetric finite diagonal census

Assume the five-label alternative. With \(P=0\) every label solves
\[
 L_3(t)=(\alpha t+\beta)L_4(t),\qquad \alpha\ne0 .
\]
Here \(L_4(t)\ne0\) at each label, by coprimality with \(L_3\). The actual first and terminal uncentered clocks are \(1,2m-1\). If \(m\ne1\), their centered locations are \(\pm(m-1)\). The odd/even parities of \(L_3,L_4\) force \(\beta=0\) by adding the two equations. If \(m=1\), the common centered clock is zero and its equation gives \(\beta=0\) directly. Hence the five distinct labels are \(\{0,\pm h,\pm j\}\). For \(m\ne1\) take \(h=m-1\), with \(j\ne0,\pm h\). The grouped ordinary masses at reflected clock points coincide, by exactness on degree-four Lagrange cardinals and symmetry of the normalized moment; individual copy weights need not coincide.

The ordinary moment \(I(t\cdot t(t^2-h^2)(t^2-j^2))=0\) uses degree six and yields
\[
        15m^4-21m^2(h^2+j^2)+35h^2j^2=0.                  \tag{1}
\]
This follows solely from uniform centered moments \(I(t^{2k})=m^{2k}/(2k+1)\).

In the actual first three rows the two later clocks are distinct from each other and from the first. Their [literal first-three gates](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) are arithmetic, or star with zero third predecessor tap from row 2. For \(m\ne1\), write the centered first three as \((-h,f,g)\). Choose the ordered pair \(f,g\) from \(h,0,j,-j\), with different labels. The arithmetic equation is \(g=2f+h\); the star equation is \(f+g=4-2m\). Each is a scalar linear relation in \(m,j\) after \(h=m-1\), and with (1) it is a finite algebraic constraint, **except** the literal midpoint arithmetic triple \(1,m,2m-1\). The attached exact census enumerates every ordered pair and all algebraic guards. Up to the irrelevant sign of \(j\), the finite \(m\ne1\) cases are:

| Literal case defining the mesh | Diagonal polynomial (nonzero scalar multiples equivalent) | \(j\) or \(j^2\) |
|---|---|---|
| Arithmetic \(f=h,\ g=j\) | \(8m^4-56m^3+112m^2-84m+21\) | \(3(m-1)\) |
| Arithmetic \(f=j,\ g=0\) | \(2m^4-14m^3-21m^2+28m-7\) | \(-(m-1)/2\) |
| Arithmetic \(f=j,\ g=-j\) | \(8m^4-56m^3+28m-7\) | \(-(m-1)/3\) |
| Star \(h,j\) | \(120m^4-1008m^3+2744m^2-2800m+875\) | \(5-3m\) |
| Star \(0,j\) | \(50m^4-462m^3+1463m^2-1680m+560\) | \(4-2m\) |
| Star \(h,0\) | \(m=5/3\) | \(j^2=485/231\) |
| Star \(j,-j\) | \(m=2\) | \(j^2=156/49\) |

The [saturated weighted mirror](../clock-localized-tail/tied-stage-floor/README.md) is available because every weight is nonzero; it has diagonal one and reflected clocks \(2m-x\). Thus the **same** clock mesh and first-three census apply at the opposite end, without assuming reflection symmetry of the method or of the chronology. If either opener is non-midpoint, its mesh is in the table.

If **both** ends are midpoint arithmetic, set \(u=m-1\), \(\kappa=1+2u-u^2\), \(H=-2+u+4u^2-u^3\), \(q=(1+4u-4u^2)+4u^2(3u-2)/H\). The actual forward residuals on the three common labels \(1,m,2m-1\) are \((1,\kappa,q)/2\); from the other end they are a nonzero multiple of \((q,\kappa,1)/2\). The product at each double is \(-L_4(t)/B\) by Vieta. Comparing the middle with the first gives \(qL_4(0)=\kappa^2L_4(h)\). Clearing the explicit nonzero \(H\), the exact factorization removes \((m-1)^2\) and \(m^2-4m+2=-\kappa\), both forbidden. The remaining factor is
\[
 2m^7-38m^6+270m^5-882m^4+1365m^3-985m^2+315m-35.
\]
Thus this exceptional mesh is also finite; the field with an adjoining sign choice of \(j\) is checked at degree 14.

For \(m=1\) the centered first clock is zero. The next two must come from different \(\pm\)-groups: opposite values of one radius neither form the arithmetic relation \(g=2f\) nor the star relation \(f+g=2\). Let the signed first gap be \(u=f\). The other signed radius is \(2u\) or \(2-u\) and (1) gives, respectively,
\[
 u^4-\tfrac34u^2+\tfrac3{28}=0,\qquad
 u^4-4u^3+\tfrac{14}{5}u^2+\tfrac{12}{5}u-\tfrac{69}{35}=0.
\]
These account for the two half-diagonal mesh fields. All assertions involve actual clock labels, not the signs of square roots.

## 3. Exact two-ended fourth-read exclusion on every mesh

For each exact mesh the replay enumerates the **literal** first-three clock placements and their residuals. It uses the normalized formula \(k=1+2u-u^2\) and the third residual \(q/2\), with \(q=k\) for star and the indicated rational \(q\) for arithmetic. A vanishing residual, a zero arithmetic numerator for an asserted nonzero tap, or a duplicate physical pair is forbidden. Every algebraic choice of mesh is covered because the reported primitive polynomials are irreducible and the inverse coordinates are checked; replacing the sign of a radius leaves the set of allowed labeled points the same.

For the fourth read, let \(T_2(x)=a_0+b_0x+c_0x^2\) interpolate the actual first three residuals, and \(J\) integrate from zero. The pure grade-three formulas give
\[
 Ag=g\Lambda,\quad Ax^2-x^3/3=g\Delta,\quad
 \Lambda=1+(x-1)/k,\quad
 \Delta=4/3+2(k+1)(x-1)/(3k).
\]
They are determined by the first two reads and the rank-two \(F_3=g\,\langle1,x\rangle\) flag. Consequently the supported input \(g-T_2(x)\) kills all three prior coordinates, giving the actual fourth diagonal equation
\[
 g_4\,[1-\Lambda(x_4)+b_0+c_0\Delta(x_4)]
       =T_2(x_4)-JT_2(x_4).
\]
The code evaluates this on **each of the five mesh clocks**, retaining both the regular and all singular cases. It does not assume the fourth clock new.

At the first three centered labels interpolate quadratics \(A^{(0)}\) through \(L_4(t_i)/g_i\) and \(G_2\) through \(g_i\). Thus \(A_2=A^{(0)}-B G_2\). Each known fourth pair gives the one linear equation
\[
 B\,(g_4-G_2(t_4))=L_4(t_4)/g_4-A^{(0)}(t_4),
\]
and the code checks or retains each resulting rank possibility. The only undetermined fourth residual is the **\(m=2\) arithmetic center repetition**: \(T_2(x)=x/2\), and both fourth coefficients vanish at \(x=2\). It is retained as a free quartic fit with its actual fourth clock occupied. In particular it cannot be paired with another prefix using the center, since that would consume more than two physical stages at that label. All other surviving fourth-prefix fits have a fixed nonzero \(B\).

Write \(A_{\rm f},B_{\rm f}\) for the forward quartic coefficients and \(A_{\rm r},B_{\rm r}\) for the reverse-normalized ones. If \(\lambda\ne0\) maps the reflected residual to the original residual, the chronological weighted-adjoint formula implies the necessary exact match
\[
   A_{\rm r}(t)=\lambda A_{\rm f}(-t),\qquad
   B_{\rm r}=\lambda^2 B_{\rm f}.
\]
It is a relation between descriptions of the same original pair set, not an assumption that the original tableau is symmetric. After excluding excessive physical occupancy (more than two at any label), the exact equations in \(\lambda\) are linear/quadratic when both \(B\)'s are fixed. If only one is fixed, the three coefficient equations remain quadratic after clearing \(\lambda\), using \(A=A^{(0)}-B G_2\) on the free side. The free fourth residual is **not** specialized when using this necessary equation. No cases with two free \(B\)'s survive physical occupancy. The exact polynomial gcd in each admissible direction is constant after the nonzero scale and distinct physical pair guards.

| Exact mesh fields | Field degree | Four-prefix fits before opposite-end test |
|---|---:|---:|
| Three non-midpoint arithmetic quartics | \(4\) each | \(4\) each |
| Two nonconstant-star quartics | \(4\) each | \(6\) each |
| \(m=5/3\) | \(2\) | \(4\) |
| \(m=2\) | \(2\) | \(5\), including one free fourth residual |
| Two half-diagonal fields | \(4\) each | \(4\) each |
| Both midpoint arithmetic | \(14\) | \(2\) |

Every row leaves zero opposite-end matches. This rejects the entire five-double chart over characteristic-zero fields, yielding the claimed at-least-seven restriction.

## 4. Verification scope

Run `python check_clock_census.py` and `python check_end_fits.py` with SymPy 1.14 (Python-flint 0.8 used for the tested replay). They check the literal finite census, inverse mesh coordinates, every singular fourth-read option and the exact small-polynomial exclusions. No finite reduction or numerical search is needed. The [Lean companion](../../lean/RKCert/Research/SDIRKEightAllDirtyClockCensus.lean) is staged scalar source, not a fresh stock build; the actual tableau, clock census, and exact end fits are the source proof. The adjacent [fibre-residue note](FIBRE-RESIDUES.md) gives further general diagnostics once the at-least-seven restriction holds. No support or weight-sign assumptions beyond the stated all-dirty chart are used.
