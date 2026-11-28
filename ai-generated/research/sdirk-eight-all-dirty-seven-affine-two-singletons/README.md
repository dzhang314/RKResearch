# The affine seven-clock graph needs a two-double prefix at a singleton endpoint

Keep the characteristic-zero, all-dirty, strict ten-stage ordinary-order-at-least-eight hypotheses and the affine singleton graph of the [affine opener packet](../sdirk-eight-all-dirty-seven-affine-openers/README.md). A label D is doubled; a label S is singleton. The two physical endpoints cannot both be D.

**New restriction.** If both endpoints are S, then at least one actual first-three prefix (original or weighted mirror) has type **S,D,D**. If exactly one endpoint is S, then its own first-three prefix is either S,D,D or an arithmetic S,D,S with nonzero third tap. In particular the latter cannot be a star. These are chronology restrictions, not an unrestricted affine-graph or stage exclusion.

## Pair geometry of an S,D,S opener

At a singleton first row write \(R(x)=(x-1+a)/(2a)\) in the normalized diagonal-one clock, \(a\ne0\). Let \(u=x_2-1\), \(\kappa=1+2u-u^2\), and \(q=2g_3\). Reuse the exact literal arithmetic numerator and denominator \(q_{\rm num}(u), D(u)\) in the companion. In a star, \(x_3=3-u\) and \(q=\kappa\). When this third clock is S, its graph value imposes
\[
      \kappa=1+(2-u)/a,\qquad u=1/a
\]
by the guard \(u\ne2\). The resulting two non-initial pairs are exactly the pair set of the companion's **S,S,D star**, with the two physical positions switched: singleton clock \(3-1/a\), doubled clock \(1+1/a\), and both residuals \(\kappa/2\). The same \(\kappa\) follows from replacing \(u\) by \(2-u\). We do not permute a proposed tableau or claim an order invariant under such reassignment. The companion's exclusions in both endpoint cases use only this consumed physical pair list from the first three stages, not a fourth read or the order of rows 2 and 3. Hence they apply unchanged to this star pair-data branch. In particular, when the other endpoint is D, S,D,S star is excluded.

In arithmetic, \(x_3=1+2u\) and S at that clock imposes \(q_{\rm num}/D=1+2u/a\). Using the companion constant-graph numerator identity \(q_{\rm num}-D=4u(u-2)(u^3-3u^2+1)\), this fixes
\[
              a=\frac{D(u)}{2(u-2)(u^3-3u^2+1)}.             \tag{2}
\]
Every denominator is nonzero by the genuine arithmetic guards and because \(a\) and \(u\) are nonzero. The pair set now has other singleton at \(1+2u\) and doubled clock at \(1+u\). This is the only new phase, denoted T for these calculations.

## All phase combinations at two singleton endpoints

Assume both endpoint prefixes contain two S labels. They cannot have three by the actual first-nonzero residual argument in the companion. Thus three complete pair-data phases suffice at each end:
- A: S,S,D arithmetic, with \(a\) free, other S offset \(2-1/a\), D offset \(4-2/a\).
- S: either star order, with \(a\) free, other S offset \(2-1/a\), D offset \(1/a\).
- T: S,D,S arithmetic, with \(a\) as in (2), other S offset \(2u\), D offset \(u\).

The physical weighted mirror gives the same formulas with its \(b\) and/or gap \(v\). The right endpoint is \(\ell=2-a-b\), and the doubled-centered graph zero is \(z=b-a\). Let \(w_f,w_r\) be the other two S offsets from their respective endpoints; let \(p_f,p_r\) be the two D offsets. The actual two D-label coordinates are \(y_f=a+b+2p_f\) and \(y_r'=a+b+2p_r\) in their respective orientations. They must satisfy the companion's exact polynomial equations
\(K(y_f,z;\ell)=K(y_r',-z;\ell)=0\), including when a D label equals the affine graph zero or when the two ends touch the same D label. The four S labels are all used in the two disjoint prefixes. Their monic quartic must take the \(L_4\) value at the graph zero. Hence the third necessary equation is
\[
                   J_4(z)=560\,a(a+w_f)b(b+w_r).            \tag{3}
\]

The companion already retires A/A, A/S and S/S. For A/T, S/T, T/T, compute integer polynomial numerators of these two divided-difference equations and (3). The code uses the common denominator \(d_f d_r\), where \(d_f=a\) or \(d_r=b\) in an A/S orientation, and \(d=2(u-2)(u^3-3u^2+1)\) in a T orientation. The polynomial \(K\) is homogeneous of degree six in \(y,z,\ell\), and (3) of degree four in the five normalized coordinates, so clearing denominators does not need any division by \(R\) at a doubled label. Input simplification removes only factors of the nonzero denominators.

The gcd of the two resultants of each divided-difference equation with (3), eliminating the forward parameter, is exactly
\[
      [(v-2)(v^3-3v^2+1)]^n,\qquad
      n=27\text{ for A/T or S/T},\quad n=111\text{ for T/T},
\]
up to nonzero scalar. These are precisely the forbidden reverse T denominator roots. Thus even an algebraic extension to realize more phases cannot solve the necessary equations. There is no positivity, order, or weight-sign assumption and no generic rank hypothesis beyond the established complete intersection. A common root forces all resultant projections to vanish also when leading coefficients specialize to zero; the exact resultant calculation does not discard those points.

## Reproducible computation

Run `python check_arithmetic_late_singleton.py` with SymPy 1.14 and python-flint 0.8 (about nine seconds in the tested environment). The local `exact_interp.py` evaluates each exact Sylvester determinant at enough consecutive integer reverse parameter values to exceed its proved degree bound \(d_u(f)d_v(g)+d_u(g)d_v(f)\). The evaluators check that the leading coefficients at each evaluation point remain nonzero before taking that specialized integer-polynomial resultant. Integer Newton interpolation reconstructs the unique exact projected polynomial, with a divisibility check for every factorial in the interpolation formula. No finite-characteristic extrapolation or approximate roots are used. Independent exact multivariate FLINT resultant calculations returned the same gcds. The packet uses the companion’s checked Lean scalar identities, with no additional end-to-end native Lean claim.
