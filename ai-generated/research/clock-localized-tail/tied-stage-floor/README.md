# Two-coordinate classification at the tied nonsingular stage floor

For the indicated orders, the two commutator parity lower bounds agree. A triangular method attaining that bound and having no zero component of its quadratic stage residual is characterized by two polynomial equations, a weight formula, and a test for the chronology of the stages. The zero-residual case has separate necessary conditions. These statements are not an increase in the unconditional lower bound.

- [The two equations and the weights](SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md). The stage pairs satisfy a simple complete intersection. The weights are fixed by its Jacobian.
- [Chronology and the common diagonal](EXACT-PREFIX-DIAGONAL-RECONSTRUCTION.md). Stage-pair data with a given chronology and nonzero common diagonal admit a method of the required order exactly when the stated leading-matrix tests pass.
- [The first zero residual](ZERO-RESIDUAL-RANK-LOSS-AND-FIRST-PIVOT.md). The zero branch satisfies lower-degree relations and, over an ordered field, positive-mass restrictions. The proof also identifies the first zero stage's interpolation degree.
- [A split-trace diagnostic](ZERO-BRANCH-SPLIT-INTERSECTION-DIAGNOSTIC.md). This gives an additional weight restriction when a separate coprimeness hypothesis is known, not a classification of later zero stages.

In these notes \(E_j\) is the span of actual Butcher weight vectors for trees of order at most \(j+1\), and \(F_j\subseteq E_j\) is the image of formal tree combinations with zero exact polynomial. The initial commutator is
\[
 C\coloneqq\operatorname{diag}(\mathbf c),\qquad M\coloneqq CA-AC-A^2.
\]
It sends \(E_j\) into \(F_{j+2}\) and is invertible for nonsingular triangular \(A\). The scalar equations give quotient rank at least \(\min(j+1,p-j)\) by the formal polynomial pairing. Summing in each parity yields the quadratic lower bounds. At equality in both parities each inequality is equality, hence \(F_{j+2}=ME_j\) in the available grades. The diagonal matrix of the quadratic residual divided by two also sends \(E_j\) into \(F_{j+2}\), by rooted sums with a zero-model combination of the chain and bush of order three. If that diagonal matrix is invertible, its image has the same dimension as \(ME_j\), giving the two-coordinate description inductively from the bush polynomials.

## Low orders, chronology, and the sign of the stage residual

- [Exact minima at orders three and four](COMPLETE-NONSINGULAR-ORDER-THREE-AND-FOUR-EQUALITY.md) classifies every real nonsingular triangular tableau attaining its stage floor. The common-diagonal subclasses have two and three members, respectively. The classification includes the silent first weight and repeated-clock cases; no literature-priority claim is made.
- [First rows and restricted residual layers](FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) gives mandatory first-row identities. The residual-layer bound requires distinct abscissae and the single-feeding-level hypothesis.
- [Sign restrictions](REAL-QUADRATIC-RESIDUAL-SIGN-PRICE.md) and the [ordered-field refinement](SIGNED-EXCEPTIONAL-AND-ORDERED-FIELD-ADDENDUM.md) give a conditional bound at order \(4h-1\): when the quadratic stage residuals at every nonzero-weight stage are strictly of one sign, at least \(2h^2+h\) stages carry weight, without assuming triangularity. The signed excess and the marginal inertias at equality do not determine all four joint sign counts.
- [The literal donor at a zero residual](ZERO-RESIDUAL-DONORS-AND-TWO-COORDINATE-FLAGS.md) proves the separate field-valued equality constraint and accounts for its dimension only once.

## The distinct-abscissa, single-feeding-level case

[The forced first three rows](FORCED-STAR-OR-MIXED-RESIDUAL-FEED.md), the [layer recurrence](LITERAL-LAYER-RECURRENCE-AND-PIVOT-INDUCTION.md), and the [two-ended argument](TWO-ENDED-WIDTH-OR-LAGUERRE-CONTINUATION.md) give a physical support obstruction. In this class the nowhere-zero branch cannot attain the tied quadratic floor at orders 6, 7, 8, 10, or 11. A separate zero-residual argument applies at order 6. The statements assume real coefficients, a nonzero common diagonal, distinct abscissae and no receiving row fed by more than one residual level. They do not cover all SDIRK tableaux.
