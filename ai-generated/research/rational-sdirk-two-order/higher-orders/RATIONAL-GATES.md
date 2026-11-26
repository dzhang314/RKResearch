# Exact rational scalar gates without search or replay

All the families here use \(p-1\) distinct scalar output sites for order \(p\). This is one more moment than ordinary interpolation guarantees. The extra site is obtained rationally as follows.

Write \(I(X^j)\coloneqq 1/(j+1)\). Take a monic hull \(H\) for all chosen sites except the last undetermined one. Put
\[
 D\coloneqq I(H),\qquad N\coloneqq I(XH),\qquad
 z\coloneqq N/D,\qquad F\coloneqq(X-z)H .
\]
If \(D\ne0\) and the sites are distinct, \(I(F)=0\) gives scalar exactness through degree \(p-1\). The next degree fails exactly when
\[
                    D I(X^2H)-N^2\ne0 .
\]
The numerator of the weight at \(z\) is \(D\) before normalizing by the corresponding node differences. At any other site \(y\), write \(H=(X-y)K\). Its weight numerator, multiplied by \(D\), is
\[
 D I(XK)-N I(K)=I(XK)^2-I(K)I(X^2K).
\]
This last identity is independent of \(y\); it follows on inserting \(H=(X-y)K\) in \(D,N\). Thus the scalar gates are specified by finitely many polynomial nonvanishings.

## Rational parameter choice, including mixed decoder samples

Let \(F_0\) be the hull of the fixed sites, with \(e\) roots in \((0,1)\), and let the other sites except \(z\) be independent variables \(u_i\) which will be chosen distinct and negative. If there are at least \(e+1\) such variables, all the scalar gates are nonzero polynomials in the variables.

Here is a sign proof, used only to prove that the polynomials are not identically zero. In a test specialization one may let the first \(e\) variables coincide with the \(e\) interior roots of \(F_0\). Their duplication makes the sign of the test hull definite on \((0,1)\), and proves the nonvanishing of its zeroth moment and of its two-by-two moment determinant. The same test applies to each cofactor \(K\): after omitting a variable site at least \(e\) variables remain, and after omitting a fixed site there are at most \(e\) interior factors to duplicate. If \(z\) is tested against a specified site, \(N-yD=I((X-y)H)\). For an exterior fixed site the extra factor has constant sign; for an interior fixed site it already doubles that site and one need only duplicate the other interior roots. For a variable site, set that variable negative and duplicate the interior roots with the remaining factors. All claimed polynomials are therefore nonzero. Actual choices are made away from every coincidence; coalescence was only an admissible test of a polynomial identity.

The only mixed decoder check needed below has one sample at the solved \(z\). Fix \(h-1\) distinct negative sample times, where \(h=2d-P-1>0\) is the number of samples added to the old moments for degree \(d-1\). After these samples, the remaining kernel is the span of their product times the monic orthogonal polynomial of degree \(P-d+1\) for that product weight. This follows by factoring the sample product from a kernel polynomial, as in the preceding note, but retaining its one last possible degree. Failure of the final sample at \(z\) is therefore one polynomial check against \(z\) (plus the already excluded collisions). It is not an identity if any non-sample site variable remains free: varying that variable \(u\), the function \(z\) is
\[
                     \frac{I(X^2K)-u I(XK)}{I(XK)-u I(K)}
\]
for the hull \(K\) not containing \(u\), and is nonconstant by the cofactor determinant gate. The remaining orthogonal polynomial depends only on the negative sample times and not on \(u\).

For successive lifts, a previously selected negative stage site may occur as a donor in a later polynomial. Treat all newly chosen negative sites in the finite chain as one joint parameter list; within any one lift, the negative gauge variables are entries with distinct indices in that list. Each success condition is a nonzero polynomial, after clearing denominators. Their product is nonzero. A nonzero polynomial over the rationals does not vanish on all rational tuples in an open negative box. This proves simultaneous rational choices, with no assumption that an earlier fixed donor set picked arbitrarily would work. It also specifies a deterministic finite generating rule: take the first suitable tuple on an increasing finite grid of negative rationals. Equivalently, use any negative integer grid whose size exceeds the degree of the product in each variable, by elementary polynomial interpolation. The existence proof, not a run of this rule, is the current certificate.

## A borderline scalar rule at order eleven

Here the fixed hull is the product over \(0,2/7,4/7,6/7,1/2\). There are \(e=4\) interior fixed sites and exactly four negative variables. The gates for \(D\), the full two-by-two determinant, and the fixed-site cofactors follow by the preceding sign tests. For collision with a variable site, if \(I(F_0(X-u)^2G)\) were identically zero, where \(G\) uses the three other variables, then comparing the coefficients of \(u\) would make \(I(F_0Q)=0\) for every polynomial \(Q\) of degree at most five. Indeed degree-three split monic products linearly span all degrees at most three. Taking \(Q\) to be the product over the four interior roots gives a nonzero definite integral, a contradiction.

For a free-site cofactor there are only \(e-1=3\) remaining site variables. Suppose its two-by-two moment determinant were identically zero. The linear image in symmetric two-by-two matrices, as \(G\) ranges over polynomials of degree at most three, would then consist entirely of singular matrices. To see the implication from split monic products, their real coefficient set contains an open set in the monic degree-three hyperplane, and homogeneity removes the monic normalization. A real linear subspace of symmetric two-by-two singular matrices has a common nonzero kernel vector: two nonproportional nonzero rank-one symmetric forms have a nonsingular sum. Consequently there would be a nonzero polynomial \(Q\) of degree at most one such that \(I(F_0 Q R)=0\) for every \(\deg R\le4\). Writing \(F_0=X F_{\mathrm{int}}\), where \(F_{\mathrm{int}}\) is the product over the four interior sites, shows that \(Q\) cannot be constant, by taking \(R=F_{\mathrm{int}}\). It follows that the degree-five monic orthogonal polynomial for \(X\,dX\) would contain all four fixed interior sites, in particular \(1/2\).

This is impossible. Multiplying that degree-five polynomial by \(X\) gives a linear combination of the shifted Legendre polynomials of degrees six and five, with coefficient one on the monic degree-six term. At \(1/2\) the degree-five term vanishes by reflection and the degree-six term is nonzero because its roots are simple and it is reflection-even. This contradiction proves all free-site cofactor gates.

## The order-nine midpoint witness

Take the four fixed ladder sites \(0,2/7,4/7,6/7\) and the first three head sites \(-1,-2,1/2\), followed by the solved \(z\) before the fixed ladder. Work with \(Y=14X\); the seven unsolved coordinates in \(Y\) are \(0,4,8,12,7,-14,-28\). The following hand certificate modulo 19 gives the required nonvanishings. Use \(\int Y^j=14^j/(j+1)\), whose residues for \(j=0,\ldots,9\) are
\[
                 1,7,2,2,11,8,1,17,11,17 .
\]
The unsolved hull has coefficients, in ascending order,
\[
                         0,13,5,10,15,4,11,1 .
\]
Its three moments are \(4,12,2\) modulo 19, so the solved coordinate is \(3\) modulo 19 and the determinant is \(16\). It is different from the seven fixed residues. The completed hull has coefficients
\[
                         0,18,17,13,3,3,9,8,1 .
\]
For its eight roots the cofactor integrals are as follows; synthetic division and the displayed moments give every entry.
\[
 \begin{array}{c|rrrrrrrr}
 {\rm root\ mod}\ 19&0&4&8&12&7&5&10&3\\ \hline
 \int F/(Y-{\rm root})\ {\rm mod}\ 19&14&7&11&4&1&6&17&4
 \end{array}
\]
All are nonzero. The original integral and solved rational node reduce legitimately, since the given initial denominators and \(D\) are units modulo 19. Thus these formulas specify an exact rational degree-eight scalar rule with a degree-nine defect. No original order-nine literal fixture is reused or rerun.
