# Literal silent two and three are impossible in the regular star–star chart

Work at the ten-stage strict SDIRK8 floor over a characteristic-zero field in the [constant reverse-live nine-site chart](../sdirk-eight-silent-one-eight-reverse-live-constant/README.md). Physical one is the sole nonzero quadratic-defect stage and has zero ordinary weight; eight ordinary sites are distinct, and the other ordinarily silent row has an actual nonzero reverse read at a separate clock. Assume genuine quintic cubic-defect profile, non-Gauss literal front, nonzero regular fourth-anchor coefficient, star front and star rear. This packet excludes both **actual silent physical two and actual silent physical three**. The [silent-fourth result](../sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed/README.md) is separate. Together they exclude the three literal silent placements for these two star phases, neither the nonliteral placements nor the other phases. The unrestricted interval remains **10–11**.

## Actual exchange, and the identically zero centered relation

The actual star-front normalized clocks are \(A_0=2+2t\), \(B_0=2-2t\), \(2t^2=1\), with the two corresponding known cubic amplitudes. The actual tap from physical two to physical three is **zero** in this phase, not a free coefficient. Their transposition preserves strict triangularity: the only order-reversed off-diagonal slot between distinct stages is this zero tap. Simultaneous permutation of rows, columns, and weights preserves the rooted elementary reads by induction, and hence the order. It also permutes ordinary and actual reverse weights, leaves physical first, fourth, and rear stages in place, and preserves the nine-site data. Under this transposition \(t\mapsto -t\). The replay checks the exact conjugation of both fourth projected polynomials and both centered tail coefficients, the invariance of the cleared cubic profile, and the change of sign (not vanishing) of the regular anchor \(V\). Thus it is sufficient to analyze physical two without assuming an unlicensed exchange of two coupled stages.

Write \(x=1-\gamma,\ m=1-2\gamma\), the true rear pair \(m\mp\gamma v\), \(w=v^2\), and the cleared centered relation \(A+B w=0\). If \(A=B=0\), use the [exact highest and next centered coefficient identities](../sdirk-eight-silent-one-eight-reverse-live-star4-zero-tail/README.md). Those force the same degree-five diagonal polynomial, regardless of which literal is silent. The actual fourth retains its full cubic equation after its two exact earlier padded roots. The actual affine reverse root is now \(z=\gamma A_0\) or \(\gamma B_0\), according to the chosen actual silent placement. Using the even average of the two ordinary rear reads gives the full gap quadratic with leading coefficient \((x-z)h_4\), true nonzero because \(h_4=-h_5\ne0\) in this branch, and the actual terminal is distinct from the literal silent. The five known ordinary pegs are the *other* literal, the actual fourth, terminal, and the two rear pegs. At \((1129,t=203)\), in both silent placements, all three monic diagonal components of degrees \(1,1,3\) preserve the actual cubic and quadratic leading units. Their full five-peg Padé determinants are units. No actual fifth or sixth hypothesis is required for \(A=B=0\).

## Exact quadratic-coefficient diagonal projection by bounded CRT

For the remaining \(B\ne0\) branch the [regular projections](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md) give the two actual fourth polynomials \(P,Q\) in \(\mathbb Q(t)[\gamma,s]\), \(s=c_4/\gamma\). The true homogeneous scales and literal collisions were accounted for in constructing them. Their exact bidegrees \((\deg_s,\deg_\gamma)\) are \((9,29)\) and \((26,79)\). Their symbolic \(s\)-resultant has \(\gamma\)-degree at most \(9\cdot79+26\cdot29=1465\).

Put \(z_0=2t\), so \(z_0^2=2\). Clear rational denominators and divide nonzero integer contents of \(P,Q\), obtaining exact primitive representatives in \(\mathbb Z[z_0][\gamma,s]\). On coefficient pairs use \(|a+bz_0|_* = |a|+2|b|\), and on polynomials sum these norms over monomials. It is submultiplicative since \(z_0^2=2\). Bounding the determinant expansion by the product of Sylvester row norms gives \(\|P\|_*^{26}\|Q\|_*^9\) as an integer bound for the absolute value of each coefficient in either of the two exact coordinates of the resultant. The replay computes this bound (4154 bits); it is not a bound inferred from stabilization.

For each distinct verified prime in the replay take both simple residue roots of \(z_0^2=2\). Retain true degrees 9 and 26 in both input specializations, then compute the two residue \(s\)-resultants. Their sum and difference recover the two coefficient coordinates modulo that prime. Pad to the exact \(\gamma\)-degree bound, so possible reductions of the \(\gamma\)-degree do not discard coefficients. Integer CRT stops at the first product greater than twice the coefficient bound (70 primes). The centered representatives are therefore the unique exact integer coefficients. An independent small split at 1559 also replays both coordinates. This certifies exact resultant degree 1465 and an exact common factor \(\gamma^{265}\) of the two coordinates. It is legal to divide by that factor and a nonzero integer content because an actual strict diagonal is nonzero. Write the resulting necessary polynomial as \(J=U+z_0V_0\), with \(\max(\deg U,\deg V_0)=1200\).

Any true diagonal must satisfy the rational norm \(U^2-2V_0^2=0\). Its degree is 2400, and the complete product of its exact rational factors is checked before any local tests. For the three rows marked as smaller orientation degree below, intersect the rational factor with \(J\) by an exact polynomial gcd over \(\mathbb Q(t)\). All other rows keep the entire rational factor, even if it includes the conjugate orientation too. Using the norm does not by itself exclude any characteristic-zero candidate.

## Exact physical guards and the independent actual fifth

For each exact diagonal factor first specialize the true fourth polynomial \(P\) and guards in the full exact coefficient quotient. Where indicated, remove the exact gcd with that guard from \(P\), repeating the division to account for multiplicities; then normalize the retained \(P\) monic. At a true candidate these guards are nonzero:
- The normalized profile scale \(\delta\) is the actual nonzero regular profile scale after exact division of the already nonzero \(\gamma,L_4(a),L_4(b)\), where \(a=\gamma A_0,b=\gamma B_0\).
- The actual ordinary terminal defect \(H_*(x)\ne0\) follows from the exact deflated pointwise identity, and a genuine quintic has nonzero highest coefficient.
- The normalized \(B\ne0\) is the separate branch considered here. If \(A+2B=0\), then \(w=2\) and \(k=0\), impossible.
- The actual clock \(a\) is ordinarily silent in this representative but is a distinct **reverse-live** site. Therefore \(x-a\ne0\), and \(B(a-m)^2+\gamma^2 A\ne0\), the latter excluding collisions of \(a\) with either physical rear peg.

| Exact norm degree, multiplicity | Orientation degree kept | Actual exact guard | Removed fourth degree |
|---|---:|---|---:|
| \(326,1\) | 326 | none | 0 |
| \(24,3\) | 12 | \(\delta\) | 3 |
| \(2,6\) | 1 | \(x-a\) identically zero | whole orientation |
| \(18,6\) | 9 | rear collides with \(a\) | 3 |
| \(27,12\) | 27 | \(H_*(x)\) | 3 |
| \(4,14\), \(2,15\) | 4, 2 | \(\delta\) | 3 each |
| \(1,20\) | 1 | rear collides with \(a\) | 3 |
| \(21,48\) | 21 | quintic leading coefficient | 3 |
| \(1,48\) | 1 | \(B\) | 6 |
| \(4,54\) | 4 | \(A+2B\) identically zero | whole factor |
| \(3,60\) | 3 | \(B\) | 2 |

The actual independent fifth constraint uses the same [cleared literal determinant](../sdirk-eight-silent-one-eight-reverse-live-star4-regular-closed/README.md) with the actual earlier clocks \(A_0,B_0,s\). The earlier ordinarily silent literal keeps its true nonzero cubic read. The known pegs now fold as
\[
 E^\#(X)=(X-b)(X-\gamma s)(X-x)\bigl(B(X-m)^2+\gamma^2 A\bigr).
\]
Any actual \(B\ne0\) solution satisfies \(E^\#=BE\) where \(E\) is the true monic ordinary five-peg nodal. The four choices of missing-cubic cofactor give padded fifth resultants without dividing by \(B\) or an actual coefficient pivot. The actual fifth is ordinarily weighted and belongs to the missing cubic, so all these resultants are necessary. No unknown actual fifth node is reduced at the test prime.

After the exact guard division, retain the full monic fourth fiber. The degree-326 row needs no supplementary guard: at least one complete original fourth degree is retained in all nine reduced components. At \((1129,t=203)\), for each retained gamma factor and every one of its reduced irreducible components, intersect the complete actual fourth equations and all four necessary fifth cofactor resultants. Every intersection is empty. No component is discarded for a residue-only zero of a guard. Whole-factor contradictions in the table are exact over characteristic zero. The remaining full degree-preserving finite local unit tests then certify characteristic-zero impossibility, not a statement about reducing unknown tableau coefficients.

## Replay and native scope

Install sympy==1.14.0 and python-flint==0.9.0 and run **python3 check_star23_regular_closed.py** with the stated sibling folders. It builds and checks the exact bounded CRT resultant, norm factor product, both identically zero tail placements, and the complete nonzero-tail orientation fibers. No data file or prior machine state is needed. The [native file](../../lean/RKCert/ReviewedNative/SDIRK8EightActiveLateralStarReads.lean) checks the uncoupled adjacent exchange, its triangularity condition, and the norm/CRT scalar identities on Lean/Mathlib 4.36.0. Tableau saturation, exact projections and the arithmetic replay remain source-level.
