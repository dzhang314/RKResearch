# The terminal-new A2 corner of two-singleton front versus rear D,S,S arithmetic is impossible

Assume a strict ten-stage SDIRK tableau has ordinary order at least eight over a characteristic-zero field, all ten physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton endpoint. Its first three rows in the actual orientation from the singleton cannot be S,D,S with true arithmetic while the opposite opening is D,S,S with true arithmetic, when the two observed D clock labels are distinct. The [reused-terminal](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-reuse/README.md), [terminal-new front star](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md), and [terminal-new A3](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a3-front/README.md) packets cover the other phases. The [scoped ledger](LEDGER.md) records the resulting unique-singleton-end chronology restriction. This is **not** a general ten-stage exclusion or 10–11 interval update.

## Actual rows, exact ingress and the swapped projection

Use the full [A2 ingress](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a2-ingress/README.md). The true normalized clock coordinates are \(0,d,s=2d\) at the front and \(H,p=H-v,q=H-2v\) in original coordinates from the rear, with \(d\ne H\). Their measured original or reverse-normalized residuals are those of their own genuine arithmetic phases, including the nonzero third tap. Their actual first-departure, distinctness, nonzero defect, and parity guards are retained. The measured affine factor of the cubic \(M_3=L R\) from the two true S readings \(0,s\) recovers the graph \(R=1/2+a y+b y(y-s)\) with true \(b\ne0\) and the third D label. This recovery uses neither \(f_s-1/2\) nor a ratio or remainder leading coefficient as a pivot. It therefore includes the genuine half-amplitude and \(v=2\) shapes, even though [two independent special checks](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a2-ingress/SPECIAL.md) also exclude them.

The exact guarded integer rows \(E,\mathcal R,\mathcal N,\mathcal X,\mathcal Y\) from that ingress are respectively the quadratic-coefficient gate, actual rear graph ratio, four-singleton nodal minor, paid S value, and paid terminal D fit. Their degree triples in \((H,d,v)\) are
\[
 (18,18,0),\ (10,11,3),\ (22,26,2),\ (16,17,8),\ (26,27,8).
\]
The nonzero first projection \(\Pi=\operatorname{Res}_v(\mathcal R,\mathcal N)\), after stripping only true nonzero guards independent of \(v\), has degree pair \((84,100)\) in \((H,d)\). Instead of a large \(\operatorname{Res}_d(E,\Pi)\), compute \(\operatorname{Res}_H(\Pi,E)\). The target is an exact polynomial in the paid front gap \(d\). This swap does not imply any leading coefficient is a unit at a specialized root.

## Fraction-free exact resultant up to a rational scalar

View \(A=\Pi\) and \(B=E\) as polynomials in \(H\) over \(\mathbb Q(d)\), with integer polynomial coefficient representatives. Work with dense coefficient polynomials in \(d\). One cancellation step takes \(g=\gcd(\operatorname{lc}_H A,\operatorname{lc}_H B)\), performs
\[
       A'=\frac{(\operatorname{lc}_H B/g) A
                   -(\operatorname{lc}_H A/g) H^k B}{c}
\]
with the usual matching \(H\)-degree shift \(k\), and divides by the exact coefficient content \(c\ne0\) of the numerator. Repeat until the \(H\)-degree is below that of \(B\). These are operations in a formal coefficient field, not specialized divisions in an unknown mesh. Log the products \(\alpha\) of the step factors \((\operatorname{lc}_H B/g)/c\), so that the final primitive remainder \(R_0\) satisfies \(R_0\equiv\alpha A\bmod B\).

For degrees \(m=\deg_H A\), \(n=\deg_H B\), \(r=\deg_H R_0\), the root-product identity, with roots of \(B\) counted with multiplicity, gives
\[
  \operatorname{Res}_H(A,B)
   =(-1)^{mn}\operatorname{lc}_H(B)^{m-r}\alpha^{-n}
                      \operatorname{Res}_H(B,R_0).
\]
For the final \(H\)-constant \(B\) the resultant is \(B^{\deg_H A}\). Accumulate the powers of coefficient polynomials in \(d\) using an exact gcd-refined square-free, pairwise coprime basis. This avoids expanding the large artificial contents of intermediate pseudoremainders. After cancellation all surviving powers are positive; only nonzero numerical rational factors, including the overall sign, are irrelevant to root support. Thus the result is the **ordinary exact polynomial resultant up to a nonzero rational scalar**, and covers specialized degree drops without treating any pseudoremainder divisor as a true physical guard. The source also compares the accumulated product against ordinary exact integer resultants at three degree-preserving integer substitutions as an independent arithmetic check, not as the proof of polynomial equality.

The exact full swapped resultant has degree 3066. Remove only true nonzero factors depending on \(d\) alone, after exact cancellation, leaving degree 1660, with irreducible degree/multiplicity pairs
\[
 \begin{gathered}
 (1,192),(3,30),(3,60),(4,1),(8,3),(8,16),\\
 (16,3),(24,3),(36,8),(48,3),(134,1),(356,1).
 \end{gathered}
\]
These are twelve actual rational irreducible support factors, not unlifted modular factors.

## Complete fibre exclusion

| Degree, multiplicity of \(d\) factor | Certificate | Prime | \(d\) residue | Entire \(H\) test at this residue |
| --- | --- | ---: | ---: | --- |
| 1, 192 | exact static trim | 11 | 10 | unit anchor gcd |
| 3, 30 | direct | 13 | 3 | \(11\) |
| 3, 60 | direct | 17 | 4 | no anchor root |
| 4, 1 | exact static trim | 23 | 12 | unit anchor gcd |
| 8, 3 | direct | 101 | 67 | \(11\) |
| 8, 16 | exact static trim | 103 | 37 | unit anchor gcd |
| 16, 3 | direct | 17 | 15 | \(3\) |
| 24, 3 | direct | 29 | 25 | \(22\) |
| 36, 8 | exact static trim | 31 | 10 | unit anchor gcd |
| 48, 3 | direct | 101 | 52 | \(47\) |
| 134, 1 | direct | 31 | 7 | \(17\) |
| 356, 1 | direct | 11 | 7 | \(4\) |

For each row the chosen \(d\) residue is simple for its irreducible factor and the leading coefficient is a unit. Hensel gives an embedding of the abstract \(d\)-field into \(\mathbb Q_p\). In a **direct** certificate, the verifier computes the actual degree of \(E\) in \(H\) over that abstract field by exact reductions of its coefficient polynomials modulo the \(d\) factor. The degree is 18 except for degree-3 multiplicity-60, where it is 15. It is positive and survives at the chosen place; hence a putative \(H\) is algebraic and integral after extending the embedding. The joint reduced \(H\)-gcd of \(E,\Pi\) has its entire root set listed in the table, with total multiplicities checked. For every such \(H\) reduction, at least one of the four genuine \(v\)-rows retains full nominal positive degree, forcing \(v\) algebraic and integral. Their joint reduced gcd is a unit, so no residue component can lift. No assumption is made that an original physical clock guard stays nonzero modulo the chosen prime: the four rows are already integer necessary equations over characteristic zero and are evaluated as such even at a guard-zero residue.

In an **exact static trim**, work first over the entire irreducible \(d\)-field. Regard \(E\) as a polynomial in \(H\), remove only factors of true nonzero guard polynomials, and normalize the retained factor to monic. The four operations use:
- the nonzero normalization parameter \(m\), trimming \(E\) from degree 18 to 12;
- the genuine nonzero \(M_3(0)\), trimming 18 to 17;
- the two paid D Legendre values \(L_4(H),L_4(d)\), trimming 18 to 16;
- the exact common divisor of the nonzero affine slopes of \(F_*\) and \(L\) over the degree-36 field. It has degree one in \(H\), and trims 18 to 17.

All other factors of \(E\) are retained. Their monic polynomial has integral coefficients at the chosen \(d\)-place as certified by exact reduction in its algebraic field. Its reduced gcd with \(\Pi\) is a unit. This is a true anchor contradiction, not deletion of a singular-looking point after reduction. Together the eight direct and four trimmed certificates exhaust all swapped factors over arbitrary characteristic-zero fields, including non-real or nonsplit graphs. No conclusion for finite-characteristic tableaux, ordered sign strata beyond the stated hypotheses, or other clock counts is inferred.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_final_a2.py` (SymPy 1.14 and python-flint 0.8). It regenerates the exact ingress, swapped projection, primitive cancellations, irreducible factors, and all fixed places from source, with no saved projection tables or prime sweep. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDssArithmeticA2Final.lean) checks the primitive-step and true-nonzero-guard scalar implications. The full tableau proof, resultant recurrence, exact algebra, and field-transfer argument are mathematical with exact replay, not an end-to-end native Lean theorem.
