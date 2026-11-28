# DIRK12/15: both singular rational profiles are impossible

For real ordinary order-twelve DIRK in fifteen physical stages with \(C(2)\), \(f_5=3\) and **true reverse pure grade-six rank four**, the genuine cubic \(\mathbf h=A\mathbf c^2-\mathbf c^3/3\) must satisfy \(\mathbf b\odot\mathbf h=0\). Indeed the [high uniform chart](../dirk12-fifteen-rank3-uniform-chart-exclusion/README.md) was already closed. The [rational reduction and census](../dirk12-fifteen-rank3-rational-profile-census/README.md) excluded coprime denominators and left two singular profiles, both excluded below.

This is a complete **visibility restriction on this rank-four equality face**, not exclusion of fifteen stages. In particular the weighted-invisible face, the reverse-rank-five faces (including the four cancelling dirty labels), and the other \(f_5\) or \(C(2)\) cases are not removed. The real stage interval remains **15–16**.

## Geometry and genuine grades used

Write \(T_j,F_j,\mathcal B_j\) for the actual rooted stage span, pure forward span, and true scalar weighted reversed flag, with grade equal to tree order minus one. Let \(\beta\mathbf v=\mathbf b\odot\mathbf v\). In every remaining singular profile all fifteen weights are live. There are exactly three actual clean rows (the literal endpoints and one interior); all \(F_6\) and \(\mathcal B_6\) vanish there. In particular the clean primitive discrepancies through scalar input degree five vanish in both directions. The actual diagonal of the lone clean interior is nonzero, as already certified in the census from the fixed profile \(D/(X-u)\) at its clock \(u\) and the clean grade-six primitive. This applies to its reflected value too, since actual transposition does not change a diagonal. Here \(D=L'_6\) has five simple interior roots and \(D(1-X)=-D(X)\).

Ordinary and weighted reversed grade-\(j\) pure corrections through grade five are exactly \(\mathbf h P_{j-3}(\mathbf c)\) and \((\beta\mathbf h)P_{j-3}(\mathbf c)\) for \(3\le j\le5\), and the reversed flag stays in that form at grade six. For a scalar profile \(S\) and a pure correction \(\mathbf h Q\), an actual primitive raises the grade by one and changes the scalar profile to \(JS=\int_0^X S\) in that direction's clock variable. A genuine pair is used in the actual physical triangular array in its own direction (ordinary \(A\) or weighted reversed \(A^{\mathsf T}\)); no full normalized transposed method is asserted. In reversal the vector is multiplied by \(\beta\), and a nonzero local weight is canceled only after retaining the genuine flagged discrepancy.

In the **one-shared-root** profile, the clean clock \(u\) is the single shared root of \(D,T\), and on the twelve live dirty rows, at distinct labels, \(h=U/V\) with \(U\) a nonzero scalar multiple of \(D/(X-u)\) and \(V\) of degree at most one. This applies also at a normal dirty row numerically at \(u\), when one exists. \(V\) does not vanish at any live dirty row, nor at any root of \(U\). If \(V(u)=0\), there is no dirty row at \(u\). The census gives five to seven dirty rows on each side of the clean pivot.

In the **two-shared-root** profile, write \(d\) for the anomalous clock in the reflected direction and \(u\) for the distinct clean interior clock. The nine normal dirty rows have the regular cubic \(W\), a nonzero scalar multiple of \(D/[(X-d)(X-u)]\). The three further dirty rows at \(d\) have different nonzero amplitudes, each unequal to \(W(d)\). Exactly one is before the clean pivot in reverse chronology and two after it. The normal dirty counts are four and five on the two sides, in some order. There is no normal dirty row at \(d\), although a normal dirty row may share the numeric clean clock \(u\). All statements this packet makes before the pivot include any placement of the lone reverse anomaly among that actual prefix.

## First finite receipt: rule out the shorter prefix

In either of two settings, use the **actual earlier physical prefix** of the lone clean interior:

- one-shared-root: exactly five dirty rows in the chosen direction, plus its literal origin;
- two-shared-root: exactly four normal dirt plus the lone reverse anomaly, read only in the reverse direction, plus its literal origin.

In either setting the seven coefficients of a grade-four scalar-and-correction input \(S-\mathbf h Q\), \(\deg S\le4,\deg Q\le1\), leave a nonzero contrast through the six physical conditions on the earlier prefix. Its scalar profile cannot be zero: a pure affine polynomial vanishing numerically at at least two distinct live dirty labels is zero. Its first nonzero coordinate cannot be the clean pivot \(u\): the true grade-six commutator would be \(-A_{ii}^2 S(u)\) there, but the clean grade-six output is zero and the known diagonal is nonzero. Thus \(S(u)=0\). The input is then zero including the pivot; its primitive and its primitive after one clock multiplication force \(JS(u)=J[XS](u)=0\) in grades five and six. We also have \(S(0)=0\). These conditions leave the unique nonzero scalar profile up to scale
\[
                     H=X(X-u)(X^2-uX+u^2/5).
\]
Indeed the remaining quadratic is orthogonal to degrees at most one for \(X(u-X)\,dX\) on \([0,u]\).

In the one-root case, \(VH-UQ\) is of degree at most five and zero at the five earlier dirty labels. It is not identically zero: coprimality gives \(U\mid H\) in that case, impossible since \(H(0)=0\), \(U(0)\ne0\), and both are quartics. Thus it is a nonzero multiple of the actual five-root hull. The genuine primitive of the contrast is zero at those same earlier rows. Its degree-five discrepancy is \(hR_2\), so \(VJH+UR_2\) is also divisible by the same hull, with quotient affine. At every root of \(U\), \(V\ne0\), so the three evaluations \(JH,H,XH\) are linearly dependent on any three selected roots. This holds in either physical direction; in reversal the same legitimate weighted profiles are used.

In the two-root case, \(H-WQ\) has degree at most four and is zero at the four earlier normal labels. It is not identically zero: an affine \(Q\) in such an identity would vanish at zero and \(u\), where \(W\ne0\). It is a nonzero multiple of the actual four-root normal hull. The same genuine grade-five primitive now gives \(JH+WR_2\) divisible by that hull, with quotient affine. At the three roots of \(W\), this gives exactly the same dependence of \(JH,H,XH\).

The first receipt asserts that for every root \(u\) of \(D\) and every choice of three other roots \(z_i\),
\[
                       \det\bigl[JH(z_i),\,H(z_i),\,z_i H(z_i)\bigr]_{i=1}^3
                                  \ne0.
\]
It is an undivided determinant test; no assumption on an arbitrary value \(H(z_i)\) is needed. This closes **both** asymmetric splits 5/7 and 7/5 in the one-root case (exactly six dirty on each side survives), and closes four normal predecessors in the reverse direction of the two-root case (exactly five reverse normals survive).

## Common four-node obstruction

Use actual **reverse** chronology for both remaining splits. There are eight physical rows through the clean interior inclusive: origin, six actual dirty rows, and the pivot itself. In the two-root case the six include the singleton anomaly and five normals; its location among them is unrestricted. Pick a nonzero true grade-five scalar-and-correction contrast \(S-\mathbf h Q\), \(\deg S\le5,\deg Q\le2\), weighted in reversal, vanishing on all eight rows. Nine coefficients and eight homogeneous constraints suffice. A pure polynomial \(Q\) must vanish on at least five distinct dirty labels, so \(S\ne0\). Thus
\[
                          S(0)=S(u)=JS(u)=0 .
\]
The primitive equality follows from a literal zero input including the pivot and the clean grade-six discrepancy there.

In the one-root case set \(U\) to the monic quartic \(D/(X-u)\) by scaling \(U,V\) together. The polynomial \(\Delta=VS-UQ\) has degree at most six and is zero on the six earlier dirt. If identically zero, \(S=UR\) with \(R\) affine, whose two roots at \(0,u\) force \(S=0\). Thus \(\Delta\) is a nonzero multiple of their actual six-root hull. Besides the chosen contrast, use the genuine grade-five masked clean profile \(X(U-\mathbf h V)\), supported on the three clean rows and numerically zero before the clean pivot in reverse. Its scalar profile is \(XU\). The true primitives of both contrasts are zero on the six earlier dirt. Their pure discrepancies are in \(\mathcal B_6=(\beta\mathbf h)P_3\). Hence the polynomials
\[
               V JS+ U R_3,\qquad V J[XU]+U R'_3
\]
are both divisible by \(\Delta\) (quotient affine). At the four fixed roots \(z\) of \(U\), \(V(z)\ne0\); we obtain two affine functions \(L,L'\) with
\[
                          JS(z)=L(z) S(z),\qquad J[XU](z)=L'(z) S(z).
\]

In the two-root case scale the cubic \(W\) and \(\mathbf h\) together so \(U=(X-d)W\) is the monic \(D/(X-u)\). Set \(\Delta=S-WQ\), degree at most five and zero on the five normal predecessors. If identically zero, \(Q(0)=Q(u)=0\) since \(S= WQ\) and \(W\) does not vanish at these two clocks, and the actual singleton anomaly equation \(S(d)=h_d Q(d)\) gives \(Q(d)=0\) because \(h_d\ne W(d)\). The three distinct roots force \(Q=0\), hence \(S=0\), contradiction. Thus \(\Delta\) is a nonzero multiple of the five-normal hull. Besides the first contrast, use the canonical true grade-five weighted mask \(X(X-d)(W-\mathbf h)\), with scalar profile \(XU\). Its actual inputs are zero strictly before the clean pivot, including at the anomaly. The two genuine primitive discrepancies again give affine quotients, now
\[
                  JS+W R_3=\Delta L,\qquad J[XU]+W R'_3=\Delta L'.
\]
At the three roots of \(W\), these give the two required affine ratios. At the singleton reverse anomaly \(d\), the actual input zero and its two earlier primitive zeros are
\[
                S(d)=h_d Q(d),\quad JS(d)=-h_d R_3(d),\quad J[XU](d)=-h_d R'_3(d).
\]
Therefore
\[
        h_d\Delta(d)=(h_d-W(d))S(d),\quad
        h_d\Delta(d)L(d)=(h_d-W(d))JS(d)
\]
and the same for \(L'\) and \(J[XU]\). Since \(h_d-W(d)\ne0\), the very same affine ratios hold **also at \(d\)**, completing the four nodes \(U=0\). This fourth-node transfer uses actual numerical zeros, not a divisibility assumption at the singular denominator. It works for every possible placement of the singleton anomaly before the clean pivot; no adjacent-pair purity or missing-gap claim is needed to remove the remaining chronologies.

## Second finite receipt and conclusion

Let \(K=\{z_1,z_2,z_3,z_4\}\) be the four fixed roots of \(U=D/(X-u)\), normalized monic. Define the cardinal profiles for the subspace of polynomials of degree at most five which vanish at \(0,u\):
\[
 E_j(X)=\frac{X(X-u)\prod_{k\ne j}(X-z_k)}
              {z_j(z_j-u)\prod_{k\ne j}(z_j-z_k)},\quad
 \lambda_j=J E_j(u),\quad \Gamma_{ij}=JE_j(z_i),\quad F_i=J[XU](z_i).
\]
These denominators come only from **distinct fixed roots**, never a chosen tableau pivot. In particular \(S=\sum_j S(z_j)E_j\). The exact replay verifies \(F_i\ne0\) and \(\sum_j\lambda_j F_j\ne0\) for all five possible \(u\). The latter and \(JS(u)=0\) prohibit constant \(L'\), because \(F=L' S\) and all \(F_i\ne0\). Therefore \(L'\) is affine nonconstant; after scaling \(S\) the relation can be written \(S(z_i)=F_i Q_i(\rho)\) where
\[
                  Q_i(\rho)=\prod_{j\ne i}(\rho-z_j),\qquad \rho\notin K .
\]
Here \(\rho\) is the zero of \(L'\); the common factors were absorbed into the normalization, possible because \(L'\) and every \(S(z_i)\) are nonzero at these four nodes.

The necessary moment \(JS(u)=0\) reads
\[
              H_u(\rho):=\sum_j \lambda_j F_j Q_j(\rho)=0.
\]
This has degree three with leading coefficient \(\sum_j\lambda_j F_j\ne0\). The second affine-ratio condition \(JS(z_i)=L(z_i)S(z_i)\) means the values
\[
               R_i(\rho)= (z_i-\rho)\frac{\sum_j\Gamma_{ij}F_j Q_j(\rho)}{F_i}
\]
are affine in \(z_i\): these are the true ratios multiplied by one common nonzero factor (up to sign). For every triple in \(K\), the corresponding determinant \(\det[1,z_i,R_i(\rho)]\) is a polynomial of degree at most four. The exact receipt verifies the degrees three and four are attained and their gcd is one modulo both 181 and 1013, for each of the twenty choices of \(u\) and triple. Thus there is no such \(\rho\). This closes both balanced singular cases and all earlier splits. Combined with the uniform exclusion, it proves the stated visibility restriction.

## Exact arithmetic and Lean scope

The dependency-free script **check.py** constructs each determinant, cardinal polynomial, and cubic–quartic pair directly. The quartic-profile determinants are nonzero at all three tested primes 43, 181, 1013. The complete fixed-four-node gcd receipt with unchanged degrees is verified at both 181 and 1013. For the degree-preserving gcd tests, take the rational symmetric product over all choices of labeled roots of the individual fixed-degree resultants (squaring factors or using both orderings to remove sign choices). The leading coefficient of \(D\), fixed clock differences, and all small integration denominators are units at these primes. Reduction of each resultant is nonzero, so the rational product is nonzero; no characteristic-zero common root is possible. The same symmetric product argument applies to the nonzero determinant and moment numerators. There is no inference of tableau clock values from modular roots.

The real rooted reduction and chronology arguments are mathematical. The portable **DIRKOrderTwelveFifteenSingularProfilesArithmetic** checks the fixed-grid quartic-profile determinants directly and the published cubic/quartic degrees and Euclidean gcds from expanded data modulo 181; it compiles on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1 with standard axioms only. The companion **DIRKOrderTwelveFifteenSingularProfilesDirect** independently recomputes all cardinal, quartic and gcd arithmetic in the Lean kernel on 4.36.0. The reviewed **DIRKOrderTwelveFifteenSingularAnomalyTransfer** checks the local affine transfer without canceling any factor except the actual mismatch, on Lean/Mathlib 4.36.0. Earlier actual rank, pure flag and chronology data have their own reviewed native partials.

    python3 -B check.py --expanded /tmp/dirk12-singular-expanded.json
    cmp receipts.json /tmp/dirk12-singular-expanded.json
    sha256sum -c sources.sha256

From **ai-generated/lean** in the pinned Lean/Mathlib environment:

    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenSingularProfilesArithmetic
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenSingularProfilesDirect
    lake build RKCert.ReviewedNative.DIRKOrderTwelveFifteenSingularAnomalyTransfer
