# A first-provider exclusion at paid degree seven

Work over a field with the relevant factorials paid (for example when \(14!\) is a unit). Use degree \(j=|t|-1\). Suppose the degree-seven model is separated, as it is at ordinary order at least 14 or retained Beta size at least 14. Assume the established strict pure growth, the paid midpoint floor \(\dim F_5\ge5\), and the paid actual ordinary order-seven stage floor of nine. No ordered-field hypothesis is used.

**Claim.** If \(\dim F_7\le7\), then \(\dim F_3=2\). If in addition \(\dim F_4=4\), the rank-two \(F_3\) is contained in the clock-invariant core \(U\) of the one-head flag from degree four. Thus \(\dim F_3\ge3\), or a nonzero level-three head in the level-four flat flag, forces \(\dim F_7\ge8\). For an ordinary order-15 tableau it supplies the conditional paid stage floor of 23. No unconditional table improvement is asserted.

The established separated \(\dim F_5\ge5\) and strict growth force the dimensions \(5,6,7\) at levels 5 through 7. The paid invariant-core lower rent \(\dim F_{r+1}\ge\dim U+\lfloor(r+1)/2\rfloor\) for any clock-invariant \(U\subset F_r\) implies noninvariance at levels 5 and 6. At level seven use the invariant endpoint rent \(\dim F_7\ge\lceil3(7)/2\rceil-3=8\) if the full space were invariant. Thus, when \(\dim F_4=4\), the flag from 4 through 7 is a one-head flag; \(F_4\) itself cannot be invariant since this rent would give \(\dim F_5\ge6\). Its retained head satisfies the interpolation hypotheses of the one-head multiplier argument.

## The first case: \(\dim F_3\ge3\)

Strict growth through the cap gives \(\dim F_3=3,\ \dim F_4=4\), and the paid invariant-core rent makes \(F_3\) noninvariant. We therefore have a one-head flag beginning at level \(a=3\), with invariant core dimension at most two. Its generator \(f\in F_3\) has actual nonzero polynomial head profile of degree at most three, since the endpoint level seven pays its product with the base. The first nonzero clean clock gives an actual order-seven provider, and its first primitive condition rules out a monomial profile. Put \(u\coloneqq\dim U\) and \(h\coloneqq3-u\); the initial head may have length more than one. The proof of the [first-provider lemma](FIRST-CLEAN-PROVIDER-AND-RESIDUE-RENT.md) still applies with the following degree change. At degree five the pure head polynomial \(S_1\) has degree at most \(h+1\), so all preceding head clocks are zeros of
\[
 B_1(X)\coloneqq J(XP)(X)+P(X)S_1(X),\qquad \deg B_1\le d+h+1,
 \quad d\coloneqq\deg P.
\]
The multiplicity argument in that lemma still gives \(B_1\ne0\): otherwise \(P\) divides \(J(XP)\), which is impossible for the nonmonomial \(P\). There are at most \(d+h+1\) preceding head rows, at most \(u\) core pivots and one clean origin. This gives at most \(u+1+d+h+1=d+5\le8\) predecessors, contradicting the ordinary lower bound of nine. Lower pure growth gives \(\dim F_3\ge2\), so the remaining case has exactly two.

## The second case: \(\dim F_4=4\), with a level-three head direction

Write
\[
 F_{4+k}=U\oplus w\,P_{<h+k}(\mathbf c),\qquad
 0\le k\le3,\qquad h\coloneqq 4-\dim U .
\]
The paid degree-two Gram exit puts the nonzero stage residual \(A\mathbf c-\mathbf c^{\odot2}/2\) in \(U\). Hence \(h\le3\). Suppose some \(f\in F_3\) has a nonzero head component \(T(C)w\). The inclusion \(CF_3\subset F_4\) and enough distinct effective labels imply \(\deg T\le h-2\), so \(h\ge2\). The level-three root product sends \(D_fF_4\) into \(F_7\). The previous one-head multiplier argument gives \(D_fU\subset U\), and on a joint-invariant complement the profile satisfies \(D_f\bar w=P(C)\bar w\) for \(\deg P\le3\). Here \(P\ne0\): the projection of \(f\) is \(T(C)\bar w\ne0\); at any complement coordinate with this value nonzero the raw \(f_i\) is nonzero as well, since the projection is obtained within a joint \((c,f)\) block where \(f\) is constant.

Chronologically compress on \(E_7\), then choose its three or fewer joint-block core pivots as in the first-provider theorem. Use a (not necessarily normalized) nonpivot contrast \(\lambda_i\) that kills \(U\) and uses only its own joint \((c_i,f_i)\) block up to physical index \(i\). At each read put
\[
 \rho_i\coloneqq\lambda_i\mathbf1,\qquad
 \omega_i\coloneqq\lambda_i w .
\]
Its effects on model and head monomials are given by \((\rho_i,\omega_i)\), and this pair is nonzero by full raw span. The relations
\[
 f_i\rho_i=T(c_i)\omega_i,
 \qquad
 \omega_i\ne0\ \Longrightarrow\ f_i=P(c_i)
\]
follow from the joint block and the actual head relation. Thus if \(T(c_i)\ne0\), then \(\rho_i\ne0\). Such a read is either clean (\(\omega_i=0\)) or, after normalization, has \(\omega_i/\rho_i=P(c_i)/T(c_i)\). The nonzero \(T\) has degree at most one. At its possible root, a head read with \(\rho_i\ne0\) has \(P(c_i)=0\); head reads with \(\rho_i=0\) are allowed. No independence is assumed merely because the physical coordinate names differ.

Call a nonzero-clock clean read a nonzero numerical combination of nonpivot contrasts supported at one nonzero clock, normalized to \(\rho=1,\omega=0\). Contrasts within a clock are independent as rows, hence their pairs \((\rho,\omega)\) are independent there, since any dependence would annihilate all of \(E_7\). There can be at most two; if there are two, they give a clean combination at that clock, available by their second physical index. At the clock zero the literal origin is one clean read and at most one further head is possible.

There is a nonzero-clock clean read. Otherwise the contrast \(C(P(\mathbf c)-f)\) annihilates all nonpivot evaluations: it vanishes at clock zero, on heads it vanishes by the displayed relations, and there are no other clean reads. Subtracting its core-pivot interpolation would thus make it zero in the whole raw system, contradicting its nonzero separated model \(XP\).

Let \(i_1\) be the earliest index allowing a nonzero-clock clean read, with normalized combination \(\lambda_*\) at clock \(\xi\ne0\). Before \(i_1\), every nonpivot besides the clean origin is a head, with distinct clocks among these heads. Apply the same core-pivot correction to
\[
 \mathbf z_k\coloneqq C^k(P(\mathbf c)-f),\qquad k=1,2,3.
\]
It agrees on every numerical coordinate before \(i_1\) with some \(\mathbf u_k\in U\). Strict chronology gives \(\lambda_* A(\mathbf z_k-\mathbf u_k)=0\). The normalized \(\lambda_*\) kills all \(F_7\) and gives its nominal time at \(\xi\), so
\[
 J(X^kP)(\xi)=0\qquad(k=1,2,3).
\]
Ordinary strict truncation, with each matrix and output scaled by \(\xi^{-1}\), makes \(\lambda_*A\) an actual order-seven provider. It is supported before \(i_1\) even if \(\lambda_*\) itself uses two earlier/same-clock contrasts.

The three moments show \(P\) is a cubic with three distinct nonzero roots in an algebraic closure. One direct check sets \(\xi=1\) by dilation and takes \(H=J^3(XP)\). This nonzero polynomial is divisible by \(X^4(X-1)^3\) and has degree at most seven, so its quotient is a nonzero constant. Thus \(P\) is proportional to \(35X^3-60X^2+30X-4\). Its value at zero is nonzero. Its derivative, up to the paid factor 15, is \(7X^2-8X+2\). Subtracting \(5X\) times that quadratic from the cubic gives \(-4(5X^2-5X+1)\); the combination of these two quadratics with coefficients \(7,-5\) gives \(5X-3\), where the first has value \(-7/25\). No common root is possible. These integer divisions are all paid in the stated range.

For each preceding head \(\lambda_i\), strict chronology also gives \(\lambda_i A(\mathbf z_1-\mathbf u_1)=0\). The expression has model \(J(XP)\) and pure part in \(F_5\), so some \(S\) of degree at most \(h\) satisfies
\[
 \rho_i J(XP)(c_i)+\omega_i S(c_i)=0 .
\]
Every such preceding head label is a root of
\[
                    B(X)\coloneqq T(X)J(XP)(X)+P(X)S(X).
\]
This follows by ordinary normalization off the root of \(T\). At a root of \(T\) with \(\rho_i\ne0\), it follows from \(P(c_i)=0\). At a root with \(\rho_i=0\), it follows from \(\omega_i\ne0\) and hence \(S(c_i)=0\).

The polynomial \(B\) is nonzero. Otherwise \(P\mid T J(XP)\). At least two of the three distinct nonzero roots of \(P\) are not roots of the at-most-linear \(T\). The primitive \(J(XP)\) would need a double root at both (its derivative already vanishes there), and also at zero. Its degree is five, making this impossible. Finally
\[
                 \deg B\le 3+h .
\]
Indeed \(\deg S\le h\), while \(\deg T\le h-2\) and \(\deg J(XP)=5\). The actual width before \(i_1\) is consequently at most
\[
 \dim U+1+(3+h)=8 .
\]
The terms are the core pivots, the clean origin, and at most \(\deg B\) earlier distinct head labels. This contradicts the paid ordinary order-seven stage floor of nine and completes the strict subcase.

The argument uses an actual localized clean read and degree budgets, not classification of coefficient arrays. The rank-two case with \(F_3\subset U\) is not resolved by this proof: at level seven the cost-four generator need not have a known polynomial profile, because its square has cost eight.
