# Both singleton endpoints, two shared D labels, arithmetic/arithmetic

Assume strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, all ten literal quadratic defects nonzero, exactly seven distinct clocks and both physical endpoint clocks singleton. If both actual S,D,D openings are arithmetic, they **cannot share both of their doubled clock labels**. The other phase choices on two shared D labels have separate [star/star](../sdirk-eight-all-dirty-seven-quadratic-both-s-two-shared-stars/README.md) and [mixed](../sdirk-eight-all-dirty-seven-quadratic-both-s-two-shared-mixed/README.md) proofs.

## Actual order, Vieta, and an odd quintic

Normalize the common diagonal to one with \(y=x-1\) and endpoint labels \(0,H\), so the first two D labels in forward order are \(u,2u\). In the reflected coordinate \(H-y\), rear arithmetic on the same two labels forces opposite literal order: the same order gives \(H=0\), forbidden by distinct singleton endpoints, while opposite order gives \(H=3u\). In the original centered coordinate \(w=y-h,\ h=3u/2,\ d=u/2,\ m=h+1\), the shared D labels are \(-d,d\), and the endpoints are \(-h,h\).

Write \(f_1=\kappa(u)/2,\ f_2=N(u)/(2D(u))\) for the two paid original arithmetic defects, using the same \(\kappa,D,N\) as the [mixed packet](../sdirk-eight-all-dirty-seven-quadratic-both-s-two-shared-mixed/README.md#literal-clocks-and-a-single-paid-quintic). The actual normalized rear gap is also \(u\), and the original residual pairs at \(-d,d\) are respectively \((f_1,\lambda f_2)\) and \((f_2,\lambda f_1)\). Hence
\[
 \beta=B\lambda=-L_4(d)/(f_1f_2),\quad
 A_2(-d)=-B(f_1+\lambda f_2),\quad A_2(d)=-B(f_2+\lambda f_1).
\]
The true \(\lambda\ne0\) satisfies \(R(-h)=1/2,\ R(h)=\lambda/2\).

The antipodal shared pair makes \(F_*=b w\) in the [true projection](../sdirk-eight-all-dirty-seven-clock/README.md), with \(b=(d^2-3m^2/5)/L_4(d)\ne0\). This follows from odd/even parity and the true nonzero \(L_4(d)\); comparison of degrees then makes the slope nonzero. Its exact factorization is
\[
 Q_0=L_3-F_*L_4=-b w(w^2-d^2)(w^2-\eta),\qquad
 \eta=1/b+6m^2/7-d^2.
\]
The third actual D is either the center, or some \(e\ne0\) with \(e^2=\eta\). This split permits repeated graph roots or a graph root at an already observed D where compatible; it does not throw away \(\eta=0\) in the centered case.

## Noncentral third D

If the third D is \(e\ne0\), then \(R(w)=w(w+e)/(2h(h-e))\) and \(\lambda=(h+e)/(h-e)\ne1\). The two endpoints give \(A_2(-h)=2L_4(h)-B/2,\ A_2(h)=2L_4(h)/\lambda-B\lambda/2\). At the four equally spaced labels \(-h,-d,d,h\) the third finite difference of this actual quadratic is zero. Multiplication by \(2\lambda\) factors it as
\[
 (1-\lambda)\left[4L_4(h)+\beta(1+6(f_2-f_1))\right]=0 .
\]
The bracket gives the following irreducible degree-nine polynomial for the actual \(u\), after removing only nonzero tap and gap factors:
\[
81u^9-891u^8+3411u^7-4659u^6-733u^5+4378u^4+940u^3
     -992u^2-432u-48=0 .
\]

The fixed place \(p=23,\ u=5\) is a simple root of the full-degree gap polynomial. This embeds its abstract rational field into \(\mathbb Q_{23}\). The monic equation \(e^2=\eta\) is then integral and has both possible residues \(8,15\); the replay checks both, not just one sign. At either all used reconstruction denominators and the resulting \(\lambda,B\) are units. In each residue, the still-unused S labels satisfy
\[
 J_S=\bigl[L_4-R(A_2+B R)\bigr]/(w^2-h^2)=0 ,
\]
and this is a quadratic with nonzero leading coefficient in the residue. The actual third-D residual satisfies the quadratic \(U(e,g)=L_4(e)-g(A_2(e)+Bg)\) whose leading coefficient is also a unit. Thus every possible actual fourth label/residual used below is integral. The two shared D labels have both their occurrences consumed, and both endpoints are singleton; these are all possible forward fourth choices.

For completeness the actual first-three residual interpolant in \(y=x-1\) is
\(T_2=\tfrac12+(1-\alpha u)y+(\alpha-\tfrac12)y^2\),
\(\alpha=(3u-2)/D\). With its \(x\)-linear and quadratic coefficients \(b_x,c_x\), compute the [true fourth read](../sdirk-eight-all-dirty-seven-clock/README.md#literal-fourth-reads-including-singular-pivots)
\[
 C_4(w)g=N_4(w),\quad C_4=1-\Lambda+b_x+c_x\Delta,\quad N_4=T_2-JT_2 ,
\]
where \(x=w+h+1,\ \Lambda=1+(x-1)/\kappa\), \(\Delta=4/3+2(\kappa+1)(x-1)/(3\kappa)\), and \(J\) here means integration of the polynomial from zero. Both gcds, \(J_S\) against \(C_4 R-N_4\), and \(U(e,g)\) against \(C_4(e)g-N_4(e)\), are units at **each** residue. This excludes all algebraic residue roots. No affine fourth coefficient is inverted and no order or splitting restriction on the original field is used.

## Center third D: normalized trace against both fourth options

If \(e=0\), the singleton graph is \(R(w)=(w^2-\eta)/(2(h^2-\eta))\), even and still genuinely quadratic. Then \(\lambda=1\), \(B=\beta\); both paid D evaluations of \(A_2\) now equal \(-B(f_1+f_2)\), so \(A_2\) is even. Its values at \(w^2=d^2,h^2\) determine it. The true residual distinction at either shared D also gives \(f_1\ne f_2\). Use \(X=w^2\) and let \(\sigma\) be the squared clock of the other singleton pair, obtained from the remaining factor \(J_S\propto X-\sigma\). Exactly four S clocks and the degree-four singleton polynomial force that factor to have nonzero leading coefficient and \(\sigma\ne0,h^2,d^2\). In particular \(R(\sqrt{\sigma})\) here is an even-polynomial value at \(X=\sigma\), not an assumption of an additional field extension.

Use the [normalized nilpotent trace](../sdirk-eight-all-dirty-seven-constant/README.md#the-trace-gate-and-its-normalization),
\(2\sum 1/g_i=2m\sum b_i/g_i\).
The unweighted sum in this chart is
\[
 \sum 1/g_i=4+\frac{2}{R(\sqrt{\sigma})}
             +\frac{A_2(0)}{L_4(0)}+2\frac{A_2(d)}{L_4(d)} .
\]
The three D terms are Vieta inverse sums. For the weighted sum the [exact Cauchy remainder identity](../sdirk-eight-all-dirty-seven-quadratic-two-triple-d/README.md#normalized-quadratic-trace-and-literal-fourth-reads) gives the coefficient of \(w^7\) in the remainder of \(H_3(L_4/R+A_2)/Q_0\) modulo \(L_4^2\), with \(H_3=4m^6/175\) and \(Q_0=Q/B\).

This weighted formula does not require two distinct roots of \(R\): the Cauchy expression is
\[
 \frac{B H_3[A_2(A_2+B R)+B L_4]}{P\mathcal H L_4^2}
 =\frac{B H_3}{P\mathcal H R^2}
    -\frac{H_3(L_4/R+A_2)}{Q_0L_4^2},
 \qquad \mathcal H=L_4-R(A_2+B R).
\]
Its physical residues are the grouped \(b/g\); any extraneous residues are contributed by the second term at \(L_4\) roots, including when a physical S is also such a root. The whole expression has zero residue at infinity. This gives the coefficient rule, with the sign as written. Since \(R\mid Q_0\) and \(Q_0\) has no root in common with \(L_4\), both inverses are legitimate. In \(X\) the odd remainder is \(w\) times the remainder of
\[
 (L_4/R+A_2)/[-b X(X-d^2)(X-\eta)]
\]
modulo the even \(L_4^2\), and the coefficient needed is that of \(X^3\), times \(H_3\). Here inverse coefficients can be formed by an adjugate over the monic basis; their determinants are nonzero at every actual candidate by that coprimality. This specialization does not assume a generic rational pivot is nonzero.

The exact trace numerator has degree 12. For the unused S option, reduce \(C_4(w)R(w)-N_4(w)\) modulo \(w^2-\sigma\), obtaining \(a_0+a_1 w\), and require \(a_0^2-\sigma a_1^2=0\). For the center D option, use the denominator-free necessary equation
\[
 C_4(0)^2 L_4(0)-A_2(0)N_4(0)C_4(0)-B N_4(0)^2=0 .
\]
This remains necessary in the singular affine case. Their exact numerator degrees are 45 and 23. The replay checks all final denominator factors against the actual nonzero gap, tap, Legendre, curvature, quartic leading, distinct-label and \(R\)-value guards. The **raw** rational-polynomial gcd with the trace numerator is a unit for each. Both options at the centered third D are therefore impossible.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_offcentre.py` and `SYMPY_GROUND_TYPES=flint python check_centre.py` with SymPy 1.14 and python-flint 0.8. The native Lean companion checks the scaled interpolation difference and denominator-free fourth equation; it does not formalize the full topology, trace or finite-place transfer. The noncentral finite test certifies a characteristic-zero contradiction only. No interval endpoint moves.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
