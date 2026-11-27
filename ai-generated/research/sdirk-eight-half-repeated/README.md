# The repeated-clock endpoint-pair charts are impossible at strict SDIRK8

This closes the two remaining physical clock charts of the [all-active half-diagonal endpoint pair](../sdirk-eight-half-equal/README.md) for ten-stage strict SDIRK of order at least eight over a field of characteristic zero. In this chart \(\gamma=1/2\); only stages 1 and 10 have nonzero quadratic residuals, both \(g=1/8\) and \(c=1/2\), with \(b_1=-b_{10}\). Let \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). The earlier [coprime](../sdirk-eight-half-arithmetic-quadratic/README.md) and [no-singleton](../sdirk-eight-half-shared-root/README.md) proofs leave only six or seven distinct zero clocks among the eight physical zero rows. Both counts are excluded below. This is not an exclusion of every ten-stage strict SDIRK8 tableau, and the unrestricted interval remains **10–11**.

On the zero rows write \(\ell(f)=\sum b_i f(c_i)\) for scalar functions, and similarly with \(h\) or \(h^2\) factors using the physical values. Ordinary precision through seven is unaffected by the canceling endpoint pair. The paid \(h\) and \(h^2\) moments vanish through respective scalar degrees four and one.

## 1. Six clocks fail a two-node quadrature completion

The four pegged front/rear zero clocks \(a,b,c,d\) are distinct. The earlier literal tap result also gives \(s=c_4,y=c_5\) distinct from \(a,b\) and each other, even with a repeated quadratic-zero clock elsewhere. Their necessary equation is the [literal fifth-clock gate](../sdirk-eight-half-shared-root/README.md), \(R(s,y)=0\), with the earlier pure-rank and clock factors already removed.

If there were six distinct physical zero clocks, their monic nodal polynomial would be \(P_4 Q_2\), where \(P_4(X)=(X-a)(X-b)(X-c)(X-d)\) and \(Q_2=X^2+uX+v\). With \(I(X^j)=1/(j+1)\), the paid scalar moments give \(I(P_4Q_2)=I(XP_4Q_2)=0\). Thus \(u,v\) solve one exact two-by-two system with entries \(M_j=I(X^jP_4)\). Its determinant \(M_0 M_2-M_1^2\) is nonzero in every relative endpoint phase. This does not assume that every aggregated weight at a repeated clock is nonzero.

Now \(s,y\) are distinct ordered choices from \(c,d\) and the two roots of this fixed monic quadratic. Work in the two-dimensional quotient over \(\mathbb Q(t), t^2=1/2\), naming one root \(z\); the second is \(-u-z\). For all twelve ordered choices and all six relative phases, the exact norm of \(R(s,y)\) is nonzero. It therefore cannot vanish at any actual root choice, whether the quadratic splits in the coefficient field or not. This argument does not use a shared-root assumption. The [Lean scalar receipts](../../lean/RKCert/ReviewedNative/SDIRK8RepeatedClockScalarReceipts.lean) check the two nodal coefficient equations and the quadratic-root nonvanishing bridge.

## 2. One repeated clock: the final literal chart

If there are seven distinct zero clocks, the [shared-root census](../sdirk-eight-half-shared-root/README.md) leaves one repeated clock \(r\) with different \(h\)'s and exactly one common factor, \(p=(X-r)p_0,\ q=(X-r)q_0\) after normalizing \(q\) monic. Here \(q_0=1\) or \(X-\xi\), with \(p_0,q_0\) coprime. No hypothesis excludes \(\xi=r\). Let \(D\) be the monic degree-seven nodal polynomial of the **physical distinct** zero clocks. Interpolating the paid aggregates gives
\[
       R_h(x)=D'(x)\sum_{c_i=x}b_i h_i=\kappa q_0(x),\qquad
       S_h(x)=D'(x)\sum_{c_i=x}b_i h_i^2=\kappa p_0(x),
       \qquad \kappa\ne0 .
\]
The sums here run only over zero rows. The formula uses the degree budget proved in the census, not an attempt to divide through the repeated clock.

The first four physical zero clocks in each chronological orientation are distinct. Hence the repeated pair crosses the two four-zero halves, \((2,3,4,5)\) and \((9,8,7,6)\). It cannot contain two pegged corners because those four clocks are distinct. Orient any pegged member of the pair as a *front* corner; if neither member is pegged, take either orientation. Then \(a,b,s,y,c,d\) are six distinct clocks, \(r\) is one of \(a,b,s,y\), and physical rows six and seven consist of the repeat at \(r\) and the remaining new singleton clock \(z\) in some order. Thus
\[
       D=P_6(X-z),\quad P_6=(X-a)(X-b)(X-s)(X-y)(X-c)(X-d).
\]
By \(I(D)=0\), \(z=I(XP_6)/I(P_6)\); the denominator is nonzero because \(\ell(P_6)=b_z P_6(z)\) and the active singleton \(z\) is distinct from all of the six pegs. The replay equivalently uses the scaled nodal polynomial \(\widetilde D=I(P_6) XP_6-I(XP_6)P_6\), avoiding division in the symbolic projection.

## 3. A low-degree Bézout constraint with a physical pole

Use \(W_f(X)=I_Z((f(X)-f(Z))/(X-Z))\) and \(\mathcal B_p(D)=pW_D-DW_p\). At each clock \(x\), \(W_D(x)=D'(x)\sum_{c_i=x}b_i\) by ordinary Lagrange interpolation. The original physical relation \(q(c_i)h_i=p(c_i)\) implies \(p(x)W_D(x)=q(x)R_h(x)\), including at the pole \(r\). The polynomial \(\mathcal B_p(D)\) has degree at most three: formally it is \(D E_p-p E_D\), where \(E_f=\sum_{j\ge0}I(X^j f)X^{-j-1}\). The first three coefficients of \(E_p\) are zero by Legendre orthogonality, and the first coefficient of \(E_D\) is zero by \(I(D)=0\). Thus \(D E_p\) and \(p E_D\) each start in degree at most three. There are seven distinct roots of the difference, so
\[
                         \mathcal B_p(D)=\kappa q q_0 .
\]
There was no cancellation at a physical clock in obtaining this equality. In particular the same collinearity is necessary for \(\mathcal B_p(\widetilde D)\) and \(q q_0\). The coefficient replay uses the divided-difference monomial formula from the [arithmetic Bézout projection](../sdirk-eight-half-arithmetic-quadratic/README.md).

## 4. Exact scalar projection and all exceptional fibers

For each relative front/rear phase, the previous chronological chart supplies \(h_s\) by a cubic, \(h_y\) by the two affine pure reads, and \(R(s,y)=0\). In front star there are two explicit linear choices for \(y(s)\); in front arithmetic retain its monic quadratic over \(\mathbb Q(t)(s)\). Choose each of \(a,b,s,y\) as the known first occurrence \(r\), and test both denominator degrees.

On the generic pivots interpolate \(p\in\langle L_3,L_4,L_5\rangle\) from the first three literal front values, including the value at a pole if it is among them. The linear case \(q=X-r\) has no remaining parameter; its fourth value, rear ratio and Bézout collinearity are exact scalar gates. For \(q=(X-r)(X-\xi)\), write \(q=q_A+\xi q_B\), \(p=p_A+\xi p_B\); the fourth value is \(F_0+\xi F_1=0\). When \(F_1\ne0\) use \(F_1 q_A-F_0 q_B,F_1 p_A-F_0 p_B\), a common scaling that avoids the division by \(F_1\). The rear ratio
\[
                        l q(d)p(c)-k q(c)p(d)=0
\]
is homogeneous in these scaled profiles, and the scaled reduced denominator is \(F_1 X+F_0\). Compare the degree-three coefficient vector of \(\mathcal B_p(\widetilde D)\) with the vector of \((X-r)(F_1 X+F_0)^2\) by cross-products. In the linear case the corresponding vector is \(X-r\). Neither test requires computing the individual weights of the repeated pair.

The [projection replay](shared_profile_projection.py) takes norms of these necessary scalar functions in the literal \(y\) quotient and the quadratic coefficient field, then computes their exact rational-polynomial numerator gcd. In all **72** cases (orientations, pole choices and denominator degrees) its squarefree factors lie entirely in the known scalar pivot support. Coefficient denominator factors are checked against that support. The resulting exception polynomials have degree at most \(88\). Thus there are no solutions in the open chart; all possible bad pivots are included rather than simply rejected.

The [finite replay](check_repeated_clocks.py) factors that recorded support and rechecks each factor in exact algebraic quotients. It chooses the auxiliary literal affine pivot and the third front interpolation site again, and if the fourth-value equation loses its \(\xi\) coefficient, keeps the rear equation as a separate finite polynomial. Nonunit coefficients split by exact polynomial gcds or verified binary-root decompositions. It also checks that the six pegs remain distinct, \(z\) is a seventh clock, and any root of the reduced denominator is not a physical clock other than \(r\). The latter uses maximal cancellation, not division at \(r\). Every finite chart fails an actual scalar condition, so after the six-clock result there is no remaining all-active half-diagonal endpoint pair.

Run `python3 check_repeated_clocks.py` from this repository folder with `sympy==1.14.0` and `python-flint==0.9.0`. It imports the earlier literal quadratic, star and arithmetic checker folders. Argument `1` runs the front-star one-repeat fibers and `0` the front-arithmetic ones; either run also checks the six-clock cases. The Lean receipts verify the scalar steps above, not an end-to-end exclusion for the entire tableau or the exact polynomial calculations.
