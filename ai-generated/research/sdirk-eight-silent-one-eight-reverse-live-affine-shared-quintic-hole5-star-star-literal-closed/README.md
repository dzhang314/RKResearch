# Regular corrected ordinary hole5, star front and true star rear, actual silent 2 or 3

This excludes the literal ordinarily silent positions \(\zeta=2,3\) with early rank two, star front and ordinarily weighted star rear in the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md). There are ten strict SDIRK8 stages over a characteristic-zero field, with only first quadratic defect, and that first stage is ordinarily and reversely silent. Eight ordinary physical clocks are distinct; one other ordinarily silent physical row is reverse-live at a separate ninth clock. The common root of \(T\) and \(S\) is the **ordinary fifth** \(r=c_5\), with true fifth amplitude zero but \(H(r)\ne0\) for the continued quartic \(H=(S/T)/\gamma^3\). The homogeneous \(H_N=\Delta H=\alpha_N L_4+\beta_N K_3(\,\cdot\,,r)\) comes from the two actual early readings as in the [arithmetic-rear companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-arithmetic-literal-closed/README.md). The earlier [rank-loss packet](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-rank-closed/README.md) is separate.

## Exact front split

Let \(Y=r/\gamma,\ s=c_4/\gamma,\ a=\gamma A,\ b=\gamma B\). The actual-early reduced identity \(J=(\Delta H_4(s)-H_N(\gamma s))/((s-A)(s-B))=0\) uses the true fourth, and its two divisions are at distinct literal fourth clocks, not fake fifth pads. The actual zero fifth gives the exact factorization
\[
 32\Psi(s,Y)=(Y^3-9Y^2+18Y-6)(3s-2Y-1).
\]
Write \(D(Y)=Y^3-9Y^2+18Y-6\). Keep the entire monic cubic \(D=0\), with \(J\) still imposed. In the complementary case \(s=(2Y+1)/3\), substitute that value in \(J\) and remove the exact factor \(\gamma\ne0\), obtaining \(P(\gamma,Y)\) of bidegree \((5,9)\). This covers also any overlap with \(D=0\).

## Two true centered rear comparisons

Set \(x=1-\gamma,\ v=u-1,\ w=v^2,\ X=x-\gamma,\ c=X-\gamma v,\ d=X+\gamma v,\ k=2-w\), and let \(h_y=H_N(y)\). The actual extra ordinarily silent clock is \(z=a\) or \(b\). The penultimate read gives \((x-z)h_c-k(c-z)h_x=0\). The star row gives
\[
 (1-v)h_c-(1+v)h_d+2vk h_x=0 .
\]
Multiplying the first comparison by \(1-v\) and using the star row gives \(1+v\) times the analogous comparison at \(d\). This is a true nonzero gap \(u\); thus **both** physical comparisons hold. Taking their half-sum and divided half-difference gives
\[
 E(w)=(x-z)(h_c+h_d)/2-k(X-z)h_x=0,\qquad
 O(w)=(x-z)(h_c-h_d)/(2v)+\gamma k h_x=0 .
\]
The star row divided by \(v(1-v^2)\) is \(F(w)=0\). The three nonzero factors \(v,1-v,1+v\) correspond to \(c\ne d,\ d\ne x,\ c\ne x\), true distinct actual ordinary tail clocks. Quartic \(H_N\) makes \(E\) quadratic and \(F=F_0+F_1w,O=O_0+O_1w\) affine. Exact expansion gives \(F_1=140\alpha_N\gamma^4\ne0\) by the genuine quartic degree. No leading coefficient of \(O\) is divided. Remove only \(\gamma\) from \(F_1O_0-F_0O_1\), yielding \(Q(\gamma,Y)\) of bidegree \((6,20)\).

## Full leading-zero and cubic fibers

For \(D(Y)=0\), the exact padded \(\operatorname{Res}_Y(D,Q)\) has diagonal degree 60, with no removed factor. Retain \(J=0\) in the \(s\)-fiber. For \(s=(2Y+1)/3\), the exact \(\operatorname{Res}_Y(P,Q)\) has degree 130; remove only \(\gamma^{24}\beta_N^6\) by genuine nonzero diagonal and correction (\(\beta_N=\Delta b_rH(r)\)). The retained degree 82 splits off
\[
 L(\gamma)=120\gamma^3-60\gamma^2+12\gamma-1
\]
with multiplicity one. The leading \(Y\)-coefficient of \(P\) is \(-78400\gamma^6tL(\gamma)/9\), \(2t^2=1\). For \(L=0\), specialize the **full** \(P,Q\) modulo \(L\) first, with respective \(Y\)-degrees 4 and 5. A separate degree-preserving full local check gives no common \(Y\). Do not discard this locus based on a prime-field leading test. Outside it, keep all of the degree-79 projected diagonal. All zero and degree assertions refer to exact polynomials over \(\mathbb Q(t)\).

At the split prime \((1129,t=203)\), the replays retain all monic diagonal factors with their multiplicities. At each, at least one \(Y\) polynomial retains its original leading unit, including the explicitly specialized \(L=0\) chart. The common reduced \(Y\)-gcd is complete. In the cubic-\(Y\) branch retain the full \(J(s)\) quotient using its checked leading unit. Reconstruct \(w=-F_0/F_1\) with a checked unit, and take the complete monic quotient \(v^2-w\), not a chosen root. This keeps both literal orientations because the terminal read uses actual penultimate \(c=X-\gamma v\), not only the unordered tail set.

The five known ordinary nonhole pegs are the other literal early clock, \(c_4,x,c,d\). In the [signed coefficient and terminal rows](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs), their node polynomial \(E_5\) gives \(D_7=E_5R_2\) for true monic quadratic \(R_2\). Using \(H_N(r)I-\beta_N\mathrm{ev}_r\) in the three nonconstant coefficient equations, and the actual \(b_9=b_{10}\ne0\) terminal row, supplies four necessary vanishing minors. The listed minors generate a unit in **all 14 and 22** full retained components respectively (or the earlier \(Y\)-equations already generate the unit). The finite localization argument uses monicity and verified unit tests, not a premise of tableau good reduction.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_star_star_literal.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared sibling dependencies. Three [native algebraic statements](../../lean/RKCert/ReviewedNative/SDIRK8ReverseLiveAffineSharedQuinticHoleFiveStarRear.lean) verify the second literal comparison, its centered sum/difference and the no-pivot scalar elimination on Lean/Mathlib 4.36.0. The finite certificate is exact source-level, not native Lean. Other regular placements, arithmetic front, and other ordinary holes are separate. This does not change the unrestricted **10–11** bound.
