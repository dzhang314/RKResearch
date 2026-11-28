# Regular corrected ordinary hole5, arithmetic front and star rear, actual ordinarily silent fourth

This excludes the regular arithmetic-front, ordinarily weighted star-rear chart with extra ordinarily silent yet reverse-live **stage 4**. It is the [genuine affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) for ten strict SDIRK8 stages over a characteristic-zero field. First alone has nonzero quadratic defect and is ordinarily and reversely silent. The eight ordinary clocks are distinct, plus actual reverse-live fourth clock \(z\) at a separate ninth site. The common root \(r=c_5\) is the ordinary fifth, whose actual amplitude is zero and whose continued \(H(r)\ne0\); early rank two means \(\Delta\ne0\). No ordering is used.

Write \(Y=r/\gamma,\ z=c_4=\gamma s,\ a=c_2=\gamma A,b=c_3=\gamma B\), \(H_N=\Delta H=\alpha_N L_4+\beta_NK_3\). The true fourth read is \(H_N(\gamma s)=\Delta H_4(s)\), although the ordinary weight of fourth vanishes. The actual determinant \(\Psi(s,Y)\) uses the true zero fifth amplitude and no spurious fifth pad. As in the [literal arithmetic-front companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-arithmetic-star-literal-closed/README.md), impose
\[
 J(\gamma,Y,s)=\frac{\Delta H_4(s)-H_N(\gamma s)}{(s-A)(s-B)}=0,\qquad \Psi(s,Y)=0 .
\]
Only the true earlier literal pads occur in \(J\). Its exact padded \(s\)-resultant with \(\Psi\), divided by \(\gamma^3\ne0\), gives \(P\) of \((Y,\gamma)\)-bidegree \((17,27)\).

## Centered odd read at the actual silent-fourth clock

Set \(x=1-\gamma,\ X_0=x-\gamma,\ v=u-1,\ w=v^2,\ k=2-w,\ c=X_0-\gamma v,\ d=X_0+\gamma v\). The genuine star row gives \(F(w)=F_0+F_1w=0\) with \(F_1=140\alpha_N\gamma^4\ne0\). The true pair of comparisons at \(c,d\) yields the [centered odd law](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed/README.md#two-true-centered-rear-comparisons)
\[
 (x-z)(L_0+L_1w)+\gamma(2-w)H_N(x)=0,\qquad
 L(w)=\frac{H_N(c)-H_N(d)}{2v}=L_0+L_1w .
\]
Here \(v\ne0\) because the two actual ordinary rear clocks are distinct. Put \(A_0=F_1L_0-F_0L_1\). The actual affine necessary equation is
\[
 U(\gamma,Y,s)=\frac{(x-\gamma s)A_0+\gamma H_N(x)(2F_1+F_0)}{\gamma}=0 .
\]
Its coefficient in \(s\) is \(-A_0\). It is genuinely nonzero at the tableau: otherwise \(\gamma H_N(x)kF_1=0\), contrary to the actual nonzero factors. Neither this coefficient nor the silent fourth amplitude is inverted in the projections. No virtual fourth is used.

The homogeneous quadratic/linear \(s\)-resultant of \(J,U\) has bidegree \((15,50)\) in \((Y,\gamma)\); divide only \(\gamma^4\) for \(C\) of bidegree \((15,46)\). Independently the cubic/linear resultant of \(\Psi,U\) supplies \(N\) of bidegree \((22,60)\) with no removed factor. The exact padded \(Y\)-resultant of \(P,C\) has diagonal degree 1007; divide only \(\gamma^{150}\beta_N^{45}\), with \(\beta_N=\Delta b_rH(r)\ne0\), for full monic degree **677**. The exact gcd of the rational norms of the two \(Y\)-leading coefficients and retained diagonal is one. No simultaneous nominal leading-drop branch is omitted by a modular convention; individual actual leading drops remain allowed.

## Full components and true ordinary pegs

Since \(\zeta=4\), the known ordinary nonhole pegs are \(a,b,d,c,x\), **not** \(z\). Their \(E_5\) gives \(D_7=E_5R_2\), with true monic quadratic having the ordinary sixth/seventh as roots. The [signed coefficient and terminal rows](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole4-middle-closed/README.md#signed-polynomial-determinant-from-five-true-nonhole-pegs) with \(\Lambda=H_N(r)I-\beta_N\mathrm{ev}_r\) and actual \(b_9=b_{10}\) give four necessary vanishing minors. No mass or Cramer pivot is required.

At \((1129,t=203)\) retain all complete degree-preserving diagonal factors with multiplicities, then the full \(Y\)-gcd of \(P,C,N\) with checked full leading unit for at least one. In \(s\), use the full reduced common gcd of \(U,J,\Psi\) when its intermediate pivots are units, or a full monic defining polynomial plus the other residuals if not. Reconstruct \(w=-F_0/F_1\) only with checked unit, and take the whole \(v^2-w\) quotient, retaining both literal orientations. The actual penultimate comparison uses **\(z=\gamma s\)** in this quotient; all four signed/terminal minors and residuals are tested. All **11** full components pass (two already have no common \(Y\)). The finite localization argument does not assume good reduction of the unknown tableau.

Run `python3 check_eight_reverse_live_affine_shared_quintic_hole5_arithmetic_star_fourth.py` with `sympy==1.14.0`, `python-flint==0.9.0`, and the declared siblings. The [two candidate Lean scalar statements](scalar-draft.lean) are included as Lean source; the current native check timed out before elaboration output. The finite exact certificate remains source-level. Ordinary arithmetic rear and later silent positions are separate; the unrestricted **10–11** bound is unchanged.

The publication replay independently reproduced the complete exact arithmetic. Any accompanying Lean scalar source is a draft, not a kernel-checked proof of this result.
