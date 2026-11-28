# Eight distinct zero clocks: early live affine root, finite rear gaps

Consider strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, with common nonzero diagonal. Write \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly eight physical zeros have distinct clocks, and the nonconstant reverse barycentric numerator has its root \(q\) at one of physical rows 3, 4, 5. The [low-label census](../sdirk-eight-eight-zero-low-labels/README.md) gives the distinct silent off rows 1 and 2; the [silent affine-root exclusion](../sdirk-eight-eight-zero-silent-pure-root/README.md) ensures \(b_q\ne0\).

**Result.** The silent-eighth and live reflected arithmetic phases are both impossible in this chart, for each of the three possible physical root placements. Together with the [live-star proof](../sdirk-eight-eight-zero-affine-early-star/README.md), this excludes the first three clean rows as affine-root sites in **all** rear phases. No change in the global stage interval follows.

## 1. The affine cardinal rows and the individual jump

Normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\). Let \(P_8\) be the monic eight-site polynomial and \(B(x)=I_D(P_8/(T-x))\), \(I_D(T^j)=D^j/(j+1)\). In the finite-gap phases write
\[
 s=D-1,\quad t=s-v,\quad r=s-2v,\quad \kappa=1+2v-v^2\ne0.
\]
The actual rear pure/ordinary ratios and \(z_iP'_8(x_i)=\Theta(x_i-q)\) give
\[
  \kappa(s-q)B(t)-(t-q)B(s)=0.
\]
At a silent eighth row the other row is \(B(r)=0\), and the literal ghost gap polynomial is \(H(v)=v^3-4v^2-v+2=0\). At a live arithmetic eighth, write \(\kappa_3\) for its third relative residual ratio. The [literal two reverse tests](../sdirk-eight-seven-zero-pure-distinct/README.md#2-rear-cardinal-rows-and-the-arithmetic-compatibility-sextic) give \(\kappa_3(s-q)B(r)=(r-q)B(s)\), \(H(v)\kappa_3=-\kappa Q(v)\) and the affine-compatibility sextic \(T_6(v)=0\), with
\[
 Q(v)=4v^3-12v^2+3v+2,\qquad
 T_6(v)=8v^6-44v^5+22v^4+97v^3-55v^2-13v+6.
\]
The sextic is the same literal three supported input test; its pure reverse row space is spanned by \(\mathbf z^\mathsf T,\mathbf z^\mathsf T C'\) because the second pure ratio is nonzero. Clearing \(H(v)\) gives the second cardinal row \(-\kappa Q(v)(s-q)B(r)-H(v)(r-q)B(s)=0\). No ratio is taken at \(q\). No ordinary mean \(I_D(P_8)=0\) is presumed.

Let \(a,b,c,d,e\) be the five early zero labels in order, \(q\in\{a,b,c\}\), \(\sigma=(T-a)(T-b)(T-c)\), and \(P_2=(T-d)(T-e)\). Form \(U_6=\sigma(T-s)(T-t)(T-r)\), \(V_5=U_6/(T-q)\). Use the just derived relative cardinal equations on \(P_8=U_6P_2\) as the two genuine ordinary homogeneous rows in the coefficients of \(P_2\); all these masks have total mean degree at most seven. The individual live root has
\[
 b_q=I_D(V_5P_2)/(V_5(q)P_2(q)).
\]
The [pure-profile proof for a single live root](../sdirk-eight-eight-zero-affine-early-star/README.md#1-the-single-live-root-has-a-split-free-pure-jump) is independent of the rear phase. For \(F_4|_U\) its actual two modes are \(L_4\) and the scaled mean reproducer \(K(T,q)\), with the extra value \(-D^6/b_q\) at the actual \(q\) in the latter mode.

## 2. Literal pure transfer and exact factors

The forward first-two supported reads and actual third diagonal give \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\) and transfer \(f(c)=\alpha(c)f(a)+\beta(c)f(b)\) for all \(F_4|_U\) profiles. On \(L_4\) this is \(C_3(c;D)=0\). On the actual \(K\)-with-jump mode it is
\[
 E_K I_D(V_5P_2)-w_qD^6 V_5(q)P_2(q)=0,
\]
where \(E_K=K(c,q)-\alpha(c)K(a,q)-\beta(c)K(b,q)\) and \(w_q=-\alpha(c),-\beta(c),1\) for \(q=a,b,c\). Both coefficients \(E_K,w_qV_5(q)\) divide by \((c-a)(c-b)\) exactly, as in the gap-free proof. This gives a third homogeneous row on the unknown monic quadratic, in addition to the two cardinal rows. Their determinant \(A_0(D,c)\) is zero without an ordinary recovery-pivot hypothesis.

The exact coefficient field has primitive \(u+b+2v\) and degree 18 (ghost) or 36 (arithmetic). Its irreducibility, inverse coordinates and the front equations are verified in the replay. Writing \(C_3=\ell_2c^2+\ell_1c+\ell_0\), at \(\ell_2\ne0\) scale \(L=\ell_2c\) and reduce \(A_0\) after clearing powers of \(\ell_2\) to \(A+B L\) in the monic quadratic algebra. Its norm is \(A^2-AB\ell_1+B^2\ell_2\ell_0\). The following counts are exact; no residue-rank drop is used to strip a factor.

| Phase | Root | Raw norm degree | Factors removed after the \(\ell_2\) power |
|---|---|---:|---|
| Ghost | \(a\) or \(b\) | 86 | \(D^{12}\) and the three scalar rear-collision squares |
| Ghost | \(c\) | 110 | \(D^{12}\) and three degree-six projected rear-collision factors |
| Arithmetic | \(a\) or \(b\) | 88 | \(D^{12}\), terminal collision power four, other two rear-collision squares |
| Arithmetic | \(c\) | 120 | \(D^{12}\), terminal projected collision squared, the other two projected collisions once each |

The \(\ell_2\) powers are the respective \(c\)-degree of \(A_0\), namely \(5,8,5,9\), with \(\ell_2\) of degree four. The scalar collision guards are equalities of the known \(a,b\) with rear labels, forbidden by distinctness. In the \(q=c\) chart each projected collision is \(C_3(\rho;D)\) for \(\rho=s,t,r\). The replay verifies exact division and the exact congruence \(A+B\ell_2\rho=0\) modulo each. There \(B,\ell_2\) are units in the selected reduction of the preserved-degree factor. Thus an actual root on it would make \(c=\rho\), even if a factor occurs twice. After these guards the norm is degree 48 in every case.

The exact degree-30 first-two rank factor is the [same transfer argument as in live star](../sdirk-eight-eight-zero-affine-early-star/README.md#3-front-equations-exact-exceptional-factors-and-the-fourth-read): on the two other early labels the oriented \(L_4,K\) minor (before its optional \(c-a\) or \(c-b\) factor is canceled) is \(w_q\) times the actual first-two \(L_4,K\)-with-jump determinant. The scaled norm of that normalized minor \(E\), stripped of its known \(\ell_2\) power, divides the degree-48 factor exactly. Its scaled remainder \(E_0+E_1L\) obeys \(E_0 B-E_1 A=0\) modulo the degree-30 factor. With all \(B,\ell_2\) and \(w_q\)-norm units checked, it forces an impossible rank loss at the **actual** root. The complementary factor is degree 18.

## 3. Fourth read and all remaining field guards

In the complete degree-18 quotient the replay recovers \(c=-A/(B\ell_2)\), checks the ordinary two-row determinant, and recovers the coefficients of monic \(P_2\). \(I_D(V_5P_2)\) is a unit, so the actual \(-D^6/b_q\) jump is recovered. The corrected basis detects the first two reads with unit determinant. The supported cubic \(\sigma\) kills the first three actual donors; its primitive error is fitted from \(-J\sigma(a),-J\sigma(b)\) in this basis. At the actual fourth zero \(d\), its input reads diagonally and there is no jump there. Subtract the fitted pure correction from \(\sigma-J\sigma\) and clear the basis determinant. Dividing by the monic product of the two first-three labels other than \(q\) gives a quadratic necessarily zero at \(d\). Its norm modulo monic \(P_2\) is a unit throughout the degree-18 quotient. This excludes both orders of the prospective last two early labels.

The separate \(\ell_2=0\) case has \(\ell_1\) a unit in the entire preserved-degree guard algebra; substituting \(c=-\ell_0/\ell_1\) gives constant gcd with \(A_0\). No ordinary or pure mode recovery pivot is used there.

| Phase | \(q=a\) | \(q=b\) | \(q=c\) |
|---|---:|---:|---:|
| Ghost | \((17,6)\) | \((17,6)\) | \((17,6)\) |
| Arithmetic | \((59,28)\) | \((59,28)\) | \((103,65)\) |

Each pair is \((p,z_0)\), a prime and fixed simple root of the exact primitive field polynomial, with all played-back coefficient denominators integral. The checked leading degrees make every hypothetical diagonal root integral, and the pivot units justify every recovery and reduction. Monicity of the recovered quadratic makes both possible fourth labels integral. Residue checks operate in full polynomial quotient algebras, including nonsplit factors. They prove characteristic-zero nonexistence, not an assertion about all tableaux over the residue fields.

## 4. Replay and native scope

Run `python check_affine_finite.py PHASE SLOT` for `PHASE=ghost,arith` and `SLOT=0,1,2`. SymPy 1.14 and Python-flint 0.8 are used. Exact univariate guard divisions use cached rational-polynomial field inverses and are checked with zero remainder before any residue computations. The arithmetic \(c\)-case may take longer. The [Lean companion](../../lean/RKCert/Research/SDIRKEightEightZeroAffineFiniteMasks.lean) checks the relative-cardinal scalar elimination; kernel and fourth-read arithmetic are the earlier native gates. The full saturated tableau ingress and exact field comparisons remain mathematical proofs.

The new companion is included as source; its independent stock Lean replay was not completed at publication.
