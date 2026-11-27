# The head-silent four-tap architecture cannot reach eleven stages over the rationals

This extends the earlier [symmetric calculation](SYMMETRIC-ELEVEN-OBSTRUCTION.md). It covers nonsymmetric and repeated active clocks and imposes **no** stage-order assumptions on the head. It is not an unrestricted rational eleven-stage ERK exclusion.

## Hypotheses

Let \(A\) be an eleven-stage strictly lower triangular rational matrix, \(c=A\mathbf 1\), and \(c_{11}=1\). Write the seven potentially contributing clocks, in physical order, as
\[
 (c_1,c_6,c_7,c_8,c_9,c_{10},c_{11})=(0,a,h,d,e,f,1).
\]
For \(b\) and four row reads
\[
 B=b^\top A=b^\top(I-C),\qquad D=b^\top C A,\qquad
 E=b^\top C^2 A,\qquad F=DA ,
\]
where \(C=\operatorname{diag}(c)\), require all five rows \(b^\top,B,D,E,F\) to vanish at stages \(2,3,4,5\). Require their scalar polynomial moments as in the [twelve-stage chart](README.md):
\[
\begin{array}{c|ccccc}
 \text{row}&b^\top&B&D&E&F\\
 \text{density}&1&\mu_0&\mu_1&\mu_2&(2-3x+x^3)/6\\
 \text{paid degree}&7&6&5&4&4
\end{array}
\qquad
\mu_j(x)=\frac{1-x^{j+1}}{j+1}.
\]
A row moment against a density is a literal equality on evaluation vectors \(g(c)\) for each polynomial \(g\) through the paid degree. Write \(L[g]=\int_0^1(1-x)g(x)\,dx\), and \(Jg(x)=\int_0^x g(y)\,dy\). When \(e,f,1\) are pairwise distinct, assume \(b_9\ne0\) or \(D_9=0\). This mild additional condition is automatic if every named active slot has nonzero weight.

Under these hypotheses the chart cannot exist over \(\mathbb Q\), hence cannot exist over \(\mathbb Z[1/210]\) either.

## Branch I: the three final clocks are distinct

Only the last row can receive donor 10. Its clock is 1, so \(D_{10}=B_{10}=b_{10}(1-f)\). Also \(D_{11}=B_{11}=0\). Choose a quadratic \(H(x)=(1-x)(1+k(x-f))\) making \((D-b^\top H(C))_9=0\). If \(b_9=0=D_9\), any \(k\) works; otherwise \(e\ne f,1\) and \(b_9\ne0\) permit interpolation. Then \(U=D-b^\top H(C)\) is supported on \(1,6,7,8\). Strictness makes \(UA\) zero in columns \(8,9,10,11\). Its representation as \(F\) minus a linear combination of \(B,D,E\) makes it zero in columns \(2,3,4,5\). Thus \(UA\) is supported on \(1,6,7\).

Put \(P=x(x-a)(x-h)\) and \(V=(x-d)P\). It follows that \(U\) kills \(V(c)\), and \(UA\) kills \(P(c)\) and \((xP)(c)\). Write
\[
       \mu_1-H=(1-x)(p x+q).
\]
These coefficients are not both zero, since \(p f+q=(f-1)/2\ne0\). By the given moments \(U\) integrates against \(\mu_1-H\) through degree 5. Also \(UA\) integrates through degree 4 against \(\int_x^1(\mu_1(y)-H(y))\,dy\), since the adjoints of the degree-two monomials integrate against \(\mu_0,\mu_1,\mu_2\). Thus the three zero reads give
\[
 L[(px+q)V]=L[(px+q)JP]=L[(px+q)J(xP)]=0.
\]
This is integration by parts on polynomials and uses neither internal exact primitivity nor nonzero order weights on the first four head rows.

Two further zero reads follow directly from support.

1. The output pays the degree-seven polynomial \((1-x)(x-e)(x-f)V\), which vanishes on every potentially active site. So \(L[(x-e)(x-f)V]=0\).
2. The row \(D-B\) pays degree five against \(\mu_1-\mu_0=-(1-x)^2/2\). It is zero in the last two physical slots at \(f,1\), so \(L[(x-1)(x-e)V]=0\).

### Exact elimination of the five scalar equations

If \(p=0\), the two primitive moments give \(a+h=6/7,\ ah=1/7\). The discriminant \(8/49\) is not a rational square. Otherwise set \(\rho=-q/p\). The primitive equations determine
\[
 S:=a+h=\frac{3(2\rho-1)(9\rho-7)}{Q},\qquad
 T:=ah=\frac{3(21\rho^2-28\rho+9)}{7Q},\qquad Q=63\rho^2-78\rho+23.
\]
The quadratic \(Q\) has discriminant \(144\cdot2\). Set \(K=63\rho^3-126\rho^2+81\rho-16\). The nodal equation gives \(Kd=K+\rho-1\); if \(K=0\) this would give \(\rho=1\) and \(K(1)=2\).

For \(I_j=L[x^j V]\), direct substitution now gives
\[
 I_0=-\frac{(3\rho-2)(63\rho^2-84\rho+25)}{420QK},\qquad
 I_1=\rho I_0,\qquad
 2I_2=(3\rho^2-2\rho+1)I_0 .
\]
If \(I_0=0\), the second numerator factor has discriminant \(36\cdot21\); the first would give \(\rho=2/3\), then \(S=1,T=1/7\), with nonsquare discriminant \(3/7\). Thus \(I_0\ne0\).

Subtracting the bush equation from the \(D-B\) equation gives \((f-1)(\rho-e)I_0=0\). Since \(f\ne1\), this forces \(e=\rho\), then \(I_2=\rho^2 I_0\) forces \((\rho-1)^2=0\), contradicting \(e\ne1\).

This branch does not require any distinction between \(a,h,d\) and earlier or later clocks. The [Lean module](../../lean/RKCert/ReviewedNative/ERK8ElevenFourTapRational.lean) checks the elimination from the five reduced scalar equations, including the constant-density and zero-denominator cases, with rational nonsquareness reduced to concrete natural-square exclusions. The matrix-to-moment reduction above is mathematical, not asserted as a Lean theorem.

## Branch II: repeated final clocks

First, a rational order-eight rule cannot be supported on five or fewer sites once both endpoints are included in the set of allowed sites, even if their weights are zero. Pad with rational sites to obtain five sites with endpoints. The monic cubic with the three interior sites as roots would then be orthogonal to \(1,x,x^2\) against the positive weight \(x(1-x)\), by integrating its products with the nodal factor \(x(1-x)\). The unique monic cubic with these moments is
\[
       (x-1/2)(x^2-x+1/7).
\]
Uniqueness follows by applying positivity to the square of any difference of degree at most two, or by the nonsingular \(3\times3\) moment matrix. The quadratic has discriminant \(3/7\), not a rational square. This also excludes any monic rationally split cubic (even with repeated roots) orthogonal to these three tests. As a result, if the three final sites contain a repeated clock the seven potentially contributing slots must occupy precisely six distinct sites, and no other repeat is possible.

For use in the repeated cases, notice that for any \(f\) the row \(G=E-(1+f)D+fB\) vanishes at every donor whose later receiver clocks are all \(f\) or 1. Its polynomial density is \(\mu_2-(1+f)\mu_1+f\mu_0=(1-x)^2(3f-1-2x)/6\).

For the first two cases below, the following observation is useful. Set \(P=x(x-a)(x-h)\). Suppose two **different monic quadratics** are each orthogonal to \(1,x\) against density \((1-x)P(x)\). Their difference is nonzero of degree at most one. If it is constant, the first two moments of \((1-x)P\) vanish and either quadratic forces the next two to vanish as well. If it is proportional to \(x-\ell\), the first two moment relations are \(m_1=\ell m_0,\ m_2=\ell m_1\). The monic quadratic recurrence then gives \(m_3=\ell m_2\). In the constant case take \(\ell=0\). Either way \((x-a)(x-h)(x-\ell)\) is a rationally split monic cubic orthogonal to \(1,x,x^2\) against \(x(1-x)\), already excluded.

* **\(e=f\ne1\)** or **\(e=1\ne f\)**: the six distinct sites are \(0,a,h,d,f,1\). The quadrature makes \((x-d)(x-f)\) a monic quadratic orthogonal to \(1,x\) against \((1-x)P(x)\). Here \(G=E-(1+f)D+fB\) vanishes already at donor 8 and later, because all later receiving clocks are \(f,1\). So \(G\) kills both \(P(c)\) and \((xP)(c)\), and its density gives the same two moments for \((x-1)(x-(3f-1)/2)\). This second monic quadratic is different since \(d,f\ne1\). The observation excludes both cases.
* **\(f=1\ne e\)**: the six sites are \(0,a,h,d,e,1\). Quadrature gives \(I_1=eI_0,\ I_2=e^2I_0\) with \(I_j=L[x^jV]\), using the degree-six nodal polynomial and its linear multiple. The row \(E-2D+B\) is supported only at \(1,6,7,8\); later receivers all have clock 1. Its density is \((1-x)^3/3\), so \(I_0-2I_1+I_2=0\). With \(e\ne1\), all three moments are zero, making \((x-a)(x-h)(x-d)\) the excluded rationally split cubic.
* **\(e=f=1\)** leaves at most five distinct sites and was excluded at the start of this branch.

These cases are mathematical reductions. They explain why just changing the symmetric clock grid, allowing a repeat at a different site, or retuning the inactive prefix does not achieve a rational eleven-stage chart while these reverse-read assumptions remain in place. A candidate would need to relax head silence, one of the exact tap moment requirements, the last active clock, or the interpolation condition for a zero-weight ninth slot.

To verify the reduced algebra in Lean, from ai-generated/lean run:

    lake build RKCert.ReviewedNative.ERK8ElevenFourTapRational

The checked theorem is **RKResearch.Certified.ERK8ElevenFourTapRational.no_eleven_four_tap_chart**. Lean/Mathlib 4.36 reports only the standard axioms propext, Classical.choice and Quot.sound.
