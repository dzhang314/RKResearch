# Corrected actual ordinary hole six: star-front cubic case excluded

This is one exact exclusion in strict SDIRK8 at ten stages over a characteristic-zero field. Use the [reverse-live nine-site corrected ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md): the sole quadratic-defect row is physically first and ordinarily and reversely silent, and the nine other clocks are distinct. Eight of these are ordinarily active; the extra ordinarily silent row \(\zeta\) is actually reverse-live. The affine reverse numerator and genuine quintic mixed numerator share the ordinary root \(r\). The actual normalized amplitude there is zero but its continued quartic \(H\) satisfies \(H(r)\ne0\). Here the **actual ordinary hole is physical six**, the front is star, and the actual fifth amplitude agrees with the literal fourth cubic evaluated at the fifth clock: \(h_5=H_4(c_5/\gamma)\). This includes every nonexceptional fifth clock in the star front and any exceptional clock with that same amplitude. All actual ordinary-silent placements \(2,3,4,5,7,8\) are excluded, including both ordinary rear phases. No order or positivity is used.

## True early reconstruction

Use the [physical pure-four graph](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole67-clean-bridge/README.md). Put \(s=c_4/\gamma,\ y=c_5/\gamma,\ R=r/\gamma\), and let \(a,b=2\pm\sqrt2\) denote the two normalized literal early clocks. In the star front
\[
 H_4(Y)=(6-18Y+9Y^2-Y^3)/8,\qquad
 D(Y)=d_2Y^2+d_1Y+d_0
\]
where \(D\) is the exact divided \(L_4\) fourth-pivot polynomial and \(D(s)\ne0\). The replay computes its coefficients. At actual fifth, the condition \(h_5=H_4(y)\) means \(M_2-(a+b)M_1+ab M_0=0\) on its strict predecessor taps after stage one. This is exactly the actual fourth tap times \((s-a)(s-b)\). The latter factors are nonzero, so the actual fourth tap in row five is zero. The same two-tap read as the hypothetical fourth gives \(D(y)=D(s)\), using the actual pure-four graph and \(R_A(Y)=1/4\). Since \(y\ne s\), write
\[
 e=y+s=-d_1/d_2,\qquad p=ys .
\]
The division by \(d_2\) is genuine: \(d_1,d_2\) are coprime, and a zero \(d_2\) would leave \(d_1(y-s)=0\) with \(d_1\ne0\). This also covers the case \(y=(3s-1)/2\) **if** it has the specified cubic amplitude; no conclusion is made by assigning that amplitude to a general exceptional fifth.

The actual clean sixth has zero amplitude at \(R\), not \(H(r)\). Its paid row-six scalar gate gives
\[
 9L_4(r)+D(s)(R^4-16R^3+72R^2-96R+24)=0 .
\]
By the [true corrected non-Gauss guard](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-signed-nodal/README.md) \(L_4(r)\ne0\). Thus
\[
 J=r^4-16\gamma r^3+72\gamma^2r^2-96\gamma^3r+24\gamma^4\ne0,\qquad
 p=\frac{d_0+9\gamma^4 L_4(r)/J}{d_2},
\]
because \(D(s)=d_0-d_2p\). This calculation is valid regardless of early profile anchor rank and ordinary visibility.

All four early physical rows \(2,3,4,5\) have true cubic amplitudes \(H_4\) at their normalized clocks, also when one is \(\zeta\). Therefore
\[
 H(\gamma Y)=H_4(Y)+\lambda (Y-a)(Y-b)(Y-s)(Y-y),\qquad \lambda\ne0 .
\]
Use the following physical-clock polynomial representatives, with all removed scaling factors nonzero:
\[
 \begin{aligned}
 C_3(X)&=6\gamma^3-18\gamma^2X+9\gamma X^2-X^3,\\
 E_4(X)&=(X^2-4\gamma X+2\gamma^2)
     \left[d_2J X^2+\gamma d_1 J X+\gamma^2(d_0J+9\gamma^4L_4(r))\right].
 \end{aligned}
\]
Here \(C_3=8\gamma^3 H_4(X/\gamma)\), and \(E_4\) is the four-early-clock product scaled by \(d_2J\ne0\). The ordinary paid moments give \(I((X-r)X^j H)=0\) for \(j=0,1,2\), because \(H=\alpha L_4+\beta K_3(X,r)\). Define \(F_j=I((X-r)X^j C_3)\), \(E_j=I((X-r)X^j E_4)\). Then \(\boldsymbol F+\eta\boldsymbol E=0\) with finite \(\eta\ne0\). Therefore the three minors \(B_{ij}=F_iE_j-F_jE_i\) vanish. Their \(r,\gamma\) bidegrees are all \((6,14)\).

## Exact diagonal, retaining all rank losses

The three pairwise resultants of the \(B_{ij}\) in \(r\) have degree 148 in \(\gamma\). Their exact common monic gcd has rational factor degrees and multiplicities \((1,24),(4,4),(16,1),(66,1)\); its degree-one factor is \(\gamma\). The degree-four factor forces \(L_4(r)=0\): the complete common \(r\)-gcd over its exact number field is the monic \(L_4(r)/70\). The degree-sixteen factor has complete common \(r\)-gcd linear; all three \(E_j\) vanish there. But the three pairwise \(r\)-resultants of the \(F_j\) have constant common gcd, so the \(F_j\) never vanish simultaneously. This excludes the entire rank-lost component without inverting a moment there. These are exact rational and number-field eliminations. The whole degree-66 diagonal remains for the finite check.

## Actual rear and signed nodal checks

Use the paid [star rear](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-star-literal-closed/README.md), [arithmetic rear](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-arithmetic-literal-closed/README.md) and [actually silent-eighth](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole5-star-silent-eighth-closed/README.md) identities. Those scalar rear identities use the **true** terminal/penultimate/eighth values and are independent of which earlier ordinary stage is the hole. Put \(x=1-\gamma,\ c=c_9=x-\gamma u,\ k=1+2u-u^2\). The true penultimate equation for known silent clock \(z\) is
\[
 (x-z)H(c)-k(c-z)H(x)=0 .
\]
For an ordinarily weighted eighth, its clock \(d\) is \(x-\gamma(2-u)\) in the star rear, and \(x-2\gamma u\) in the arithmetic rear. The universal equations independent of \(z\) are:
- With \(v=u-1\) in the star rear, the divided numerator is
  \[
  \frac{(1-v)H(c)-(1+v)H(d)+2v k H(x)}{v(1-v^2)} .
  \]
  This is an exact quadratic, with leading \(2\gamma^4\) for monic normalization of \(H\). Each removed padding factor is nonzero by distinctness of \(c,d,x\).
- In the arithmetic rear, let \(J_{\rm r}=2+3u-12u^2+4u^3\), \(H_{\rm r}=-2+u+4u^2-u^3\). The divided numerator is
  \[
  \frac{H_{\rm r} H(d)+2J_{\rm r}H(c)-kJ_{\rm r}H(x)}{u^2}.
  \]
  This exact quintic has leading \(-8\gamma^4\) for monic \(H\). No division by either cubic or any inferred nonzero amplitude at \(d\) is made.
- If eighth itself is \(\zeta\), \(z=x+\gamma k(u-2)/2\). The required numerator
  \[
  \frac{(u-2)H(c)-(2u+k(u-2))H(x)}{u}
  \]
  has exact degree four, with leading \(\gamma^4\) for monic \(H\). No ordinary phase is imported into this branch.

The [signed nodal form](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-signed-nodal/README.md) is \(D_7=H U_3+\nu M_5\), \(M_5=(X-r)L_4\). Thus the remainders of \(D_7\) and \(M_5\) modulo \(H\) are proportional. Use all six two-column minors of their four coefficient pairs, without assuming a nonzero coordinate modulo the prime.

For \(\zeta=2,3,4,5,8\), there are six known ordinary nonhole pegs: both endpoints and either all four early clocks (silent eighth) or the three non-silent early clocks plus \(d\). Let \(E_6\) be their monic product, and \(A_c=H(c)E_6'(c),\ A_x=H(x)E_6'(x)\). The seventh ordinary nonhole clock \(n\) is physical seven. Actual \(b_9=b_{10}\) gives \((A_c-A_x)n=cA_c-xA_x\), and \(A_c-A_x\ne0\) on the source since both endpoint factors are nonzero and \(c\ne x\). Instead of dividing, test the signed minors for
\[
 E_6(X)\big((A_c-A_x)X+xA_x-cA_c\big).
\]
If \(\zeta\) is an early clock, use its own true \(z\) in the penultimate equation as well. Silent two and three are each checked using one of the two actual early star clock values. For silent four or five, choose \(z\) as either root of the **complete** quadratic \(X^2-\gamma e X+\gamma^2p\), and retain the other root \(\gamma e-z\) as ordinary. This covers the two placements without postulating any chronological exchange. Silent eighth has no ordinary \(d\) factor. For \(\zeta=7\), all seven ordinary nonhole clocks are known, so test their literal full product directly and check \(b_9=b_{10}\). These necessary equations already exclude this placement without recovering its unknown \(z\).

## Complete specialization proof and receipt

With \(p_{\rm res}=1009\), the degree-66 monic \(\gamma\) factor is integral and its complete reduced factor degrees are \(2,5,15,21,23\), all simple. Over each residue field, the three \(r\)-parents retain their actual full degree six. Their reduced common gcd is linear. Every actual characteristic-zero candidate would be algebraic in \(\gamma,r\) (the degree-six leading is a local unit) and reduce in one of these fibers. On **all** the reduced joint roots, \(\gamma,d_2,J,L_4(r),E_0,F_0\) and the leading coefficient of \(E_0 C_3-F_0 E_4\) are nonzero. Thus the rational \(e,p\), and normalized \(H\) in the code, are integral at the corresponding residue primes and equal the reductions of the actual quantities. Both the quadratic early factor and each shown rear polynomial have unit leading coefficient, so the further actual clocks or gaps are integral at those primes as well. No assumed good reduction of a hidden tableau is needed: for any remaining candidate, embed its algebraic scalar coordinates in an algebraic closure of the \(1009\)-adic field, use these full-leading unit checks to force integral scalar reductions, and apply the homogeneous necessary gates there.

The code keeps every irreducible gap factor and tests every possible root of the early \(z\) quadratic where required. Seven ordinary star factors and ten ordinary arithmetic factors each pass four tests (silent 2, silent 3, both 4/5, and silent 7); the silent-eighth branch has fourteen factors. This is an exclusion, not a bounded search for tableaux.

Replay from this directory with `python3 check_sixth_hole.py` using `sympy==1.14.0` and `python-flint==0.9.0`. The two scripts are self-contained and need no sibling executable or network once those packages are installed. This is exact source arithmetic, not a new native Lean claim. An actual star-front corrected ordinary hole six would now require **\(y=(3s-1)/2\) and \(h_5\ne H_4(y)\)**. Arithmetic-front actual hole six and all actual hole-seven cases remain separate. The unrestricted strict SDIRK8 bound is still **10–11**.
