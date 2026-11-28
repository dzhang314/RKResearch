# DIRK12/15: a third ordinary live clock and exact higher pure ranks

Consider the same four-ghost real order-twelve high-site frames as the [ordinary fourth-ghost proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md). Use either:

1. exactly three ghosts before the first ordinary live nonzero clock \(a\), with the fourth before the next live clock \(b\), or
2. the [no-late affine-mask chart](../dirk12-fifteen-rank3-invisible-no-late-affine-masks/README.md) with all ghost clocks nonzero and \(L_6'(a)\ne0\).

In both cases \(L_6'(a)\ne0\), the actual ordinary second live diagonal vanishes, and the first three ordinary live nonzero clocks \(a,b,c\) each have just one physical live row in the relevant nine-site early-return or ten-site earliest-extra-zero chronology. The real interval **15–16** is unchanged.

There is a genuine grade-four state with ordinary scalar profile \(W'\), where \(W=X^2(X-a)^2(X-b)\), numerically zero on all ghosts, the literal origin, and the first live \(a\)-row. Its actual primitive has values \(W\) on all live rows. This forces the third live diagonal to be nonzero and gives an exact degree-seven scalar condition on \(c/a\) with at most five admissible values after \(a,b\) are fixed. The same state also shows the exact ordinary pure ranks
\[
                          (f_6,f_7,f_8,f_9)=(5,7,9,11)
\]
in these two subcharts.

## The literal common quartic mask

In the no-late case take the kernel affine mask from the cited proof: it is grade four, its primitive is \(W\) (scale the mask), and its numerical entries vanish on every ghost and at \(a\). Its actual commutator \(R=CA-AC-A^2\) is zero at \(a\), hence live-zero by the actual \(F_6\) profile and \(a L_6'(a)\ne0\); it is ghost-zero by actual causality as well.

In the late case use the actual grade-four states \(\mathbf U=(C-aI)\mathbf V\) and \(\mathbf W=A\mathbf V\) from the ordinary fourth-ghost proof, with scalar profiles \((X-a)S, JS\), respectively. Their only possible ghost entries are at the fourth ghost. The actual \(b\)-tap \(q\ne0\) satisfies \(qU_{g_*}=f_b,\ qW_{g_*}=l_b\), where \(f_b=J(XS)(b)-aJS(b)\) and \(l_b=J^2S(b)\ne0\). Thus the actual state
\[
                      \mathbf U-(f_b/l_b)\mathbf W
\]
is zero on all ghosts and the first ordinary live rows through \(a\). Its scalar primitive is
\[
      J[(X-a)S]-(f_b/l_b)J^2 S
                  =\frac{3\kappa a}{2b}X^2(X-a)^2(X-b),
\]
from the previously forced cubic \(S=\kappa X(10X^2-12aX+3a^2)\). Scale by the nonzero constant to obtain the true common mask \(\mathbf Q\) with scalar profile \(W'\). The actual \(R\mathbf U,R\mathbf W\) are genuine grade six and vanish on live rows by the actual grade-six line at \(a\). Hence \(R\mathbf Q\) is live-zero, and all its ghost values are zero by causality with the now ghost-zero mask. Thus \(R\mathbf Q=0\) in either case. The actual \(A\mathbf Q\) has numerical value \(W\) on live rows (true grade five) and is identically zero on ghosts by causality.

## The third live diagonal and clock

The actual row \(c\) has only the prior \(b\)-row as a possible earlier nonzero source of \(\mathbf Q\), because \(W'(a)=0\) and every ghost is zero in \(\mathbf Q\). Write \(\omega=A_{cc}\), \(\tau_b=A_{c,b}\). The genuine grade-five read and actual zero of the commutator give
\[
 \tau_b W'(b)+\omega W'(c)=W(c),\qquad
 (c-b-\omega)\tau_b W'(b)-\omega^2 W'(c)=0 .
\]
There is no hidden intermediate stage between live \(b,c\), and \(A_{bb}=0\). Eliminating the literal tap gives
\[
           \omega[W(c)+(c-b)W'(c)]=(c-b)W(c).
\]
The right hand side is nonzero, since \(a,b,c\) are distinct nonzero and the scalar roots of \(W\) are exactly \(0,a,b\). Thus the bracket and \(\omega\) are nonzero. With \(x=b/a,\ y=c/a\) this is
\[
 \frac{\omega}a=\frac{y(x-y)(y-1)}{2D},\qquad
                 D=2xy-x-3y^2+2y\ne0 .
\]
This rules out any exceptional pivot at \(D=0\); it is not assumed nonzero at an unknown candidate.

The true \(AC\mathbf Q\) scalar primitive is \(J(XW')=XW-JW\) at grade six. Numerically at \(a\) it is zero, so its grade-six discrepancy is \(JW(a)\). At \(c\),
\[
  (AC\mathbf Q)_c=b W(c)+(c-b)\omega W'(c)
\]
from the literal \(b\)-tap and diagonal. Subtracting the scalar primitive and applying the exact commutator equation gives the true grade-six error \(JW(c)-\omega W(c)\). Comparison on the genuine live \(X L_6'\) line yields
\[
       \frac{L_6'(c)}{L_6'(a)}=
          \frac{a\,[JW(c)-\omega W(c)]}{c JW(a)},\qquad
          JW(a)=-(2x-1)a^6/60\ne0 .
\]
On inserting the diagonal expression it is \(-y^2P/[(2x-1)D]\), with
\[
\begin{aligned}
 P={}&6x^2y^3-18x^2y^2+20x^2y-10x^2
       -4xy^4+8xy^3-6xy^2+5xy\\
    &+2y^4-3y^3 .
\end{aligned}
\]
The cleared equation \((2x-1)D L_6'(a y)+y^2P L_6'(a)=0\) is degree seven in \(y\) for fixed \(a,x\) (its leading degree-seven coefficient is \(-3(2x-1)\,5544a^5\ne0\)). The polynomial has the two already inadmissible roots \(1,x\): the normalized right-hand side evaluates respectively to \(1\) and the already paid two-clock ratio \(x^3(2x^2-6x+5)/(2x-1)\), with \(D\ne0\) at both. Thus at most five other distinct ratios \(c/a\) may occur. This is an exact projection, not a claim that all roots extend.

In the late chart it also supplies a direct check of the mixed \(\chi=\alpha/\gamma\). Write \(F_b,l_b,W_{g_*}\) as above, let \(J_S,L_S\) be the cubic's first and second primitives in the [late proof](../dirk12-fifteen-rank3-invisible-ordinary-ghost-chronology/README.md), and set \(\theta=A_{c,g_*}/q\). The true \(A(A\mathbf V)\) read at \(c\) gives
\[
 \theta=\frac{L_S(c)-\tau_b J_S(b)-\omega J_S(c)}{l_b},
 \qquad \tau_b=\frac{W(c)-\omega W'(c)}{W'(b)} .
\]
For \(j=5,7\) put \(K_j(s)=L_j'(s)-L_6'(s)L_j'(a)/L_6'(a)\). The actual Jacobi tap at the fourth ghost satisfies \(A_{s,g_*}=s\gamma\ell_{g_*}(\chi K_5(s)+K_7(s))\) by the zero \(a\)-tap. Thus the reverse-derived true \(\chi\) must satisfy the additional linear equation
\[
  \big[cK_5(c)-b\theta K_5(b)\big]\chi
                 +cK_7(c)-b\theta K_7(b)=0 .
\]
If its first coefficient is nonzero it solves for the mixed ratio from the first three ordinary clocks alone; if the first vanishes and the second does not, that scalar geometry is excluded. Neither coefficient is silently assumed nonzero. The reverse formula continues to use the actual unpaid \(\varepsilon_{12}\).

## The exact live higher pure ranks

The genuine grade-seven pure state \(R(A\mathbf Q)\) is zero at \(a,b\) by chronology, since \(A\mathbf Q\) is zero there and on all preceding rows. At \(c\) its actual value is \(-\omega^2 W(c)\ne0\). The actual four ghost columns \(A\mathbf e_g\in F_7\) already have two independent readings on \(a,b\), by the exact [ordinary ghost-tap rank](../dirk12-fifteen-rank3-invisible-four-ghost-variable-high-sites/tap-rank-and-moments.md). This third genuine pure word therefore raises the live \(F_7\) projection rank to at least three. Its upper bound is three: on nonterminal live rows \(T_7\) has polynomial profiles of degree at most seven, and a pure such profile \(p\) satisfies \(p(0)=0\) and \(\int_0^1 (1-X)p(X)Q(X)\,dX=0\) for all \(Q\in P_3\), by the actual \(7+4=11\) pairing. This gives
\[
                     p\in X\langle L_5',L_6',L_7'\rangle .
\]
A separate terminal coordinate is fixed for a pure vector by the ordinary constant pairing and its nonzero weight. Hence the live dimension is exactly three, and \(f_7=7\) after adding the four genuine ghost axes already in \(F_6\).

In both charts \(T_8\) on the nonterminal live rows has degree-at-most-eight polynomial profiles: at \(m=9\), \(\mathcal B_3=\langle\mathbf G\rangle\) solely equates the repeated pair, leaving arbitrary values on nine labels; at \(m=10\), it removes the degree-nine coefficient by the actual barycentric sum on ten labels. The degree-eight pure upper bound similarly gives \(X\langle L_4',\dots,L_8'\rangle\) by the true \(8+3=11\) pairing. The lower bound is the \(F_7\) profiles and their genuine ordinary clock lifts. Multiplying \(L_5'\) and \(L_7'\) by \(X\) gives nonzero \(L_4'\) and \(L_8'\) components, respectively: the upper neighbor is forced by leading degree, and the lower neighbor follows by symmetry of the \(X(1-X)\) weighted pairing and the nonzero upper neighbor of \(X L_4'\). Thus actual \(F_8\) live rank is five and \(f_8=9\).

At grade nine, the actual origin is zero for pure vectors, and the scalar probes of degrees \(0,1,2\) remain paid. On the other live coordinates these are three independent functionals, by any three distinct nonzero-weight live labels. This gives an upper bound \(11-1-3=7\) on the live pure rank. Clock lifting \(F_8\) supplies the seven formal profiles \(X\langle L_3',\dots,L_9'\rangle\) by the same two-neighbor argument. At \(m=10\) they are numerically independent on ten nonterminal labels. At \(m=9\) they have rank at least six on the nine distinct nonterminal labels (evaluation of degree at most nine has a one-dimensional kernel). A further genuine \(A\)-shift supplies a split of the physical pair in that case: for a true \(F_8\) state with nonterminal profile \(p=X L_8'\), \(\mathbf G\) annihilates its repeated-equal entries, while \(\mathbf G\cdot A\mathbf V=(N\mathbf G)\cdot\mathbf V=\mathbf H\cdot\mathbf V\ne0\). The last sum is the nonzero multiple of the leading degree-eight coefficient in the actual nine-label barycentric quotient of \(\mathbf H\). Therefore that \(F_9\) word is independent of all the repeated-equal clock lifts. The live rank is seven and \(f_9=11\) in either case.

No scalar exactness through degree twelve, positive physical weights, or clean reverse singleton has been assumed. The chronology and pure-space arguments are mathematical; the accompanying exact symbolic replay checks the third-row diagonal, polynomial, and two invalid-root factors.

    python3 -B verify.py
