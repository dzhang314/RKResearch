# Shared doubled endpoint, split quadratic graph, and two arithmetic singleton pairs

Assume the all-dirty strict ten-stage SDIRK floor of order at least eight over a characteristic-zero field, with exactly seven distinct clock labels and genuinely quadratic singleton-residual graph \(R\). Assume the actual endpoints share the same D (doubled) clock, and each actual first-three prefix is D,S,S (two later singleton clock labels in each orientation). The [endpoint star packet](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) already excludes either star and the shared-clock centered-even arithmetic case. This packet rejects the remaining **split, non-even arithmetic/arithmetic** graph, hence fully closes this shared-endpoint D,S,S/D,S,S shape. It says nothing about other prefix shapes or the unconditional stage lower bound. Signed weights and arbitrary characteristic-zero fields are allowed.

## Actual quadratic fit and scalar masks

Scale the common diagonal to one. A shared endpoint implies \(\ell=1/\gamma=2\), so \(t=x-1\) is centered, and both physical endpoint rows occur at \(t=0\). Write
\[
 R(t)=rW(t),\qquad W(t)=t^2-z t+w,\qquad r\ne0 .
\]
The shared D label \(0\) forces the intercept of \(F\) to vanish and \(Q\) to be odd, as in the endpoint star packet. If \(Q=t\) times a quadratic in \(t^2\) has a repeated squared root or has a zero squared root, the three distinct D labels must be \(0\) and one full opposite pair, making the leftover \(R\) centered-even. Likewise, when the two noncentral D labels choose a full opposite pair, the graph is even. Therefore in the genuinely non-even split case the two graph roots come from different nonzero opposite pairs, with \(z,w\ne0\). They are distinct, although the coefficient field need not contain their square roots. Their squared values \(a,b\) satisfy \(35ab-21(a+b)+15=0\). Since \(a+b=z^2-2w,\ ab=w^2\), the exact conic is
\[
                     35w^2+42w+15-21z^2=0.              \tag{1}
\]
Reduction of \(L_4(t)=t^4-6t^2/7+3/35\) modulo \(W\), with (1), gives
\[
        L_4\bmod W=\frac{35w^2-3}{21}
                         \left(z t-w-\tfrac35\right).     \tag{2}
\]
The leading scalar is nonzero because \(L_4\) has no common root with \(Q\), hence none with \(W\).

Let \(u,v\) be the actual forward and reverse arithmetic gaps. The four singleton labels are exactly \(u,2u,-v,-2v\) in original centered clocks. In particular \(u v\ne0\) and \(u+v\ne0\). Genuine arithmetic pays the same \(\kappa,D,q\) as the earlier packet. The guard \(u=2\) is also impossible here, and likewise \(v=2\): then \(\kappa=1\), and the [actual first-departure relation](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) forces the first residual departure to repeat the first clock. Its only other physical occurrence is the terminal. Thus there would be at most two different nonzero residual values, contrary to the constant and pure \(g,g^2\) paid moments (a degree-at-most-two polynomial with zero constant can equal one on those nonzero values). Together with nonzero arithmetic taps and denominator guards, this implies \(q(u)/\kappa(u)\ne1\), since
\[
               (q_{\rm num}-\kappa D)/\kappa
                        =-u(u-2)(3u-2).
\]

The genuine two arithmetic ratios are \(q(u)/\kappa(u)=W(2u)/W(u)\) and \(q(v)/\kappa(v)=W(-2v)/W(-v)\). They are **two affine equations** in \(z,w\):
\[
 w=A(u)+B_1(u)z,\qquad w=A(v)-B_1(v)z,\quad
 A(t)=\frac{-4t^3-7t^2+6t}{3t^2-8t+4},\quad
 B_1(t)=\frac{2t^3-4t^2+5t-2}{3t^2-8t+4}.
\]
All denominators here are nonzero by the actual guards \(t\ne2,2/3\).

Write \(H=h S_4\) for the singleton quartic, \(S_4=(t-u)(t-2u)(t+v)(t+2v)\) monic and \(h\ne0\). It obeys \(H\equiv L_4\pmod W\). In addition \(H(0)\) is known through the two literal D residuals at this shared clock, \(1/2,\lambda/2\), where \(\lambda=\kappa(u)W(-v)/[\kappa(v)W(u)]\) converts reverse residuals to original. Vieta gives \(B=-4 L_4(0)/\lambda\) for the quartic coefficient in \(U\); hence
\[
 H(0)=L_4(0)
       \frac{[\kappa(u) w-W(u)][\kappa(v) w-W(-v)]}{W(u)W(-v)} .
                                                               \tag{3}
\]
The two numerator differences cannot vanish: that would put a physical D residual on the graph. Denominator \(W(u)W(-v)\) is nonzero by the actual singleton residuals. Formula (3) uses the unknown common B only via Vieta, and does not presume that \(\lambda\) equals one.

## Genuine rank two

Let \(m=u+v,p=uv,d=u-v,E=d^2=m^2-4p\) in this section; \(m\) here is a clock-gap sum, not the interval half-length. Set \(D_1(t)=3t^2-8t+4\), and let \(A_1(t),B_2(t)\) be the numerators of \(A,B_1\). The exact symmetric polynomials are
\[
 \begin{split}
 N&=B_2(u)D_1(v)+B_2(v)D_1(u),\\
 M&=A_1(u)B_2(v)+A_1(v)B_2(u),\\
 J&=[A_1(v)D_1(u)-A_1(u)D_1(v)]/(u-v).
 \end{split}
\]
The last quotient is a polynomial (antisymmetric numerator). When \(N\ne0\), the actual affine fit gives \(w=M/N,\ z=d J/N\). Since \(z\ne0\), \(d,J\ne0\). Put \(Z=z/d=J/N\). Expanding \(S_4\) gives
\[
 S_4=t^4-3d t^3+(2d^2-5p)t^2+6pdt+4p^2,
\]
so its remainder is \(s_0+d s_1t\), with
\[
 s_0=w^2-w[E(Z^2-3Z+2)-5p]+4p^2,\qquad
 s_1=EZ(Z-1)(Z-2)+w(3-2Z)+p(6-5Z).
\]
The proportionality of (2) and this remainder gives \(5Zs_0+(5w+3)s_1=0\). For the other required equation use (3), \(H(0)=4hp^2\) and the linear remainder coefficient of \(H\equiv L_4\):
\[
 4p^2W(u)W(-v)(35w^2-3)Z/21
   = (3/35)[\kappa(u)w-W(u)][\kappa(v)w-W(-v)]s_1 .       \tag{4}
\]
All terms here are symmetric functions of \(u,v\). For example \(W(u)=(1-Z)u^2+w+Zp\), \(W(-v)=(1-Z)v^2+w+Zp\). Also each numerator difference has form \((Z-1-w)t^2+2w t-Zp\) at \(t=u,v\). Thus all products are computed without choosing a square root of \(E\).

The exact script forms integer numerator polynomials \(C,F,V\) of (1), the proportionality mask, and (4). It may remove only factors of the nonzero guards \(N,p,J,E,D_1(u)D_1(v),35M^2-3N^2\). Two resultants eliminating \(p\), of \(C,F\) and \(C,V\), have projected degrees 60 and 96. Their gcd has only \(m\), \(16m-7\), \(m^3-4m^2+10m-8\), and one irreducible octic factor. Every exact \(p\) fibre is retained before applying the following actual guards:

| Projected factor | Degree of common fibre in \(p\) | Reason rejected |
|---|---:|---|
| \(m=0\) | 6 | Forward and reverse singleton positions coincide when \(u+v=0\) |
| \(16m-7=0\) | 2 | \(N=0\) at every remaining root |
| cubic | 1 | \(N=0\) |
| octic | 1 | \(W(u)W(-v)=0\) |

The algorithmic audit uses the nonzero guard list directly, so it also checks the \(m=0\) replay without relying on a projected leading coefficient. No denominator-zero fibre is discarded on the assumption that rank is generically full.

## Genuine rank drop

If \(N=0\), consistency requires \(A(u)=A(v)\). Handle equal and unequal gaps before any division by \(N\).

If \(u=v\), then \(B_1(u)=0\), whose exact numerator is irreducible cubic. Now \(w=A(u)\) and \(S_4\) is even. Since \(z,w\ne0\), \(W(t)\) and \(W(-t)\) are coprime. The even difference \(H-L_4\) is divisible by both, so it equals
\[
 (h-1)\,[t^4+(2w-z^2)t^2+w^2].
\]
The quadratic and constant coefficients give two affine equations in \(h\). Substitute \(2w-z^2=-(5w^2/3+5/7)\) from (1); their determinant is nonzero in the cubic field. Thus the equal-gap rank-drop branch is impossible, not just unavailable to the rank-two solve.

If \(u\ne v\), consistency gives \(J=0\). The exact resultant of \(N,J\) in \(p\) is \(256m^2(3m-8)(16m-7)\) up to sign. The \(m=0\) fibre duplicates singleton positions as above; \(m=8/3\) leaves \(p=4/3\) and \(\{u,v\}=\{2,2/3\}\), both forbidden pivots. The genuine last fibre is \(m=7/16,p=-1/8\), with \(d^2=177/256\). Keep both choices of \(d\). In that exact quadratic ring the affine graph constraint is the same rational equation in both orientations:
\[
                  w=\frac{59}{128}\,Z-\frac14,\qquad Z=z/d .
\]
Substitution into (1) and the proportionality mask gives univariate polynomials in \(Z\) with gcd one. Thus even this true free-parameter rank drop fails, without needing central Vieta again.

## Replay and scope

Run `python shared_split_fullrank.py`, `python shared_split_reconstruct.py`, and `python shared_split_rankdrop.py`. Tested with SymPy 1.14 and python-flint 0.8. Only small exact polynomials and compact logs are needed. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSharedSplitArithmetic.lean) stages the denominator-cleared scalar remainder identities, not the full chronological exclusion. No native stock build or finite-characteristic bound is asserted.
