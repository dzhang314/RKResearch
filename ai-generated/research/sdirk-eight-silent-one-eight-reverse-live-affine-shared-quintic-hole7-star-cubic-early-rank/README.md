# Corrected actual seventh hole, cubic-fifth star front: early profile rank loss excluded

Use the [actual cubic fifth chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole7-star-cubic-zero-slope/README.md). The corrected ordinary hole is physical seven, star front, actual fifth amplitude is \(H_4(y)\), and all nonfirst clocks are distinct. Characteristic zero is assumed, not ordering. This proof works for every actual \(\zeta=2,3,4,5,6,8\) and rear phase, without reconstructing the actual sixth clock.

Suppose the initial two-clock profile anchor \(\Delta\) is zero. By actual early consistency both interpolation slopes \(L_*,K_*\) obtained from \(L_4(\gamma a)/h_a,\ L_4(\gamma b)/h_b\) and the corresponding \(K_3\) values vanish (see the [homogeneous anchor proof](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-early-rank-closed/README.md)). The standalone replay computes their rational polynomials. In particular \(L_*=\ell_1=2\Pi(\gamma)\) for \(\Pi=1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1\), and \(K_*(r,\gamma)\) has degree three in \(r\). Thus here \(\ell_L=\ell_0\) is constant; exact \(\gcd(\ell_0,\Pi)=1\) gives \(\ell_0\ne0\).

In the affine profile description from the cubic fifth,
\[
 8\gamma^3 H=C_3+\theta P_L+\chi E_2,\qquad
 P_L=E_2(d_2X^2+\gamma d_1X),\quad E_2=X^2-4\gamma X+2\gamma^2 .
\]
For fixed \(\gamma,r\), the three homogeneous paid conditions \(I((X-r)X^jH)=0\), \(j=0,1,2\), are an affine system in \(\theta,\chi\). At prime 1009 the full monic quartic \(\Pi\) remains irreducible and the \(r\) parent \(K_*\) retains degree three and irreducibility. Consequently any actual characteristic-zero \(\gamma,r\) on this rank-lost chart are algebraic and have integral reductions in the entire tower. Over its first degree-four field the common gcd of the full monic cubic \(K_*\) with all three two-column minors of the moment system is one. Thus the moment columns have rank two at every reduced root and therefore also at each actual characteristic-zero candidate. This does not assume that \(\theta,\chi\) reduce.

But \(H^\circ=L_4/\ell_0\) is already a solution in precisely the same affine profile space. Indeed
\[
 L_4(\gamma Y)-\ell_0 H_4(Y)=(Y^2-4Y+2)D(Y),
\]
and after scaling to \(8\gamma^3 H^\circ\) and writing \(X=\gamma Y\), the quadratic factor is proportional to \(d_2X^2+\gamma d_1X+\gamma^2d_0\), so its correction lies in the span of \(P_L,E_2\). Its paid moments are zero by Legendre orthogonality. Rank two forces \(H=H^\circ\). Then \(I(H)=0\), contradicting \(\beta=b_r H(r)\ne0\) in the actual nonagreement chart. No degree-drop root is discarded from a hidden tableau, and no modular zero of the fourth pivot is interpreted as a source zero.

Replay `python3 check_early_rank.py` with `sympy==1.14.0` and `python-flint==0.9.0`. The arithmetic replay is standalone. This source result does not claim a new native Lean theorem, a closure of the complementary early rank, or a change to **10–11**.
