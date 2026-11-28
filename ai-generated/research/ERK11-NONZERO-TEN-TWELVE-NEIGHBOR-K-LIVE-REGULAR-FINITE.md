# Finite fully pivotable widths on the neighboring live cross block

**Scope.** In the all-live, half-clock two-carrier, seventeen-stage ordered ERK11 chronology with \(q=10,n=12\), both seventh boundaries new, full plateau pairs, and sole dormant physical 9 sharing the active singleton \(s=c_8\notin\{0,1,a,d\}\), assume \(K_0(a,b)\ne0\), \(b=1-d\). Keep the two fixed moment pivots and both raw affine slopes of the **original** fits live. Then the possible width pairs \((a,b)\) are confined to a finite algebraic set. This includes first losses of the auxiliary denominators used below, but **not** the original fixed-moment or raw-affine losses. It is not an exclusion of all finite widths or a stage-count improvement. The reflected neighboring coincidence gives the reflected result.

## The original true fits yield one irreducible width curve

The diagonal-pole exit already gives actual \(R_9\), measured \(u,v,b_9\), and its first left derivative coefficient. Oppose the left flank to actual \(R_9\). Write \(\ell_0,\ell_1\) for its two left derivative pairings. The measured actual \(L_7\) is proportional to
\[
 \ell_0D_L^a-\ell_1D_L^0.
\]
Oppose the right flank to this **actual \(L_7\)**, not a rotated surrogate. Its first derivative pairing is live: otherwise the actual seventh-boundary equation forces both pairings zero, impossible for a nonzero left derivative row when \(K_0\ne0\). Thus the true four stencil contacts are \([L_7,R_9]=[L_8,R_9]=0\) and \([L_7,R_{11}]=[L_7,R_{10}]=0\). In particular the right outer clock is \(1-z\), distinct from the corrected moment clock \(1-s\).

Use the same fixed columns and rank-one corrected Cramer determinants as in the [singular-width regular proof](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-K-REGULAR-EXIT.md), now with actual slopes in both orientations, **without reducing modulo \(K_0\)**. Polynomial gcd scales common to a slope pair, the moment minor bundle, or the temporal row are live by the corresponding true pivot. Let \(\mathbf c_0,\mathbf c_1,D,g_0,g_1\) be the resulting Cramer bundles and two affine coefficients. Form
\[
 (U_*,W_*,T_*)=\mathbf c_0g_1-\mathbf c_1g_0,\qquad
 p(Y)=g_0U_*+(-g_1T_*-g_0W_*)(Y-h).
\]
This is the physical first-pool line up to live multiplication by \(Dg_1g_0/w\), with \(w=a,b\) and \(h=w/2\). The true product parameter gives \(g_0\ne0\). Its two coefficient polynomials cannot vanish simultaneously at an actual candidate, so a common polynomial factor of the coefficients of either line is also live; divide it out.

The exact normalized line coefficient pairs have bidegrees \((55,50),(55,50)\) on the left and \((55,57),(56,57)\) on the right after physical reflection. Their physical projectivity determinant, up to a rational scalar, is a **single irreducible polynomial \(F(a,b)\)** of bidegree \((111,107)\) and total degree 218 over \(\mathbb Q\). It has \(12096\) nonzero coefficients before factor normalization. The replay exact-factorizes it; it does not assume irreducibility from a generic numerical rank. Every width in the stated regular chart satisfies \(F=0\). No leading coefficient of \(K_0\) is used in this construction.

## A transverse actual plateau equation

Take the actual two fitted hulls and shared fitted profile scale, as in the [same-singleton ghost and ordinary plateau exit](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-SINGLETON-DIAGONAL-POLE-EXIT.md). Put
\[
 D_s=-B_L(X)B_R(1-X)(X-s)(X-z),\quad
 \Omega=X(X-1)(X-a)(X-d).
\]
The actual response is \(P=\gamma P_*,Q=\gamma Q_*\), from the left fitted pair with one common scale. Use the ghost congruence
\[
 V_0+\gamma V_1=0\pmod{Q_*},\qquad
 V_0=D_s M_{\Omega Q_*}-\frac{J_0}{uv}Q_*(s)\frac{D_s}{X-s},
 \quad V_1=P_*^2 X(X-1).
\]
The ghost term counts dormant physical 9 in addition to the active singleton at the same clock. Select the **constant** coefficient of each remainder, and use \(\gamma=-[X^0]V_0/[X^0]V_1\) when this denominator is live. This fixes the rational formula globally, rather than switching coefficient indices at unverified sites. Use the root \(\xi\) of the fitted linear \(P\) to recover the third response \(B_\tau=(Q^2+\lambda D_s)/P\), with \(\lambda=-Q(\xi)^2/D_s(\xi)\). The fit case and all divisors here are tracked rather than silently assumed live.

Measure the ordinary left plateau mass \(B_a\) by the degree-three scalar test \(\Omega/((X-a)\Omega'(a))\), subtracting both the active singleton weights and the dormant \(b_9\) term. Calculate the active singleton sum via the inverse of \((X-a)Q_*\) modulo monic \(D_s\) and its degree-seven coefficient, as in the prior plateau proof. This avoids any division by \(D_s'(s)\) or other singleton pair gaps at the residue witness. Algebraically, the inverse can be fixed as the adjugate-of-multiplication formula in the monic quotient, with determinant a tracked denominator. Write \(f=-a^2/2\) for the literal first-row plateau response. The independent actual equation is
\[
 G=(\mu-f\nu)^2-(\nu-fB_a)(\tau-f\mu)=0 .
\]
It uses both ordinary plateau rows and the recovered third response. It is not the second-pool projectivity or the already imposed rank-one moment update.

At the exact coefficient witness \((p,a,b)=(17,7,7)\), the primitive \(F\) specializes to nonzero \(b\)-degree 97 and vanishes at \(b=7\); \(K_0\) in the companion normalization is \(12\bmod17\). All chosen original fit and auxiliary plateau denominators are units. In fact both physical projectivities pass. The ghost remainders in increasing coefficient order are \((3,2,11,7)\) and \((1,12,15,8)\); hence \(\gamma=14\). The fitted root \(\xi=7\) has \(D_s(\xi)=14\), \(\Omega'(a)=2\), and the inverse gcd is 1. Although \(D_s'(s)=0\) **in this residue**, the based quotient inverse is a unit, so the measured ordinary mass formula is legal. The resulting tuple \((B_a,\nu,\mu,\tau,f)=(0,0,8,11,1)\) gives
\[
 G=13\bmod17,\qquad G\ne0.
\]
In particular neither \(B_a\) nor \(\nu\) is used as a denominator. This is a coefficient witness, not a reduction or construction of a candidate tableau.

## Why this is a finite result, including auxiliary poles

Regard the chosen plateau calculation as one rational expression over \(\mathbb Q(a,b)\). It uses only rational operations, monic division, and the selected inverse by its determinant. Include all its denominators after clearing earlier ones: among them are the quartic leading coefficient of \(Q_*\), the linear coefficient of \(P_*\), the fixed scale-remainder coefficient and resulting scale, the \(D_s(\xi)\) factor, the plateau denominators, and the monic quotient inverse determinant. Each denominator and the terminal numerator reduce to nonzero at the single coefficient witness. Choose integral-local representations at 17 by the displayed construction. Since primitive \(F\) has nonzero reduction and \(F=0\) at the witness, Gauss's lemma over \(\mathbb Z_{(17)}\) shows **none** of those denominators or the final numerator is divisible by \(F\) over \(\mathbb Q[a,b]\).

At an actual width, with the original fits still live, either some first auxiliary denominator vanishes or all survive and \(G=0\). In either case \(F\) meets a polynomial coprime to it. Their \(b\)-resultant is nonzero (use primitivity of \(F\) in \(b\)); thus \(a\) is one of finitely many algebraic values, for each of finitely many polynomials. A nonzero irreducible \(F\) of positive \(b\)-degree has no identically zero vertical \(b\)-fiber: any common algebraic root of its \(a\)-coefficient polynomials would contradict primitivity. Consequently \(b\) also lies in a finite algebraic set. No claim is made that an exceptional denominator or a regular point of this finite set has already been excluded.

The deterministic exact replay uses python-flint 0.9.0 and no checkpoint or randomized search (reference wall time 17.805 seconds). This is a mathematical and exact-arithmetic width theorem, not a compiled full tableau result.
