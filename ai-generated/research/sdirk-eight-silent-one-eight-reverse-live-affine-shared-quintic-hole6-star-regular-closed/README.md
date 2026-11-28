# Corrected actual sixth-stage ordinary hole: last star-front branch excluded

This packet completes the **star-front** part of the corrected genuine affine shared-quintic ordinary-hole-six chart for strict ten-stage SDIRK8 over a characteristic-zero field. In this chart the sole nonzero quadratic defect is on ordinarily and reversely silent physical one; the remaining nine physical clocks are distinct. Eight are ordinary and one extra \(\zeta\) is ordinarily silent but reverse-live. The unique common root \(r\) of the affine reverse numerator and genuine quintic mixed numerator is actually ordinary, here physical six. Its actual cubic amplitude is zero but the continued quartic satisfies \(H(r)\ne0\). Neither sign nor ordering is used.

Use the [physical pure-four graph](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole67-clean-bridge/README.md). A star front satisfies \((y-(3s-1)/2)(h_5-H_4(y))=0\), with \(s=c_4/\gamma,\ y=c_5/\gamma\). The [placement ledger](STAR-HOLE6-LEDGER.md) names the independent cubic, zero-fifth-pivot, and early-anchor rank loss closures. Here \(y=(3s-1)/2\), \(h_5\ne H_4(y)\), true fifth pivot \(U\ne0\), and initial two-clock profile determinant \(\Delta\ne0\). No restriction on the ordinarily silent placement or rear phase is added.

## A physical quadratic with three fraction-free coefficient gates

Let \(q=c_4\), \(q'=c_5=(3q-\gamma)/2\). Write
\[
 \begin{aligned}
 C_3(X)&=6\gamma^3-18\gamma^2X+9\gamma X^2-X^3,\\
 E_2(X)&=X^2-4\gamma X+2\gamma^2,\\
 8\gamma^3 H(X)&=C_3(X)+E_2(X)(A_0+B_0 X+C_0X^2).
 \end{aligned}
\]
The last equation follows from the two literal front amplitudes and \(C_3(X)=8\gamma^3H_4(X/\gamma)\); \(C_0\ne0\) because \(H\) is a genuine quartic. Define \(J_j(Q)=I((X-r)X^jQ)\). The three paid conditions for \(H\), \(j=0,1,2\), give the moment matrix with entries \(J_{i+j}(E_2)\), \(0\le i,j\le2\), and right side \(-J_i(C_3)\). Its determinant \(h\ne0\): otherwise a nonzero polynomial \(E_2\) times a quadratic has the same three homogeneous moments, hence lies in \(\operatorname{span}(L_4,K_3(X,r))\) and vanishes at both early clocks, contradicting \(\Delta\ne0\). For the indicated span, the moments imply \(I(X^jQ)=I(Q)r^j\) for \(j\le3\); subtract \(I(Q)K_3\) and use the nonsingular degree-three ordinary moment matrix.

Let \(A_N,B_N,C_N\) be the three Cramer numerators, and use the exact actual fourth root
\[
 Q(q)=A_N+B_Nq+C_Nq^2=0,\qquad C_N=hC_0\ne0.
\]
In the [zero-fifth-pivot notation](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-zero-pivot-closed/README.md), put \(\eta=(h_5-H_4(y))/E_3(y)\), \(D_p=\gamma^2D(s)\), \(U_p=\gamma^3U,\ V_p=\gamma V\). Since the exact physical quadratic \(A_0+B_0X+C_0X^2\) vanishes at \(q\), its value at \(q'\) is \((q'-q)(B_0+C_0(q+q'))\). Here \(q'\ne q\) and both are distinct from the first two actual early clocks. Therefore the **actual** fifth amplitude gives \(8\eta=B_0+C_0(q+q')\). Set \(N=B_N+C_N(q+q')\). The actual fifth and hole-six equations become
\[
 \begin{aligned}
 F &= U_p N-8\gamma^2 V_p h=0,\\
 T &= (9h-N)\gamma^6 L_4(r)+D_p(h G_p-4N M_p)=0 ,
 \end{aligned}
\]
where \(G_p=\gamma^4 G(r/\gamma)\) and \(M_p=\gamma^4 M(r/\gamma,s)\) are the literal polynomials in the zero-pivot companion. No actual value was assigned to \(H(r)\) at the hole.

Take the fraction-free remainders of \(F,T\) modulo \(Q\) in \(q\). In addition to the true \(\gamma,h,C_N/\gamma^2\) guards, \(\Pi=1400\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1\ne0\): it is half the early \(L_4/h_i\) interpolation slope. If it vanishes, the early true readings and \(\beta\ne0\) make the \(K_3/h_i\) interpolation slope vanish too, contradicting \(\Delta\ne0\). Removing only powers of those exact true guards gives linear polynomials \(f,t\) in \(q\), of respective bidegrees \((r,\gamma)=(9,19),(13,26)\). Both must vanish, without requiring either leading linear coefficient to survive. The three padded resultants
\[
 \mathcal A=\operatorname{Res}_q(Q,f),\quad
 \mathcal B=\operatorname{Res}_q(f,t),\quad
 \mathcal C=\operatorname{Res}_q(Q,t)
\]
after the same exact guard removals have degrees \((15,29),(16,30),(23,43)\). There is no division by a resulting linear coefficient.

## Exact diagonal and all genuine guard drops

The **exact** \(\operatorname{Res}_r(\mathcal A,\mathcal B)\) has degree 847, computed directly over \(\mathbb Q\) in FLINT, without a CRT or large saved coefficients. Its full monic factorization has degrees with multiplicities
\[
 1^{42},\quad 4^6,\quad 4^{27},\quad 12,\quad 12,\quad 30,\quad 144^2,\quad 331 .
\]
The exact \(1^{42}\) and \(4^{27}\) are \(\gamma\) and \(\Pi\). The other quartic is the normalized \(d_2\). **\(d_2\) is not a true nonzero guard here**; its entire component is tested separately.

For the quartic and both degree-twelve fields, compute the common gcd of the three \(r\)-polynomials with the cubic guard \(C_N/\gamma^2\), by exact remainders in that cubic. The degrees are \(3,1,1\), respectively. In the degree-thirty field use \(h=\det M\) as the cubic guard, with exact common gcd degree one. These are exact **lower** bounds for the degree of the full common \(r\)-gcd. For each of these monic exact diagonal factors, reduce at 1009, keeping all residue components. The three original \(r\) degrees remain \(15,16,23\), and the full modular common gcd degrees match the exact lower bounds. This bounds the characteristic-zero common gcd above by the same number: every root of a full-degree \(r\)-parent is integral at the residue prime because its leading coefficient is a unit. The monic exact common gcd therefore has integral coefficients (elementary symmetric functions of those roots), retains its full degree, and still divides all three reductions. Consequently its exact degree equals the degree of the common gcd with the genuine guard. Every root in these diagonal fields **actually violates** that guard; no accidental modular guard zero is used.

The degree-144 exact monic factor has reduction coprime to the reduced auxiliary \(\operatorname{Res}_r(\mathcal A,\mathcal C)\) (degree 1230 modulo 1009), so cannot contain any actual \(\gamma\); the monic exact factor is integral at 1009 and the auxiliary exact resultant commutes with this reduction. This avoids a second large exact projection without replacing the full degree-847 parent by a modular guess.

## All physical terminal placements in the remaining field

The whole monic degree-331 factor remains. Its modulo-1009 irreducible degrees are \(1,19,33,65,100,113\), all simple. In every component all \(r\) degrees remain \(15,16,23\); their common gcd is linear. On every such \(r\) root, \(C_N,h,\gamma,\Pi,L_4(r)\) are units. The full \(q\)-parent has degree two, and the common gcd of \(Q,f,t\) is linear. Reconstruct monic \(H\) from \(hC_3+E_2(A_N+B_NX+C_NX^2)\), using its full leading unit \(C_N\), and use true \(q'=c_5=(3q-\gamma)/2\). These leading checks show that any actual algebraic \(\gamma,r,q\) reduce into these complete fibers. They do not assume integral coefficients for an unknown tableau.

The [corrected signed nodal identity](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-signed-nodal/README.md) requires the remainders of \(D_7\) and \((X-r)L_4\) modulo monic \(H\) to be proportional. The [star cubic-fifth companion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-cubic-closed/README.md) gives the actual rear polynomials and homogeneous endpoint rules, of degrees \(2,5,4\) for ordinary star, ordinary arithmetic, and actually silent eighth respectively. Those identities use only the true tail amplitudes and distinct clocks, independent of fifth profile; the explicit leading units for monic \(H\) are \(2\gamma^4,-8\gamma^4,\gamma^4\). Every factor is kept. For \(\zeta=2,3,4,5\) explicitly omit its own actual early peg from the known ordinary semipolynomial; use its own penultimate equation and the six-peg signed condition with terminal weight equality homogenized, never divided. Use all seven actual ordinary nonhole pegs directly for \(\zeta=7\) and the actual terminal equality, with no substituted \(z\). For \(\zeta=8\), no ordinary eighth factor is imposed. Ten ordinary star factors and thirteen ordinary arithmetic factors each exclude all five labels \(2,3,4,5,7\), with true physical four and five **separate**; ten silent-eighth factors exclude \(\zeta=8\). The two early root signs are included by testing both early labels, with no chronological exchange assumption.

## Replay and formal scope

Run `python3 check_regular_closed.py` with `python-flint==0.9.0`. Its two files are standalone, build all exact coefficients at runtime, and need no sibling executable or network after installation. The [native scalar Lean bridge](../../lean/RKCert/ReviewedNative/SDIRK8HoleSixCompactProjection.lean) checks fraction-free moment Cramer, transport of literal fourth/fifth/sixth equations, quartic reduction, and two homogeneous linear projections, over a commutative ring. The [Lean/Mathlib 4.36 transcript](lean-4.36.0-replay.txt) records the native check. The chart extraction, exact factorization and finite arithmetic are source proofs, not claimed as end-to-end Lean theorems. This closes the final **star-front hole-six** branch; arithmetic-front hole six and actual hole seven stay separate. The unrestricted strict SDIRK8 stage bound remains **10–11**.
