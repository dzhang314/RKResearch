# One-front Gauss-double cuts: shared reverse root and active Gauss front

Use the [independent six-clock chart](../sdirk-eight-silent-one-seven-six-anchored/README.md) at the ten-stage strict SDIRK8 floor over a characteristic-zero field. There is one invisible physical nonzero quadratic residual (stage one), seven active physical stages at six distinct active clocks, and independent active \(\boldsymbol h,C\boldsymbol h\). The sole doubled active clock is a Gauss root \(r\); the actual two amplitudes there differ. Other active clocks carry a nonzero common multiple of \(p_0(Y)=L_4(Y)/(Y-r)\). Exactly one literal front is active and the reverse quadratic factor \(k=1+2u-u^2\) is nonzero, where \(u=(c_{10}-c_9)/\gamma\).

**Result.** If the separate reverse-root clock \(z\) is the literal silent front and contains both physical silent zero rows, we exclude the remaining active-front singleton cases, completing that shared-root chart together with [the Gauss-copy predecessor](../sdirk-eight-silent-one-seven-six-one-front/README.md). If \(z\) is elsewhere, so has only one silent occupant, we exclude every case with the active literal front clock equal to \(r\). The separate root with a singleton active front is not included. This does not address the dependent six-clock case, seven or more distinct clocks, or change the unconditional **10–11** interval.

## Shared root at the literal silent front

Write \(z=\gamma Z_0,\ x=1-\gamma,\ c=c_9=x-\gamma u\) and \(d=c_8\) when physical eight is active. The ratio polynomial for the actual arithmetic third-from-last active stage is \(H k_d=-k T\), with
\[
 H=-2+u+4u^2-u^3,\qquad T=4u^3-12u^2+3u+2 .
\]
In star use \(H=1,k_d=k\). The actual singleton tail equations from the affine reverse multiplier root are
\[
 (x-z)h_9=k(c-z)h_{10},\qquad H(x-z)h_8=(Hk_d)(d-z)h_{10}
\]
when eighth is active. A doubled Gauss coordinate keeps its actual \(h\); it is not assigned the singleton polynomial.

* **Physical eighth active, \(p_0(z)\ne0\).** The exact [earlier tail projections](../sdirk-eight-silent-one-seven-six-reverse/README.md) are independent of the scale of \(p_0\) and of the individual silent defects. Reuse their finite characteristic-zero diagonal and gap polynomials without importing the earlier chart's front exclusions. In particular the arithmetic projection retains its separate degree-three leading locus. The known scale now comes from the actual non-Gauss active front, not from either silent stage at \(z\).
* **Physical eighth active, \(p_0(z)=0\).** This case cannot be removed just because at least one literal silent defect is nonzero. Here \(z\) is a Gauss root different from \(r\), and \(\gamma\) is in the monic cubic algebra \(p_0(\gamma Z_0)=0\). The terminal \(x\ne r\) is checked as a unit. Divide \(p_0(Y)=(Y-z)U(Y)\) in that algebra. A singleton ninth obeys \(U(c)=kU(x)\). Because \(U\) is quadratic, after dividing by the nonzero \(u\) its equation is linear in \(u\), with checked unit slope \(\gamma^2[Y^2]U+U(x)\). If eighth is singleton its equation is \(HU(d)=(Hk_d)U(x)\), which is a unit at the forced gap. If eighth is \(r\), the necessary clock equality itself fails at that gap. If ninth is \(r\), set \(u=(x-r)/\gamma\) and test the singleton eighth equation. This covers the otherwise unguarded zero-amplitude exception. [Replay](common_rear.py).
* **Physical eighth silent.** Its actual weighted successor taps give \(2(z-x)=\gamma k(u-2)\); no reflected normalization at its zero weight is taken. Thus
  \[
  \gamma=(1+Z_0-k(u-2)/2)^{-1}.
  \]
  If \(x\) or \(c\) is \(r\) its actual clock gives the exact cubic gap condition. Otherwise compare the two physical singleton tails. Cancel \(-\gamma k/2\) from the ninth comparison to obtain \((u-2)p_0(c)-(2u+k(u-2))p_0(x)=0\); after substituting this actual diagonal, clearing its denominator, and removing only known impossible roots, the monic degree is eleven. These projections include \(p_0(z)=0\); there is no division by it in this branch. [Replay](common_rear.py).

Since row four cannot repeat a literal front clock by its actual three-tap solve, it is active. The ordinary active-front and tail pegs, with \(r\) included even if its ordinary aggregate is zero, reconstruct one or two missing singleton clocks by signed Hankel once at least four pegs are known. If a sparse silent-eighth placement has only three pegs and row four is at \(r\), the actual anchoring and row-five two pure-four polynomials exclude every unpegged singleton after removing the one padded front root. Otherwise in that sparse case row four is an ordinary singleton and its exact cubic \(H_4-P\), with padded front root removed, adds a fourth peg. Here \(P\) refers to the normalized nonzero common scale of \(p_0(\gamma Y)\); it is not a physical amplitude at \(r\).

Retain the actual \(h\) as a free affine variable at a new \(r\), or compare derivatives with a padded earlier \(r\) to force a forbidden literal duplicate. If physical row five is the second silent occupant of \(z\), its literal pure-four formulas are affine in its actual \(h\) at this fixed clock. The first occupant, the literal silent front, has the **padded** same row-five formulas at its own \(h\). Their weighted read at the shared clock equals the affine formula at virtual defect \(P(z/\gamma)\), by the paid \(\boldsymbol w\) transport. This yields the same two literal tests evaluated at the virtual defect, without requiring that either silent's actual \(h\) equals it. [Replay](shared_literal.py).

## Sole separate silent root, active literal front at \(r\)

Let \(R=r/\gamma\) denote the active literal front's fixed normalized clock. Thus \(\gamma=r/R\) in the exact Gauss field; \(x\ne r\), since otherwise \(r=R/(1+R)\) in the quadratic front field contrary to the exact Gauss quartic degree. The cubic \(p(Y)=p_0(\gamma Y)\) has an unknown common scale. Both physical rows four and five are on the actual affine pure-four profile, including either with zero weight at the sole separate root.

The earlier scalar tail comparisons are homogeneous in the scale of \(p\). With \(X=x/\gamma\), write the two normalized singleton equations as \(B_i-A_i Z=0\), \(Z=z/\gamma\). At a singleton \(A_i\ne0\): \(A_i=0\) would make \(B_i=(X-c_i/\gamma)H_i p(c_i/\gamma)\ne0\). Thus solve for \(Z\) from the available singleton tail and eliminate it between two where appropriate. A known tail copy at \(r\) instead fixes its gap. If eight is silent, read its actual \(Z=X+k(u-2)/2\). This produces the same fixed-gap, finite cubic, or impossible star charts while preserving the separate physical silent position. [Replay](gauss_separate.py).

### Two chronological front reads

Row four cannot be at the earlier \(r\). Write its normalized clock \(s\) and actual \(h=H_4(s)\) from the literal three-tap cubic. Let \(v\) denote either \(\tau_4\) or \(Ah\), \(v_4(s)\) its literal polynomial, and \(q_v=v_{\rm front}/h_{\rm front}\) at the earlier active Gauss stage. The numerator \(v_4(s)-q_v H_4(s)\) has the padded factor \(s-R\) exactly, so set
\[
 V_v(s)=\frac{v_4(s)-q_vH_4(s)}{s-R}.
\]
For row-five clock \(y\ne R\), the profile fixes \(H_5=H_4(s)p(y)/p(s)\). The affine pure-four read expressed through the actual three strict taps must satisfy the denominator-cleared relation
\[
 p(s)\bigl(v_5(y,H_5)-q_v H_5\bigr)=V_v(s)(y-R)p(y).
\]
This uses \(p(s)\ne0\) when four is active; when four is the sole silent at \(Z\), the exact fixed tail fields give both \(p(Z),H_4(Z)\) units. The resulting two polynomials have the exact padded factor \(y-s\), inadmissible since four and five cannot share a singleton or the sole inactive root. If row five is at the earlier \(R\), retain its actual unknown amplitude instead: the two affine derivatives in \(H_5\) minus their required slopes are coprime linear polynomials in \(s\). Thus a different \(h\) cannot occur there; an equal \(h\) would force the padded literal duplicate, also impossible.

When the sole silent is early, the two quotient cubics at \(s=Z\) or \(y=Z\) have unit resultant. If both four and five are active, eliminate \(y\) from the cubic pair. Guard only \(s=A_0,B_0\), \(p(s)=0\) and \(H_4(s)=0\); these are physically inadmissible. The exact row-four projection has monic degree nine. Split its degree-two locus where both cubics vanish at the forbidden padded \(y=R\), and remove the exact \(y-R\) factor from both cubics **only there**; retain the degree-seven complementary locus unaltered. This keeps every possible other \(y\) even in the padded component. [Replay](gauss_front_pair.py).

Add \(s,y\) as ordinary pegs. With six known sites use the two necessary degree-six/seven nodal moments. With five use a signed rank-one Hankel. If the two physical \(r\)-amplitudes are known (earlier front and tail), use the following additional mass law, compatible even with zero aggregate ordinary mass at \(r\).

### Signed mass and the sparse silent eighth

Let \(P=\sigma p_0\) in physical clock units represent the singleton profile, including the chosen defect normalization. At \(r\), let \(H_1,H_2\) be the two actual amplitudes, \(p=P(r)\), and \(w\) their total ordinary weight. Let \(\nu=\int_0^1p_0(Y)\,dY/p_0(r)\). Since \(p_0^2-p_0(r)p_0\) is \(L_4\) times a polynomial of degree at most two, \(\int p_0^2=p_0(r)\int p_0\). Paid first and second defect moments and scalar quadrature imply the signed physical sums at \(r\) are \(b_1H_1+b_2H_2=(w-\nu)p\) and \(b_1H_1^2+b_2H_2^2=(w-\nu)p^2\). Eliminating these two sums gives the necessary
\[
 w(p-H_1)(p-H_2)=\nu p(p-H_1-H_2).
\]
Use the actual homogeneous tail comparison to get \(H_2\) at the tail copy from the terminal singleton, rather than setting \(H_2=p\). If \(V_r\) is the scaled product of the other five nodal factors, ordinary precision gives \(wV_r(r)=\int V_r\). Multiply the mass equation by \(V_r(r)\) to check it without a weight division.

The sparsest placement has physical eight silent and \(c_9=r\). Then \(x,r,s,y\) are four known distinct pegs. Their signed Hankel gives a scaled quadratic for the two remaining singleton nodes. At physical row six the preceding clocks are \(A_0,B_0,s,y\), and the actual normalized \(h_5=P(y)\) uses the determined scale. The literal marked-tap elimination from the [anchored row-six mask](../sdirk-eight-silent-one-seven-six-anchored/README.md) gives another necessary polynomial at the sixth clock, without dividing by its marked predecessor factor. Combine the scaled quadratic and this polynomial by a denominator-free pseudo-remainder resultant. In the finite quotients a linear combination of the remaining early pure-four equation, the mass law, and this last mask is a unit. This closes the physical silent eighth without assuming its last active tail has three normalized rows or equating its unseen defect with an active copy.

## Verification

Run `python3 check_shared_front.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the repository's sibling proof tree; the replay needs no network after installing those packages. It verifies 52 shared-root and 32 active-Gauss-front orientations. Exact finite projections and known forbidden factors are justified before reduction. All final monic quotients, their pivots and residual units are checked at \(p=1009,t=285\), using the same preserved-degree coprimality method as the predecessor packets. There is no reduction of an unknown tableau. The [Lean source](../../lean/RKCert/ReviewedNative/SDIRK8GaussDoubleSharedFront.lean) checks the affine virtual read, the cleared silent-eighth diagonal, and the doubled-clock mass equation in Lean/Mathlib 4.36.0 with standard axioms. The chart and arithmetic replay are source-level.
