# Seven zero labels with the early mate at row six or seven

Take a strict ten-stage SDIRK tableau of order at least eight over a characteristic-zero field. Put \(\mathbf c=A\mathbf1\), \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), and normalize \(A'=A/\gamma,\ \mathbf x=\mathbf c/\gamma,\ D=1/\gamma\). The [eight-zero low-label](../sdirk-eight-eight-zero-low-labels/README.md) and [zero-ratio](../sdirk-eight-eight-zero-zero-ratio/README.md) reductions leave two distinct silent off rows at physical positions 1 and 2, and \(\kappa_R\ne0\). Assume exactly eight physical zeros with seven distinct labels. This packet considers a repeat linking one of early zero rows 6 or 7 to the actual rear.

**Result.** A late early mate is impossible in the silent-eighth or live reflected arithmetic phase, at any of the three rear rows. It is also impossible in the live-star phase with the terminal row as rear mate. Combined with the [early–early](../sdirk-eight-eight-zero-early-repeat/README.md) and [first-three early–rear](../sdirk-eight-eight-zero-early-rear/README.md) exclusions, the only possible seven-label chart has a **live star** and the repeated label connects row 8 or 9 to one of rows 3 through 7. The eight-distinct-label chart remains separate. No result for finite-characteristic tableaux or the unconditional ten-stage bound is claimed.

## 1. The extra Legendre condition at a late repeated label

The five early zero labels are all different. Let \(a,b,c\) be the first three, and \(q\) the one repeated later. Here \(q\) belongs to the fourth or fifth early row, so it is different from \(a,b,c\). Put \(\sigma(T)=(T-a)(T-b)(T-c)\), \(C'=\operatorname{diag}(\mathbf x)\), and \(U=\ker\operatorname{diag}(\mathbf g)\). The same supported column construction as in the [fourth-read packet](../sdirk-eight-eight-zero-early-rear/README.md#1-a-two-dimensional-forward-pure-space-produces-a-fourth-gate) gives an actual \(E_3\) input \(\boldsymbol\sigma\) with trace \(\sigma\), supported on \(U\). Its primitive discrepancy is \(\mathbf f=A'\boldsymbol\sigma-(J\sigma)(\mathbf x)\in F_4\), with \(J\) the formal integral from zero. The first three actual reads vanish by chronology.

The difference \(\delta\) of the two coordinates at \(q\) is not in \(W_2\). In fact the nonzero grouped barycentric pure row is detected by a singleton rear coordinate, and the scalar Hilbert pairing removes the ordinary part of any proposed expression for \(\delta\). Thus \(F_5|_U\cap\ker\delta\) is the span of \(L_{3,D},L_{4,D},L_{5,D}\), same as in the fourth-read packet. The product \((C'-qI)\mathbf f|_U\) has a scalar representative \(V\) in that span, vanishes at \(q\), and at \(a,b,c\) takes the values \(-(T-q)J\sigma(T)\).

Since \(q\) is not among \(a,b,c\), the polynomial \(V/(T-q)+J\sigma\) vanishes at those three distinct points and has degree at most four. Consequently
\[
  V=(T-q)\bigl[-J\sigma+(\alpha+\beta T)\sigma\bigr].
\]
This uses just polynomial divisibility and **does not invert the three-point Legendre evaluation matrix**. Pairing with \(1,T,T^2\) and writing \(I_D(T^j)=D^j/(j+1)\) shows that the three rows
\[
   (m_i,m_{i+1},n_i),\qquad
   m_i=I_D(T^i(T-q)\sigma),\quad
   n_i=I_D(T^i(T-q)J\sigma),\quad 0\le i\le2
\]
have zero determinant. All moments use degree at most seven. This forward determinant is valid for either placement of \(q\) among the last two early rows.

## 2. Independent ordinary two-row determinant

Let \(e\) be the other early clock after \(a,b,c\); thus the five are \(a,b,c,q,e\) in either order of their last two. For the finite rear gap charts, \(s=D-1,t=s-v,r=s-2v\) are distinct from \(a,b,c\), \(q\) is one of \(s,t,r\), and the six known labels have monic mask
\[
  P_6=\sigma(T-s)(T-t)(T-r).
\]
The seven-label nodal polynomial is \(P_6(T-e)\). Use ordinary exactness \(I_D(P_6(T-e))=0\) and the other ordinary mask \(R\) from the [singleton ratio table](../sdirk-eight-eight-zero-early-rear/README.md#2-ordinary-recovery-from-only-singleton-ratios), now with \(U_x=P_6/(T-x)\) instead of \(P_5/(T-x)\). The same derivation gives \(I_D(R(T-e))=0\). In particular the rear ratio uses only the two singleton rear labels. If row 8 is physically silent but duplicated, no grouped silence is assumed there.

For terminal star, take \(q=s=D-1,\ m=D-2\). Then \(t,r=m\mp(v-1)\) are the two singleton rear labels and \(B(t)=B(r)\). It gives \(I_D(\sigma(T-s)(T-e))=0\), and ordinary precision further gives \(I_D(\sigma(T-s)(T-m)^2(T-e))=0\). This is gap-free.

In all cases the two ordinary equations in \(e\) force the two-by-two determinant of their first two moments to vanish, without assuming a nonzero denominator. In the finite-gap chart the masks are \(P_6,R\); in terminal star they are \(\sigma(T-s)\) and \(\sigma(T-s)(T-m)^2\).

## 3. Exact projection and its leading-drop branch

The same front gates give \(a=1+2u,\ Q(u)=0,\ b^2-(2u+4)b+1+2u=0\) and \(C_3(c;D)=0\). We use the verified number-field tower of degree six with primitive \(u+b\) in terminal star, and degrees 18 or 36 with primitive \(u+b+2v\) in the two finite-gap branches. The replay constructs the tower, verifies irreducibility and inverse maps, and regenerates \(C_3\).

In the two determinant equations \(A_0=A_1=0\) just proved, degrees in \(c\) are 2 and 3. Write \(C_3=\ell_2c^2+\ell_1 c+\ell_0\). At \(\ell_2\ne0\) use the scaled variable \(L=\ell_2 c\), with \(L^2+\ell_1L+\ell_2\ell_0=0\). For each determinant, clear the appropriate power of \(\ell_2\), reduce to \(p+rL\), and take \(p^2-pr\ell_1+r^2\ell_2\ell_0\). A solution must annul both norms, even if the scaled quadratic is split or has a repeated root. Remove only factors of \(\ell_2\), \(D\), or \(s,t,r\) coinciding with \(a\) or \(b\) (only \(s\) is used in the star). Every removed factor is ruled out by an actual guard. The exact norm degree pairs before removing the linear guards, and after, are \((32,42)\to(28,30)\) in the six finite-gap charts, and \((30,42)\to(26,30)\) in the gap-free star.

The following fixed good reductions preserve both regular norm degrees and give constant gcd. A simple primitive root and all coefficients used in the reduction are checked. Over the exact characteristic-zero field, these conclusions use the unit leading coefficient of a guarded norm to force any hypothetical common root integral, and then reduce it in an algebraic closure of the residue field. They do not rely on residue field rational roots of \(D\).

| Phase | \(q=s\) | \(q=t\) | \(q=r\) |
|---|---:|---:|---:|
| Silent eighth | \((17,1)\) | \((17,1)\) | \((17,1)\) |
| Live arithmetic | \((31,8)\) | \((31,19)\) | \((31,19)\) |
| Live star | \((13,9)\) | Not covered | Not covered |

Here a pair records \((p,z_0)\) with \(z_0\) the simple residue of the primitive element. If \(\ell_2=0\), exact \(\gcd(\ell_2,\ell_1)=1\), so \(c=-\ell_0/\ell_1\). Substitute this into **each** determinant after clearing the necessary power of \(\ell_1\), take remainders modulo \(\ell_2\), and check that their common gcd with \(\ell_2\) is constant at the same degree-preserving reduction of \(\ell_2\). This controls all roots of the leading-drop polynomial without any ordinary moment or Legendre evaluation pivot.

## 4. Replay and native scope

Run `python check_late_mate.py PHASE SLOT` with SymPy 1.14 and Python-flint 0.8. Use `PHASE=ghost,arith` and rear `SLOT=0,1,2` (\(s,t,r\)), plus `PHASE=star SLOT=0`. Each run verifies the fixed residue listed above. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightEightZeroLateMate.lean) audits the division-free three-moment determinant. The ordinary two-row minors and quadratic norm are already native in the early-repeat companion. The rooted tableau ingress and characteristic-zero exact arithmetic remain separate from the native scalar statements.
