# Corrected actual hole six: star-front fifth zero pivot excluded

Use the [corrected affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) and its [physical pure-four graph](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole67-clean-bridge/README.md). Work over a characteristic-zero field. This packet concerns an **ordinary hole at physical six**, a star front and a zero fifth slope in the remaining noncubic fifth-amplitude branch. It covers all actual ordinarily silent placements \(2,3,4,5,7,8\), independently of rear choice. Arithmetic fronts and actual hole seven are not considered.

The [cubic-fifth exclusion](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-cubic-closed/README.md) leaves
\[
 y=(3s-1)/2,\qquad h_5\ne H_4(y),
\]
where \(s=c_4/\gamma,\ y=c_5/\gamma\). With \(E_3(Y)=(Y^2-4Y+2)(Y-s)\) and literal \(H_4(Y)=(6-18Y+9Y^2-Y^3)/8\), put \(\eta=(h_5-H_4(y))/E_3(y)\ne0\). The division uses the actual three earlier clocks, all distinct from physical fifth. With \(D(Y)=d_2Y^2+d_1Y+d_0\) and actual \(D(s)\ne0\) as in the pure-four graph, write
\[
 U=\ell_L(y)+\tfrac43D(s)(5-s),\qquad V=d_2(y+s)+d_1.
\]
The literal fifth combined \(A'\boldsymbol h\) equation is \(\eta U=V\). In fact the three-tap quadratic for earlier amplitudes is \(P_h=H_4+E_3/8\), whose functional has amplitude slope \((5-s)/3\) from the three genuine tap moments. At \(h_5=H_4(y)\), the numerical \(A'\boldsymbol h-h_5\) read is \((y-a)(y-b)/4\); comparison with the graph and then substituting the actual \(h_5=H_4(y)+\eta E_3(y)\) gives exactly \(\eta U=V\). Here the line \(\ell_L\) has constant \(4(1-2d_0)/3\) and slope \(8(d_2-70\gamma^4)\), from the constant and fourth coefficients of \(L_4(\gamma Y)-\ell_L(Y)H_4(Y)=(Y^2-4Y+2)D(Y)\).

## True slope loss

If \(U=0\), then \(V=0\). Since \(d_1,d_2\) are coprime, \(d_2\ne0\) and \(s=(d_2-2d_1)/(5d_2)\). The exact homogeneous substitution in \(U\), clearing \((5d_2)^3\), gives \(d_2 P_{12}(\gamma)/3\), with the full degree-twelve polynomial in the replay. Therefore \(P_{12}(\gamma)=0\). No coefficient of the actual \(\eta\) is inverted or assigned on this branch.

Put \(R=r/\gamma\), \(G=R^4-16R^3+72R^2-96R+24\), and
\[
 M=R^4/4-R^3-(s+4)(R^3/3-R^2)+(4s+2)(R^2/2-R)-2s(R-1).
\]
At the actual ordinary hole-six stage the true amplitude is zero. Its four earlier nonfirst amplitudes are interpolated by **the cubic** \(H_4+\eta E_3\), not by \(H_4\), since that cubic matches the root values at \(a,b,s,y\). The paid \(D(s)\) row-six gate yields
\[
 (9-8\eta)L_4(r)+D(s)(G-32\eta M)=0.                      \tag{1}
\]
Indeed \(D(s)v_A=D(s)v_\tau=L_4(r)/4\), the first three strict tap moments are \(R-1,\ R^2/2-R,\ R^3/3-R^2\), and their fourth coefficient read is \(R^4/4-R^3+v_\tau\). Substituting the cubic's coefficient vector gives (1) after multiplying by \(32D(s)\).

There is a quartic coefficient \(\Lambda\ne0\) with
\[
 8\gamma^3 H(X)=C_3(X)+8\eta E_3^*(X)+\Lambda E_4^*(X),
\]
where \(C_3=6\gamma^3-18\gamma^2 X+9\gamma X^2-X^3\), \(E_3^*(X)=(X^2-4\gamma X+2\gamma^2)(X-\gamma s)\), and \(E_4^*(X)=E_3^*(X)(X-\gamma y)\) denotes polynomial multiplication by the factor \(X-\gamma y\). This follows by matching at the actual four early clocks. Thus the three paid moments \(I((X-r)X^j H)=0\) for \(j=0,1,2\), together with (1) multiplied by \(\gamma^4\), form four homogeneous scalar rows in \((1,\eta,\Lambda)^{\mathsf T}\). All four three-row determinants must vanish. This tests existence without dividing by a rank-two minor in the remaining moment matrix.

## Exact specialization

At prime 1009 the complete monic degree-twelve \(\gamma\) projection has a single irreducible component with multiplicity one. The reduction verifies \(\gamma,d_2,D(s)\) are units. All coefficients of the moment-only determinant are integral with a leading unit in its true degree three in \(r\), so every actual \(r\) at this \(\gamma\) is integral over the corresponding local ring and must reduce in its full monic fiber. The other three determinants have full degree six and the gcd of all four is one. Their equations depend only on \(\gamma,r,s\), not on any assumed reduction of \(\eta,\Lambda\) or of a hidden tableau. No candidate in this fifth zero-slope branch is possible.

Replay `python3 check_zero_pivot.py` with `sympy==1.14.0` and `python-flint==0.9.0`. It verifies the homogeneous rational projection, the genuine row-six linear coefficients, and the complete residue-gcd calculation. The original pure-four graph and chronology are source proofs, not new native Lean claims. A remaining star-front actual hole-six case must have \(y=(3s-1)/2,\ h_5\ne H_4(y)\), and now **\(U\ne0\)**. The unrestricted **10–11** interval remains.
