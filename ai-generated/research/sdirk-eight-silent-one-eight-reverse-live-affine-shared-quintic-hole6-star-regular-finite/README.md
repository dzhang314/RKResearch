# Regular exceptional star-front sixth hole: finite scalar localization

Work in the [corrected affine shared-quintic ordinary-hole chart](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole-literal-closed/README.md) over a characteristic-zero field, not necessarily ordered. Consider an actual ordinary hole at physical stage six, a star front, and the **remaining** exceptional fifth clock \(y=(3s-1)/2\) with \(h_5\ne H_4(y)\). The [cubic-amplitude case](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-cubic-closed/README.md) and [zero fifth-pivot case](../sdirk-eight-silent-one-eight-reverse-live-affine-shared-quintic-hole6-star-zero-pivot-closed/README.md) are separate exclusions. This packet shows the remaining \((\gamma,s,r)\) lie in a **finite** algebraic set. It does not exclude all its fibers or prescribe any \(\zeta\) location.

Use the notations and actual reads of the zero-pivot companion: \(s=c_4/\gamma\), \(r\) the ordinary hole clock, \(D(s)\ne0\) the true fourth pivot, and
\[
 U=\ell_L(y)+\tfrac43D(s)(5-s),\quad V=d_2(y+s)+d_1,\quad
 \eta=(h_5-H_4(y))/E_3(y).
\]
Here \(U\ne0\) and \(\eta U=V\). Define physical-clock polynomials
\[
 C_3=6\gamma^3-18\gamma^2 X+9\gamma X^2-X^3,\quad
 E_3^*=(X^2-4\gamma X+2\gamma^2)(X-\gamma s),\quad
 E=E_3^*(X-\gamma y),\quad F=U C_3+8V E_3^* .
\]
The multiplication notation in \(E\) means the factor \(X-\gamma y\), not composition. The continued quartic is a nonzero scalar times \(F+\Lambda' E\) for some \(\Lambda'\), by literal early interpolation and \(U\ne0\); no assumption about a profile anchor or a moment rank is made. With \(F_j=I((X-r)X^j F), E_j=I((X-r)X^j E)\) through \(j=2\), put \(B_{ij}=F_iE_j-F_jE_i\). They all vanish by the paid moments. The actual sixth equation is \(T=0\), obtained from the companion's equation (1) by multiplying by \(\gamma^4U\) and substituting \(\eta U=V\). The exact replay constructs this polynomial before any evaluation. In the variable order \(r,s,\gamma\), each \(B_{ij}\) has degree tuple \((2,5,10)\) and \(T\) has \((4,5,12)\).

Let \(S(s,\gamma)\) be the determinant whose rows are the three coefficient lists of \(B_{ij}\) in \(r\), each of length three. Whenever they share an actual \(r\), their coefficient matrix kills \((1,r,r^2)^{\mathsf T}\), so \(S=0\) even when a degree or rank drops. Also \(A(s,\gamma)=\operatorname{Res}_r(B_{01},T)=0\). The replay computes both exact \(S,A\), with \((s,\gamma)\) degrees \((15,30),(30,64)\). The common gcd of all \(s\)-coefficients of \(S\) in \(\mathbb Q[\gamma]\) is one. Consequently \(S\) is not identically zero in a characteristic-zero fiber at **any** \(\gamma\).

To see that \(\operatorname{Res}_s(S,A)\) is a nonzero polynomial in \(\gamma\), specialize its input coefficients at \(\gamma=1\) and then modulo 1009. Both \(s\)-degrees remain full and the gcd is one; thus the specialization of the exact Sylvester determinant is nonzero. This certifies that the exact projection is finite, not that any hidden tableau reduces at this prime. In particular there are finitely many \(\gamma\), and at most fifteen \(s\) over each, without asserting that the outer diagonal is monic at any prime.

For fixed \(\gamma,s\), the actual moment vector \((I(H),I(XH),I(X^2H))=\beta(1,r,r^2)\) has \(\beta=b_rH(r)\ne0\). It lies in the span of the two corresponding moment vectors of \(F,E\). There always exists a nonzero linear functional on three coordinates killing those two vectors. Applied to \((1,r,r^2)\) it yields a **nonzero polynomial of degree at most two in \(r\)**. This handles possible simultaneous vanishing of all \(r\)-coefficients of the determinantal equations, and completes the finite scalar localization. Possible trailing and moment recovery ranks are not classified here.

Run `python3 check_regular_finite.py` with `python-flint==0.9.0`. No neighboring executable is required. This is a source proof plus exact scalar computation, not a native Lean claim or a change to the unrestricted **10–11** bound.
