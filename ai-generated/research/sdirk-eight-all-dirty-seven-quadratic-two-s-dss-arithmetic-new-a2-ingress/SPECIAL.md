# Two exact exclusions inside the terminal-new A2 ingress

Keep the full characteristic-zero hypotheses and actual A2/D,S,S phases of the [main ingress](README.md). The corner is still open in general, but neither \(f_s=1/2\) nor equality of the two paid rear singleton defects is possible. This does not prune a failed pivot, discard an arithmetically legitimate gap, or change the overall stage interval.

## Front half-amplitude

The actual A2 front labels are \(0,d,s=2d\), and \(f_s=N(d)/(2D(d))\). If \(f_s=1/2\), then
\[
        N(d)-D(d)=4d(d-2)(d^3-3d^2+1)=0 .
\]
Here \(D(d)\ne0\), \(d\ne0\), and \(d\ne2\) by the true singleton first-departure guard. Thus \(d^3-3d^2+1=0\), irreducible over \(\mathbb Q\) by the rational root test. Specialize the guarded integer ingress \(E(H,d),\Pi(H,d)\) over this exact abstract cubic field. Their degrees in \(H\) become 15 and 65, and their raw gcd is a unit. Both guarded rows are genuine necessary equations even in this branch by the measured affine-factor recovery in the ingress, which never divides by \(f_s-1/2\). This is an exact field contradiction for every possible embedding or extension, not a residue-place guess.

## Equal rear amplitudes and genuine arithmetic \(v=2\)

The actual reverse S defects differ by a fixed scale times \(N(v)/D(v)-\kappa(v)\), whose numerator is
\[
           N(v)-\kappa(v)D(v)=-v\kappa(v)(v-2)(3v-2).
\]
All factors except \(v-2\) are true nonzero guards of the genuine rear arithmetic phase. Therefore equality is equivalent to \(v=2\). This is **an allowed arithmetic phase before the present exclusion**, not treated as a star or eliminated simply by a reverse gap guard. The rear original clocks are \(p=H-2,\ q=H-4\), distinct. Because their values on the genuine quadratic \(R\) agree, its axis is \(c=H-3\), not the reverse-star axis \(H-1\).

Write \(W=R/[y^2]R=y^2-2cy+W_0\) monic; normalization gives \(R=W/(2W_0)\), \(W_0\ne0\). The single-end parity lemma forbids \(H=6\), when this graph axis would be centered and the graph would yield a centered root or an antipodal pair over the algebraic closure. Front half-amplitude was excluded above, so the true \(R(s)=f_s\) fixes \(W_0=s(s-2c)/(2f_s-1)\). The exact graph does not need to split.

The actual four-singleton quartic is a nonzero scalar multiple of \(y(y-s)((y-c)^2-1)\). The pair factor modulo \(W\) is a known **nonzero** constant, since the observed rear defects are nonzero. Therefore the [gap-free nodal gate](../sdirk-eight-all-dirty-seven-quadratic-two-s-front-dss-star/README.md#the-gap-free-normalized-nodal-necessity) still applies with this new axis: if \(L_4\bmod W=l_0+l_1 y\), then \(s l_1-(2f_s-1)l_0=0\), and \(l_0\ne0\). Fit \(F_*\) from the true distinct D anchors \(H,d\) and form \(M_3=(L_3-F_*L_4)/[(y-H)(y-d)]\). The two coefficients of \(M_3\bmod W\) must vanish. All calculations are polynomial remainders even for a repeated graph root or a graph root shared by a double.

The three pairwise resultants of these guarded rows have degrees 82, 80, 84 in \(H\); their guarded gcd has precisely the two simple factors \(H-5\) and \(H^3-12H^2+45H-53\). In each exact field, the simultaneous \(d\)-gcd is linear. The first gives \(d=2\), prohibited by first-departure. The cubic gives \(d=H-3\) and \(d^3-3d^2+1=0\), the already excluded half-amplitude branch. There is no remaining specialized degree or unknown nodal rank used as a pivot.

The remaining A2 question is therefore the genuine terminal-new corner with \(f_s\ne1/2\) and \(v\ne2\). These exclusions use no assumptions about real coefficients or signed weight order.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_special.py`. This regenerates the A2 ingress once, performs the exact cubic-field half-amplitude check, and reconstructs both \(v=2\) fibres through the literal axis. The scalar Lean companion supplies both denominator-free amplitude identities and the paid graph coefficient relation. No end-to-end native tableau exclusion is asserted.
