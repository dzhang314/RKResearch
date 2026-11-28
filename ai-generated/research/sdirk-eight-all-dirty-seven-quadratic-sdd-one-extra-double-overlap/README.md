# One singleton endpoint: double-overlap S,D,D versus one later rear double

Assume a strict ten-stage SDIRK method has ordinary order at least eight over a characteristic-zero field, all ten quadratic defects nonzero, exactly seven different clocks, and exactly one singleton physical endpoint. Use the actual orientation from the singleton. Suppose the front opening is S,D,D and the reverse opening has exactly one later D and one S. This packet excludes **double overlap**: both later forward D labels cannot be the two rear D labels. The rear arithmetic and star orders are all covered. Single overlap, a rear D,S,S, and both-singleton endpoints are not addressed here. The overall stage interval is unchanged.

## Paid graph and two Vieta products

In the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) write
\[
 \mathcal Q=L_3-F_*L_4,\qquad R\propto \mathcal Q/P,\qquad
 L_3(t)=t^3-\tfrac35m^2t,\quad L_4(t)=t^4-\tfrac67m^2t^2+\tfrac3{35}m^4.
\]
Here \(m=(H+2)/2=1/(2\gamma)\), \(y=x-1\) in diagonal-one units, and \(t=y-H/2\). The endpoints are \(y=0,H\) with distinct multiplicities, so \(H\ne0\). Write \(L_j(y)\) below for the same Legendre modes evaluated at \(t=y-H/2\). The D labels are \(H,d,e\). The affine \(F_*\) has nonzero slope because the singleton graph \(R\) is genuinely quadratic by the [constant and affine exclusions](../sdirk-eight-all-dirty-seven-affine-final/README.md).

One extra rear D at original \(d\) determines the original rear S clock \(s\) and their normalized reverse defects \(\rho_d,\rho_s\). Set \(z=H-d\), \(\kappa(z)=1+2z-z^2\), \(D(z)=-2+z+4z^2-z^3\), and \(N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\). The actual pairs are:
\[
\begin{array}{c|ccc}
 \text{rear phase} & s & \rho_d & \rho_s\\\hline
 \mathrm{A2} & 2d-H & \kappa(z)/2& N(z)/(2D(z))\\
 \mathrm{A3} & (H+d)/2 & N(z/2)/(2D(z/2))&\kappa(z/2)/2\\
 \mathrm{star} & 2H-2-d &\kappa(z)/2&\kappa(z)/2 .
\end{array}
\]
A2/A3 mean the extra D is second/third in reverse arithmetic. Either reverse star order gives the same two known clock-defect pairs but is not an arbitrary reordering of the method. The reverse terminal normalized defect is \(1/2\); its original value is \(\lambda/2\) for the common true nonzero reverse scale \(\lambda\).

Double overlap means forward later D labels are precisely \(H,d\). A forward arithmetic third after gap \(H\) gives \(d=2H\); the other order would give \(d=H/2\), impossible by the [single-endpoint parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md). A forward star gives \(d=2-H\) in both orders. Let \(f_H,f_d\) be the actual known forward residuals. For arithmetic these are \(\kappa(H)/2,N(H)/(2D(H))\), and for star both equal \(\kappa(H)/2\). The literal nonzero guards for true arithmetic include \(z,\kappa,D,N,3z-2\) at the actual gap, and for star include \(z,z-1,z-2,\kappa(z)\). The singleton-forward first-departure guard also forbids a front gap of two. Both actual overlaps are disjoint physical stages, not a choice of two candidate abstract roots.

The genuine D quadratic is \(L_4(y)-g(A_2(y)+Bg)\) with \(B\ne0\). At \(H,d\), its two roots are the front value and the normalized reverse value multiplied by \(\lambda\). Thus Vieta gives a common nonzero \(\beta=B\lambda=-2L_4(H)/f_H\), and
\[
                     L_4(H) f_d\rho_d -L_4(d) f_H/2=0 .
\]
No \(L_4\) vanishes at a D label because \(L_3,L_4\) are coprime and \(\mathcal Q\) vanishes there. This and the true clock and phase guards justify all cleared factors. The raw and guarded product numerator degrees, respectively, are \(11\to7,\ 14\to10,\ 11\to7\) for forward arithmetic and rear A2/A3/star; and \(8\to4,\ 11\to8,\ 8\to4\) for forward star. Each guarded field polynomial is irreducible over \(\mathbb Q\). The proof keeps all six polynomial fields rather than testing real or rational roots.

## The third D and paid rear singleton

Since \(F_*\) interpolates \(L_3/L_4\) at the distinct labels \(H,d\), it is already known. Put
\[
                  M_3(y)=\mathcal Q(y)/[(y-H)(y-d)] .
\]
This is an exact cubic. If the third D is \(e\), then \(M_3(e)=0\), and no assumption is made whether this root is simple in \(M_3\). In particular \(P\) and \(R\) are allowed to share roots. In the actual branch \(e\ne0,\ s\ne e,\ M_3(0)M_3(s)\ne0\), since both \(0,s\) are singleton and have nonzero graph defects. Normalize \(R(0)=1/2\); then the rear S scale is
\[
       \lambda=\frac{R(s)}{\rho_s}
          =-\frac{e M_3(s)}{2 M_3(0)(s-e)\rho_s}.
\]
Nothing evaluates \(1/R\) or \(1/W\) at a D label. Common or repeated graph roots are not dropped.

Write \(\lambda A_2(y)=T_0(y)+\lambda T_1(y)\). Vieta sums at \(H,d\) and the paid first-S equation give the three actual interpolation rows
\[
\begin{array}{c|cc}
 y&T_0&T_1\\\hline
0&-\beta/2&2L_4(0)\\
H&-\beta f_H&-\beta/2\\
d&-\beta f_d&-\beta\rho_d .
\end{array}
\]
The distinct clocks make the interpolation unique, in the sense that these two specified quadratic fits sum to the unique actual \(\lambda A_2\). At the actual rear singleton,
\[
       L_4(s)=\rho_s T_0(s)+\lambda\bigl(\rho_s T_1(s)+\beta\rho_s^2\bigr).
\]
Set \(F_0=L_4(s)-\rho_s T_0(s)\), \(F_1=\rho_s T_1(s)+\beta\rho_s^2\). Eliminating \(\lambda\) yields the *linear* equation in the unknown third label
\[
                2M_3(0)\rho_s(s-e)F_0+e M_3(s) F_1=0.
\]
This does not divide by an affine rank or its leading coefficient. A singular fit would leave a nontrivial gcd if compatible. In the six exact projected \(H\)-fields, this equation has unit gcd with \(M_3(e)\) before any additional \(e\)-guards. No extension or splitting assumption is needed, and no trace or fourth read is used.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_double_overlap.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticSddOneExtraDoubleOverlap.lean) checks the denominator-free removal of the rear scale, not the rooted-order bridge or exact polynomial gcds. The full exclusion is an exact mathematical proof with numerical-field-free algebra replay, not an end-to-end Lean theorem or finite-characteristic assertion.
