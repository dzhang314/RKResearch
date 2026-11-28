# Open A2 corner of the two-singleton front versus rear D,S,S arithmetic

This is a rank-safe **ingress, not an exclusion**. It applies to strict ten-stage SDIRK of ordinary order at least eight over a characteristic-zero field, with all physical quadratic defects nonzero, exactly seven clocks, and precisely one singleton physical endpoint. The actual front from that singleton has order of types S,D,S and a genuine arithmetic third row (front A2). Its front D label \(d\) is distinct from the terminal D label \(H\), and the true rear opening is D,S,S arithmetic. The [terminal-reused](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-reuse/README.md), [terminal-new front-star](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md) and [terminal-new front-A3](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a3-front/README.md) cases are independently excluded. The present A2 corner remains open apart from two [exact special exclusions](SPECIAL.md): front half-amplitude and the equal-defect rear arithmetic gap. This does not change the 10–11 stage interval.

## Genuine front and rear phase data

Diagonal-one coordinates are \(y=x-1,\ m=1/(2\gamma),\ H=2(m-1),\ t=y-H/2\). The two endpoint labels are \(0,H\), with \(H\ne0\). The actual forward labels are \(0,d,s=2d\) with original residuals \(1/2,\kappa(d)/2,N(d)/(2D(d))\). Here \(\kappa(z)=1+2z-z^2\), \(D(z)=-2+z+4z^2-z^3\), and \(N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\). The first-departure at a singleton first clock forbids \(d=2\); the actual taps also give \(d,\kappa(d),D(d),N(d),3d-2\ne0\).

The actual reverse later singleton labels in original coordinates are \(p=H-v,\ q=H-2v\) with a true nonzero-third-tap arithmetic gap \(v\). Put \(\widehat q=D(v)-v(v-2)(3v-2)\). The two reverse normalized defects are \(\kappa(v)/2,\ \kappa(v)\widehat q/(2D(v))\). Their literal guards are used, and rear \(v=2\) is not excluded simply by the value of the gap. All four physical singleton labels \(0,s,p,q\) are distinct. The front and terminal D labels \(d,H\) are distinct, and the [single-end parity and Legendre guard](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids centered/antipodal D labels, with \(L_4\) nonzero at each D. These conditions use no field ordering.

## Rank-safe reconstruction and exact ingress

The full [measured affine-factor derivation](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md#the-paid-affine-factor-recovers-the-quadratic-graph) applies directly to the actual A2 defect data. Let \(\mathcal Q=L_3-F_*L_4\) with \(F_*\) affine of nonzero slope fixed at the true D anchors \(H,d\). Divide exactly \(M_3=\mathcal Q/[(y-H)(y-d)]\). In an actual method \(M_3=L R\) with affine \(L=l_0+l_1y\) and genuinely quadratic singleton graph \(R\). At the two measured front S roots,
\[
 l_0=2M_3(0),\quad l_1=(M_3(s)/f_s-l_0)/s,\quad
 R=\tfrac12+a y+b y(y-s),\quad a=(f_s-\tfrac12)/s,\quad b=[y^3]M_3/l_1.
\]
The affine factor has nonzero slope as a true factor with its third D root, so the third label \(e=-l_0/l_1\) and curvature \(b\ne0\) are recovered without dropping a rank-zero **defect-level** or half-amplitude case. In particular the A2 case \(f_s=1/2\) is retained; no formula divides by \(a\) or \(2f_s-1\). The remaining coefficient equation is
\[
                     E=[y^2]M_3\,l_1-l_1^2 a-[y^3]M_3(l_0-l_1s)=0.
\]
No \(R\)-value at a double is inverted; repeated or nonsplit graph roots are not pruned.

As in the [companion actual pair equations](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-star-front/README.md#scalar-rear-ratio-nodal-determinant-and-actual-pair-fits), use \(\mathcal R=0\) for the true cubic reverse graph ratio after cancelling \(v\), \(\mathcal N=0\) for the determinant of the two remainders of \(L_4\) and the actual four-singleton product modulo \(R/b\), and \(\mathcal X,\mathcal Y=0\) for the paid rear \(q\)-singleton and terminal D fits after the three observed S values \(0,s,p\) fix the quadratic. The source regenerates these separate physical equations for A2, including off-graph front D and nonzero reverse-scale guards. It audits all denominator products against the true base clock and phase guards, Legendre units, and measured affine-factor slope. It does not divide by any projected coefficient, quartic remainder component, or possible singular fit rank.

The guarded integer row degree triples in the nominal coordinates \(H,d,v\) are:
\[
 (18,18,0),\ (10,11,3),\ (22,26,2),\ (16,17,8),\ (26,27,8),
\]
in order \(E,\mathcal R,\mathcal N,\mathcal X,\mathcal Y\). The exact nonzero first elimination \(\Pi=\operatorname{Res}_v(\mathcal R,\mathcal N)\), after removing only proved nonzero \(H,d\)-guard factors, has degree pair \((84,100)\). Thus any physical A2 corner satisfies both \(E(H,d)=0\) and \(\Pi(H,d)=0\), followed by all four true \(v\)-rows, not a generic resultant assumption with a discarded leading-coefficient branch. A full final anchor elimination and geometric fibre exclusions are not claimed here. In particular failure of a finite search, or a potential residue guard zero in a future place, is not evidence of nonexistence by itself.

## Replay

Run `SYMPY_GROUND_TYPES=flint python ingress.py` with SymPy 1.14 and python-flint 0.8. The [Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDssArithmeticNewA2Ingress.lean) covers the literal half-amplitude identity and the paid affine-factor coefficient. Neither this Lean module nor the exact ingress replay establishes the A2 exclusion.
