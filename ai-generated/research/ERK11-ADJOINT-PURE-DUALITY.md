# Exact adjoint-pure duality on the maximal Jacobi tail

This supplements the [two-generator normal form](ERK11-TWO-GENERATOR-ENDPOINT-TAIL.md)
and the [all-live reduction](ERK11-ALL-LIVE-ENDPOINT-REDUCTION.md).
Keep their maximal rank-two endpoint hypotheses, using scaled
operators \(D=A/y,\ Z=Y/y\) and normalized physical labels
\((t,1,1,p,q,0)\) at 12–17. This is a field argument after the
paid rooted bridges; it does not alter the 17–18 interval.

## A support dichotomy not requiring all eleven early weights live

The actual seed \(h_2=2bD^2-bZ^2\) annihilates \(E_8\).
It is nonzero: \(q\ne0,\ b_{16}\ne0\) by the live last
edge and \(bA=bY\), and \(bD^2\) ends at 15, so
\((h_2)_{16}=-b_{16}q^2\ne0\).
The actual \(E_8\) rank is 16 in the maximal Jacobi branch,
using its five late pivots and full first eleven.
Also \(b\operatorname{diag}(\delta)\) annihilates \(E_8\)
by pure multiplication of degree \(2+8=10\).
Thus either all quadratic carriers have zero ordinary weight,
or the following **full row identity** holds:
\[
           h_2=-\frac{q^2}{\delta_{16}}b\operatorname{diag}(\delta).
\]
In the second case \(\delta_{16}\ne0\), since the proportional
nonzero rows have the same support at physical 16.
The formula is not restricted to the half-clock branch and
does not divide by a possibly zero early coefficient.
In particular the no-weight branch or the displayed equality
exhausts all maximal rank-two possibilities for this seed.

## A finite double-ended primitive on the pure flags

Under the all-early-live hypothesis all seventeen weights are
live. Write \(B=\operatorname{diag}(b)\), and let
\(D^*=B^{-1}D^\mathsf{T}B\), using ordinary field algebra.
For each pure \(f\in F_j\), \(f^\mathsf{T}B\) annihilates
\(E_{10-j}\) by a paid product. At grades 2,3,4 these
are equalities of whole spaces by the exact ranks:
\[
     \operatorname{Ann}(E_8)=F_2^\mathsf{T}B,\qquad
     \operatorname{Ann}(E_7)=F_3^\mathsf{T}B,\qquad
     \operatorname{Ann}(E_6)=F_4^\mathsf{T}B .
\]
In particular \(D^*\delta\in F_3,\ (D^*)^2\delta\in F_4\).
Their last physical indices are exactly 15 and 14,
respectively: the row reads \(h_2 D,h_2 D^2\) have those
last positions by the live adjacent path, and \(B\) is
diagonal invertible. Similar reasoning sends \(D^*(Z\delta)\)
into \(F_4\) by the available rooted budget.

If \(p\ne1/2\), the true pure flags are
\(F_3=\delta K[Z]_{\le1}, F_4=\delta K[Z]_{\le2}\).
All four tail carrier clocks \(t,1,p,q\) are distinct
and their \(\delta\) values nonzero.
Support at 15 and 14 therefore gives exact nonzero scalar
multiples (not just model profile relations)
\[
              D^*\delta\ \propto\ (Z-q)\delta,\qquad
       (D^*)^2\delta\ \propto\ (Z-q)(Z-p)\delta .
\]
At the front, if \(z_0,z_1\) are the first two physically
encountered distinct carrier labels, \(D\delta\) is a
(possibly zero) scalar multiple of \((Z-z_0)\delta\)
by strictness at the earliest carrier. Before the first
carrier with label \(z_1\), all entries of \(D\delta\)
vanish, both on noncarriers and on the first label.
Thus \(D^2\delta\) is a (possibly zero) multiple of
\((Z-z_0)(Z-z_1)\delta\).
This is an exact two-ended causal polynomial restriction.
In particular both \(D,D^*\) send \(\delta\) and \(Z\delta\)
to carrier-supported vectors through these grades; at every
noncarrier the corresponding two incoming and outgoing
weighted carrier-feed sums vanish.

If \(p=1/2\) and 16 is the sole late carrier, put \(f=A\delta\).
The previous note proves \(f=0\) at every carrier and
\(f_{12}f_{14}f_{15}\ne0\), with \(F_3=\langle\delta,f\rangle\)
and \(F_4=\langle\delta,f,Zf\rangle\).
The last-support restrictions now give instead
\[
              D^*\delta\ \propto\ f,\qquad
       (D^*)^2\delta\ \propto\ (Z-p)f ,
\]
again with both scalar multiples nonzero.
In particular the localized second seed has a derivative
proportional to the actual weighted \(A\delta\) profile,
which is supported completely off the quadratic carriers.
These dual identities use only the paid root products, exact
numerical ranks and physical path; they require no extra
scalar arithmetic test and do not assert a tableau surgery.
