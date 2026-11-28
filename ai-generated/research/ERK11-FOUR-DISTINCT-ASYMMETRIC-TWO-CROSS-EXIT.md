# Four distinct calibrations: the asymmetric no-opposite-plateau shape cannot have two crossings

**Scope.** Continue the four-distinct part of the
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md).
Take left extras \(\{e,t\}\) and right extras \(\{t,u\}\), with
free labels \(t,u\), or the reflected configuration. This note
excludes the case where both \(e,t\) are ordinary crossing
pairs. The single-cross case (one of those labels is the
triple) remains open.

## 1. A two-clock **product** support, even with three inner labels

The half \(h\) and the unselected-on-left free label \(u\)
each occur at only one front. The shared labels \(e,t\)
are assumed to be ordinary pairs, so the triple is one of
\(h,u,a,d\). If it is \(h\) or \(u\), the inner physical
rows 8–10 occupy just the two clocks \(h,u\), one repeated.
If it is one of the plateaus \(a,d\), the inner rows occupy
\(h,u\) and that plateau.

However, the actual product of the two grade-four
square-clock vectors vanishes at either plateau. On a
noncarrier the left vector is \(c^2(c-a)^2+a(c-a)F\),
with the factor \(c-a\); the right vector has the analogous
factor \(c-d\). The inner plateau occurrence is a
noncarrier. Thus in every two-cross case the product is
supported on rows 8–10 **at clocks \(h,u\) only**. Testing
with \((C-hI)(C-uI)\) is paid at grade \(4+4+2=10\),
by the same mixed forward/transpose calculation as the
[opposite-plateau proof](ERK11-FOUR-DISTINCT-OPPOSITE-PLATEAU-TWO-CROSS-EXIT.md).
Writing
\[
 I_j=\int_0^1 X^j\,X^2(X-a)^2(1-X)^2(X-d)^2\,dX ,
\]
it gives \(I_2-hI_1+u(hI_0-I_1)=0\). This is a
vanishing actual tree-product pairing, without any
centroid division or numerical approximation.

## 2. Projection and fibers

Keep the four-distinct Hankel data \(D=0,\ \Delta\ne0\),
Cramer numerators \(A,B\), and monic scaled free quadratic
\(Y^2+AY+\Delta B\). As in the
[selected-free half-triple proof](ERK11-FOUR-DISTINCT-SELECTED-FREE-HALF-TRIPLE-EXIT.md),
the support polynomial \(E\) is the product over \(g=h,e\)
of the norms of
\[
 \Delta(I_2-gI_1)+Y(gI_0-I_1).
\]
This product includes the reflected geometry; only
proved-live \(\Delta\) powers and nonzero scalar content
are stripped. No factor depending on an actual free-root
amplitude is divided out.

The first-contact factors multiplied by \(\Delta\) are,
for \(Y=\Delta t\),
\[
 L_0=(a-e)(\Delta a-Y),\quad L_1=-eY,\qquad
 R_0=d^2\Delta+dA+B,\quad R_1=-\Delta-A-B.
\]
The latter two use both free roots on the right rather
than a choice of just one. Take the free quadratic norm
of the usual paid row-7/row-11 inverse Gram polynomial
in these four factors, then multiply by the reflected
norm for symmetry. Strip only \(\Delta\) powers and
scalar content, to get \(C=0\). This calculation is
through the actual forward and weighted-transpose
grade-five anchored rows, with the established both-new
prefactors; no reverse order-eleven premise is used.

Writing the symmetric equations in \(S=a+b,T=ab\),
the two \(T\)-resultants with \(D\) have degrees 252
(first contact) and 108 (support) in \(S\).
Their gcd has degree-4 and degree-10 factors with
multiplicities one and two. At each coefficient fiber
the standalone replay computes a monic linear condition
at the actual same common \(T\) dividing \(\Delta^2\),
using the support and contact together with \(D\).
Thus \(\Delta=0\) at any common solution, contradicting
the independently proved-live pivot. Both projection
factors are explicitly audited; neither is discarded
just for appearing in a guard resultant.

The [standalone Python replay](erk11-four-distinct-asymmetric-two-cross-exit/replay_four_asym_two_cross.py) supplies
the exact polynomial and residue computations. No
separate Lean replay of this elimination or ordinary
stage-bound improvement is claimed.
