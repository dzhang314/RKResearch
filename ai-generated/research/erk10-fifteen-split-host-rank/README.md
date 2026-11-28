# The split evaluation host forces three residual directions

**Theorem.** In the
[rational split single-evaluation tilt](../erk10-five-opening-rank-one-size-five/SPLIT-EVALUATION.md)
at original width fifteen, the reclassified pure high
width-eleven block has exactly three independent dual
annihilators of its fourth defect space and five nominal
columns. In particular its fourth defect space has rank
three and its exact raw first reverse primitive vanishes:
the **last live physical high clock is \(1\)**. This
applies to either old host \(r=p\) or \(r=q\), with free
or fixed old contact as applicable. It is a restriction
on the remaining rational width-fifteen chart, not yet
an exclusion or a general lower bound.

We prove the following raw formulation, which makes
the exact inherited data explicit.

* \(B\) is a strictly lower high block of width at
  most eleven, with assigned clock vector
  \(\boldsymbol x\), high scores \(\boldsymbol w\),
  and scalar order-nine quadrature (plus the old
  origin score). The pure words through length five
  on \(X,\ldots,X^{9-|W|}\) have their exact nominal
  values.
* The first high physical row is a nonzero clock
  \(r\), and a vector \(\boldsymbol d\) with first
  entry \(1\) satisfies
  \(\boldsymbol w^T W\boldsymbol d=0\) for every
  pure word \(W\) of length at most five.
  The host is unscored in the actual chart; this
  rank proof itself does not need its score zero.

In the actual split reclassification these facts
hold because a zero-model old host axis, achieved
by the true size-five old pure span, has new high
response
\(\boldsymbol d=\boldsymbol e_r-\kappa\boldsymbol\delta\).
For host \(p\), the later reclassified old axis
\(q\) is silent by the old erasure proof and is
deleted from the raw block. The host vector has
zero at the erased index already, so the same
right-to-left projection (for words through five)
preserves its silence. The leading host row is
still strict and first after this operation.
This does not treat the p-host old \(q\) tap as zero
in the actual tableau.

## The dimension bound and actual annihilators

Let \(V\) be the annihilator of the combined
\(D_4\) and nominal weighted powers through degree
four. Shifted Hilbert \(5\) and the
[grade-four floor](../erk10-five-opening-rank-one-size-five/README.md#weak-plateau-assumptions-and-the-rank-debit)
give \(\dim V\le3\) at this width. The true forward
residuals
\[
                   T(f)=BE f-EJf,\qquad f\in X\mathcal P_3
\]
belong to \(V\) by the pure length-five budget.
They have rank at least two by the first two
distinct nonzero forward rows, as in the paid
plateau proof. Also
\(\boldsymbol d,C\boldsymbol d,B\boldsymbol d\in V\):
prepend a single mark or primitive to the
actual silent source, preserving all tests of
length at most four on that source. Thus
\(2\le\dim V\le3\).
It suffices to exclude dimension two. Below \(E_x\)
and \(J_x\) are linear functionals on \(X\mathcal P_3\)
given by evaluation of \(f\) and \(Jf\) at \(x\).

## Dimension two cannot contain a single-color host vector

Suppose \(\boldsymbol d\) is supported only at \(r\).
Erase its first pivot by
\(Q=I-\boldsymbol d\boldsymbol e_r^T\).
It commutes with \(C\), and its image is the first-zero
slice, with \(QB=B\) because the first strict row
of \(B\) is zero. The projected system has a strict
principal block and can be normalized to flagged
eval \(E_\varepsilon\) as in the
[directional cut](../erk10-fifteen-tilt-fullmark-closure/README.md#a-same-label-directional-erasure).
The only possible flag-zero copies are at the host
label. The projected scalar moments are unchanged:
the host direction is already silent at length
zero. Hence at least five distinct flagged nonzero
clock labels carry nonzero scalar scores, by the
shifted Hilbert factorization.

In this new system the true forward residual map,
before nonzero diagonal normalizations, is
\[
 QBQE f-QEJf = Q\bigl(T(f)-B\boldsymbol d\,f(r)\bigr)
                            \in QV .
\]
If \(\dim V=2\), then \(\dim QV=1\).
But the first two distinct flagged nonzero
chronological labels have the familiar independent
forward residual rows: all earlier unflagged calls
supply zero, flagged zero-clock calls also supply
zero on positive models, and before the second
distinct flagged label the only scalar donor is
the first distinct flagged clock.
The second-difference proof uses the four models
in \(X\mathcal P_3\) and continues to apply
unchanged. This is a contradiction. It did not
divide by a zero normalization or assume a
flag-zero row has zero score.

## Dimension two cannot contain a multicolor host vector

If two or more clock labels occur in the support
of \(\boldsymbol d\) and \(\dim V=2\), then
\(V=\langle\boldsymbol d,C\boldsymbol d\rangle\).
Write its physical residuals as
\[
                T(f)_i=d_i R_{x_i}(f)
\]
where \(R_x\) is a single affine pencil of
functionals. The host row forces \(R_r=-J_r\).
Since the first coordinate of \(B\boldsymbol d\)
is zero, its membership in the same two-plane gives
\(B\boldsymbol d=\theta(C-rI)\boldsymbol d\).
Replace \(B\) for this **necessary row calculation**
by
\[
        B_* = B-\theta(C-rI)\boldsymbol d\boldsymbol e_r^T .
\]
It is still strict; it has \(B_*\boldsymbol d=0\);
and the residual pencil retains the same form,
with \(R_x\) shifted by a multiple of \((x-r)E_r\).
We do not need any new rooted order assertion
for this gauge. Normalize the nonzero \(r\) to
one using \(x/r\) and \(B_*/r\) and keep the names
for the resulting coordinates. Write \(t,z,k\)
for the second, third, fourth distinct nonzero
forward clocks. All exist by the shifted Hilbert
support. Zero clocks are permitted anywhere.

### Through the second nonzero debut

Before \(t\) every nonzero-clock predecessor is
at \(1\) and its input is \(E_1\).
A repeat \(1\) has
\(B_* E f=(1-d_i)J_1 f\), so \(d_i=1\)
because \(E_1,J_1\) are independent.
If a zero-clock predecessor were dirty, its
residual would give \(R_0\in\langle E_1\rangle\).
Then \(R_t\in\langle E_1,J_1\rangle\) by affine
interpolation, and the \(t\)-read would give
\(J_t\) in that same span. This is impossible by
the literal probe \(f=X(X-1)(X-1/2)\):
\(E_1 f=J_1 f=0\), \(J_t f=t^2(t-1)^2/4\ne0\).
So all those zero rows have dirt zero. At the
first \(t\), \(B_*\boldsymbol d=0\) makes the
total earlier \(1\)-tap zero, hence \(d_t\ne0\)
and \(R_t=-J_t/d_t\). The entire pencil is now
\[
         R_x=-\frac{(t-x)J_1+(x-1)J_t/d_t}{t-1}.
\]

### Same-label copies through the third nonzero debut

With only \(1,t\) as earlier nonzero clocks,
\((J_1,J_t,E_1,E_t)\) are independent: their
determinant on \(X,\ldots,X^4\) is
\(-t^4(t-1)^4/120\).
Consequently every repeated \(1\) or \(t\) has
the original dirt value, and every intervening
zero row is clean since \(R_0\) is not in the
evaluation span. This uses the *actual* row
equations, not an assumption of equal dirt
on repeats.

At \(z\), the constraint \(B_*\boldsymbol d=0\)
puts its old read in the single line
\(F=E_t-d_t E_1\).
Write \(J_z=A J_1+D_1 J_t+U E_1+V_1 E_t\).
The literal row and pencil give
\[
 A=d_z(t-z)/(t-1),\quad
 D_1=d_z(z-1)/((t-1)d_t),\quad
 U+d_t V_1=0 .
\]
In particular \(A(z-1)V_1+D_1(t-z)U=0\),
without dividing by a predicted nonzero \(d_z\).
The exact determinant replay factors the left
side (up to guarded nonzero factors) as
\(t(t+1)+(t^2-4t+1)z\).
Thus with \(D=t^2-4t+1\) one obtains
\[
 z=-\frac{t(t+1)}D,\qquad
 d_t=-\frac{t^3(t-2)}{2t-1},\qquad
 d_z=\frac{t^3(t-2)(t+1)^2(5t^2-14t+5)}{D^4}.
\]
Here \(D\) is projectively rootless modulo seven;
\(t=-1\) would give \(z=0\), \(t=2\) gives \(z=t\),
and \(t=1/2\) gives \(z=1\). These guards, plus the
no-rational-root quadratic in \(d_z\), make its
ordinary Cramer divisions valid. In particular
the \(z\) row could not be clean.

### No fourth nonzero label

Before the fourth distinct label all nonzero
inputs are supported on \(1,t,z\).
The probe \(H=X(X-1)(X-t)(X-z)\) kills that
eval span. The exact \(J_1H,J_tH,J_zH,R_0H\)
are nonzero on the displayed branch (see replay).
The nontrivial guard factors
\[
 \begin{gathered}
 5t^3-6t^2+4t-1,\quad t^3-4t^2+6t-5,\quad
 t^2-3t+1,\\
 5t^2-14t+5,\qquad 3t^2-7t+3
 \end{gathered}
\]
are all projectively rootless modulo seven.
In particular \(R_a(H)\ne0\) at each preceding
\(a=1,t,z\), and \(R_0(H)\ne0\).
Subtract the established first physical row
of a given label from a later proposed same-label
row (both earlier-than-fourth). Its read still
lies in the three-label eval span, so applying
\(H\) shows the dirt value cannot change.
At each intervening zero, the \(H\)-read makes its
dirt zero. These arguments carry through
arbitrarily interleaved repeats.

Thus at the fourth distinct nonzero \(k\), its
old read under \(B_*\boldsymbol d=0\) must lie
in the span of
\(F=E_t-d_t E_1\) and \(G=E_z-d_z E_1\).
Its row implies
\(\det[F;G;J_k;R_k]=0\).
The independent symbolic replay gives exactly
\[
 \det[F;G;J_k;R_k]
 =\frac{k^2 t^3(t-k)(k-1)(t-1)^3(t+1)(k-z)^2}
        {10 D^2},
\]
which is nonzero. This is the required contradiction.
Thus all rank-two possibilities fail.

## Consequences and remaining work

The rank is therefore exactly three, forcing
\(\dim D_4=3\). Apply the existing
[paid endpoint plateau](../erk10-five-opening-plateau-endpoint/README.md)
to obtain \(K\boldsymbol w=Y\boldsymbol w\) and last live
clock \(1\). Applied in the actual chart, physical last
unscored **original high** rows can be trimmed before
reclassification; since the rational width-14 chart is
already excluded, the last original physical row must
itself be live and have clock \(1\). The reclassified
host remains unscored and first in forward order.

There are extra usable size-four inputs as well.
Let \(k_o\) be the other old label among \(p,q\)
and \(\alpha_o=P(k_o)/P(s)\). In
\(X\mathcal P_2\) the two-dimensional model space
\[
                     U_0=\ker(E_{k_o}-\alpha_o E_s)
\]
comes from true order-at-most-four combinations
that have old profile zero except possibly at
the raw host (where it is the nominal value).
For the \(p\)-host, the defining equality precisely
makes the extra erased \(q\)-axis zero on the input;
any occurrence of that axis after at least one
letter in a length-six word is suppressed by its
previous length-five silence. Thus in both hosts
these pure inputs are paid through length six.
Their actual first primitive has the one possible
high error \(\boldsymbol d\), with coefficient
\(-J_r f\) fixed by the first high row. In particular
\[
                  T(f)=-J_r(f)\boldsymbol d
                       \quad (f\in U_0).
\]
This usable forward pressure distinguishes the true
host problem from arbitrary pure width eleven, but
the rank-three width-fifteen case is not excluded
in this packet. In fact the first two physical high rows
are now determined in shape, and a rank-two first-three
restriction has an exact root gate; see [literal host gates](HOST-GATES.md).
A separate [support dichotomy](COLOUR-SUPPORT.md) excludes
all dirt with two through six clock colors. Neither result
presupposes nonzero individual high scores. The stronger local
rank ledger transfers the [largest clock cases](LARGEST-CLOCKS.md)
from width ten to width eleven, leaving only an early ordinary
pair when at least ten distinct nonzero high clocks occur.
The actual rooted profiles also give a stronger
[nonlinear consequence](NONLINEAR.md): the elementwise
weighted host error \(\boldsymbol w\odot\boldsymbol d\) is an
actual grade-four reverse defect, and the last live
physical row is clean.

## Replay

    python3 -B audit.py
    sha256sum -c ai-generated/research/erk10-fifteen-split-host-rank/sources.sha256

The symbolic replay verifies each determinant and
guard, not a finite coefficient search. The portable
Lean finite certificate checks the six modular
no-root gates; the word, rank and physical transport
arguments here are mathematical.
