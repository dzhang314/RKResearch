# Constructive information loss in the univariate hierarchy

The previous note distinguishes two marginals and the actual
middle-stage data. This construction shows that losing the
middle data is substantial even for real/rational tableaux
with a single affine lattice and actual directed composability.

## Exact realization lemma

Fix a nonzero rational diagonal \(\gamma\) with \(0<\gamma<1\)
and any finite set of target signed rational measures
\(\eta_h\) for \(h=1,\ldots,L\), with finite positive rational
gap supports contained in \((0,1-\gamma)\). One can realize
all \(\mu_h=\eta_h\) simultaneously as the actual H powers of
a rational lower-triangular tableau with common diagonal
\(\gamma\), common affine-lattice clocks, and **equal jumps along
every composable two-edge path using nonzero entries of \(H\)**.

A lane of length h has stages \(0,1,\ldots,h\) within that lane.
Put \(\gamma\) on every diagonal, and at row j≥1 put its
sole strict entry \(j\tau\) in column \(j-1\), with
\(\tau>0\) rational. The actual row sums and H entries are
\[
 c_j=\gamma+j\tau,\qquad H_{j,j-1}=j\tau^2,
\]
and all other H entries are zero. Give the lane only its
terminal output weight b. Its actual \(\ell\)-step reduced
measure has, for \(1\le\ell\le h\), one atom at gap
\(\ell\tau\) of mass
\[
 b\ \frac{h!}{(h-\ell)!}\tau^{2\ell};
\]
it has no longer walks. To add mass \(\rho\) at gap \(\Delta\)
to the h-step measure, take \(\tau=\Delta/h\) and
\(b=\rho/(h!\tau^{2h})\). It alters only the h-step and the
shorter measures. In particular actual signs or cancellations
in prescribed net data pose no problem.

Proceed descending from h=L down to 1. At each step use
one disjoint lane per nonzero residual atom of \(\eta_h-\mu_h\)
as presently realized. All already matched higher measures
remain unchanged. Residual atoms stay positive rational
in location, since shorter suffix gaps are \(\ell/h\) times
a target location. The ensemble remains finite and all
clocks are \(\gamma\) plus multiples of a common small rational
lattice unit, using a common denominator for the finitely
many strides. The matrix is block diagonal by disjoint lanes,
hence lower triangular in line-by-line chronology and also
after ordering the actual stages by clock with arbitrary
tie-breaking. If desired, start with any finite collection
of longer same-stride lanes with live terminal weights
and clocks in the same range, then fit residuals as before.
Thus arbitrary ordinary dependency depth or width can be
present without changing the prescribed hierarchy. An additional
isolated \(\gamma\)-stage sets \(\sum b_i=1\), if desired,
without changing any \(\mu_h\) for h≥1.

## Consequence for paid gap moments, not a tableau witness

For any nominal \(p\ge7\), take \(L=\lfloor(p-1)/2\rfloor\).
Choose each \(\eta_h\) independently to satisfy
\[
   \int \delta^q\,d\eta_h
     =\frac{1}{(2h-1)!(2h+q)(2h+q+1)}
     \quad(0\le q\le p-2h-1).
\]
This can be done over the rationals: pick \(p-2h\) distinct
rational nodes in \((0,1-\gamma)\) and solve the square
Vandermonde system. The signed weights are allowed. The
realization lemma supplies genuine SDIRK matrices with the
same diagonal and **all** these projected gap identities,
not just those for H and H². Yet every actual two-edge \(H\)-path has equal successive gaps, so the mixed
\((a-e)^2\) observable is zero rather than the paid \(1/1260\).
The resulting tableau is not an order-p witness. It shows
the missing joint data do not follow from the entire finite
univariate hierarchy, the shared lattice, or composability
alone.

If a common diagonal is not requested, one can additionally
fit **all clock-only bushy conditions** through nominal order
p, without changing any H^h measure. Add isolated diagonal
stages at p distinct rational clocks, each with its diagonal
equal to its clock, and solve the Vandermonde system for the
residual \(\mathbf b\cdot\mathbf c^{\odot k}\) moments. They contribute no H edges.
The enlarged finite rational clock set still lies in one
affine lattice. This optional addition uses varying diagonals;
do not claim that it gives the same common-diagonal class.

The distinction from the profile theorem is intentional:
these lanes need not have a common inbound profile on live
predecessors, so they do not contradict the convolution
obstruction. They retain genuine shared-stage paths while
showing exactly what their collapsed total-gap projections
forget. No source, compiler, runner, repository, or held
material was used.
