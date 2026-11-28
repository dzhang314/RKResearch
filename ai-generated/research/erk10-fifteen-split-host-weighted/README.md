# Weighted split-host support and the last ten-label cofactor gates

Apply the [split-host rank packet](../erk10-fifteen-split-host-rank/README.md)
at rational raw width eleven. In particular the actual
size-five host error \(\boldsymbol d\) is silent through
length five, the final physical live endpoint has zero
dirt, and
\(\boldsymbol w\odot\boldsymbol d\in D_4\).
These are new necessary conditions; they do not assert
a general rational fifteen-stage absence.

## Seven genuinely weighted labels, not merely seven dirt colors

For each real assigned clock label \(z\) define
\(m_z=\sum_{i:x_i=z}w_i d_i\), including zero if
there are high zeros. If all \(m_z=0\), the
[dirty-label count](../erk10-fifteen-split-host-rank/COLOUR-SUPPORT.md#count-the-dirty-colors-when-there-are-at-most-six)
works unchanged even without an upper bound on
the number of dirty colors: its counting argument
only needs zero at every pooled weighted dirt mass.
Thus at most four dirty colors would occur.
Consequently the multicolor mode (at least seven
colors) has at least one nonzero \(m_z\). The six
true marked tests at powers \(0,\ldots,5\) and
Vandermonde then force **at least seven distinct
labels with \(m_z\ne0\)**.

Neither a unique endpoint nor a singleton unscored
host can be one of those seven weighted labels.
For example, with only seven distinct nonzero
labels and a unique endpoint, multicolor dirt
requires at least one high zero *and* a repeated
host; all six ordinary pools and the zero pool
have nonzero weighted dirt. With eight nonzero
labels, unique endpoint and no high zero, the
host must repeat and every ordinary pool must
have nonzero weighted dirt. More generally
at least one physical weight is strictly negative
in the multicolor rational case: under nonnegative
weights the exact true square test
\(\boldsymbol w^T\boldsymbol d^{\odot2}=0\)
would instead make every \(m_z\) zero.

## The surviving ten-label geometry: exact cofactor equations

By the [largest-clock census](../erk10-fifteen-split-host-rank/LARGEST-CLOCKS.md),
assume ten distinct nonzero raw clocks, no zeros,
a unique endpoint \(1\), and just one earlier
ordinary pair at forward clock \(c\). This pair
already closes in the first five reverse rows.
The reclassified host \(r\ne0,1,c\) is a singleton,
unscored, and has \(d_r=1\).
The grade-two seed \(\boldsymbol u\) leaks, and
\(D_4=\boldsymbol u\odot{\cal P}_2(\boldsymbol x)\).
Let \(\mathcal T\) be the nine ordinary clocks and
\(F(X)=\prod_{z\in\mathcal T}(X-z)\).
There are polynomials \(A,G,Q\), of degrees at
most \(1,4,2\) respectively and \(A,Q\ne0\), such that
\[
 \begin{split}
 U_z&=\sum_{i:x_i=z}u_i=\frac{A(z)}{zF'(z)},\\
 D_z&=\sum_{i:x_i=z}d_i u_i=\frac{G(z)}{F'(z)},\\
 w_i d_i&=Q(x_i)u_i .
 \end{split}
\]
The first cofactor uses seven positive tests of the
actual grade-two defect. The second uses the four
ordinary moments obtained by pairing the true
size-five source \(\boldsymbol d\) with
\(C^j\boldsymbol u\) for \(0\le j\le3\)
(grades at most five). Both vectors are zero
at the unique endpoint, which is omitted from
\(\mathcal T\). The third equality is the actual
nonlinear grade-four receipt. Nonzero \(Q\) follows
from the multicolor weighted count. At a singleton
ordinary site, including the host, these imply
\[
   A(z)d_z=zG(z),\qquad
   w_z z^2 G(z) F'(z)=Q(z) A(z)^2 .
\]
These forms do not divide by a physical weight,
\(Q(z)\), or \(A(z)\).

At the unscored host \(Q(r)A(r)=0\) and
\(G(r)=A(r)/r\). Also \(Q(0)A(0)=0\):
sum the pointwise equality at grade zero and apply
Lagrange partial fractions to \(Q A/F\) at zero.
Indeed \(\deg(QA)<\deg F\), so
\(\sum_{z\in\mathcal T}Q(z)A(z)/(zF'(z))
=-Q(0)A(0)/F(0)\). The sum is zero by the
literal dirt test.

## The unscored host necessarily has nonzero grade two

Suppose \(A(r)=0\). As \(A\ne0\) and \(\deg A\le1\),
it is affine with sole root \(r\). The equality
\(G(r)=A(r)/r\) implies \(G=A G_3\) with
\(\deg G_3\le3\). At every ordinary singleton
except \(r\) one has \(d_z=zG_3(z)\).
At \(r\) the score is zero, so it cannot
disturb any weighted moment. The polynomial dirt
\(\Delta=X G_3\) also vanishes at the external
opening origin, where the actual dirt is zero.
Thus the only possible weighted exceptions are the
pair \(c\) and endpoint \(1\). For
\(q=(1-X)(X-c)R\), \(\deg R\le3\), the real
dirt moments and scalar precision nine imply
\[
           I\bigl(X(1-X)(X-c)G_3R\bigr)=0 .
\]
If \(G_3=0\), then the actual weighted dirt could
be nonzero only at the pair, or at the endpoint
but its dirt there is zero. Six exact moments
would kill all weighted dirt, contrary to the
weighted count. Otherwise \((X-c)G_3\) is a nonzero
degree-at-most-four polynomial orthogonal to cubics
under \(X(1-X)\). The
[modulo-eleven Jacobi certificate](../erk10-fifteen-tilt-fullmark-closure/DENSE-JACOBI.md#three-allowed-exceptional-site-sets-all-impossible)
implies that the resulting Jacobi quartic cannot
have the rational root \(c\). This is a contradiction.

In particular \(A(r)\ne0\), \(u_r\ne0\), and \(Q(r)=0\).
The same argument excludes \(A\mid G\) when \(A\)
is affine with its root anywhere *except* a live
ordinary singleton. For a live singleton at that
root \(a\), a necessary condition is
\((G/A)(a)\ne0\); otherwise the weighted
exception there disappears since \(u_a=0\) and
\(w_a d_a=0\).

## Constant cofactor and cardinal guards

If \(A\) is constant then \(d_z=zG(z)/A\) at
all ordinary singletons. If \(\deg G\le3\), the
preceding degree-nine Jacobi argument again
applies. If \(G(1)=0\), write \(G=(1-X)G_3\),
\(\deg G_3\le3\), and instead choose
\(q=(X-c)R\), \(\deg R\le3\). There is no endpoint
exception (actual and polynomial dirt zero), so
the same Jacobi contradiction results. Thus a
constant \(A\) survivor needs \(\deg G=4\) and
\(G(1)\ne0\).

If \(A(0)\ne0\), the two earlier roots give
\(Q(X)=\lambda X(X-r)\), \(\lambda\ne0\).
Let \(\mathscr P=X(X-1)F/(X-r)\), of degree ten,
whose nodes are all scalar sites except the
zero-score host. Put
\(\mu_z=I(\mathscr P(X)/(X-z))\).
The degree-nine cardinal rule gives
\(w_z=\mu_z/\mathscr P'(z)\) at every ordinary
singleton \(z\ne r,c\), including any with
zero weight. From the exact singleton identity,
\[
                       \mu_z G(z)=\lambda(z-1)A(z)^2
                                  \quad(z\ne r,c).
\]
This follows by cancelling only the distinct nonzero
factors \(z,z-r,z-1\), not the cardinal mass.
It is a further exact finite relation for the
remaining unclosed late geometry.
