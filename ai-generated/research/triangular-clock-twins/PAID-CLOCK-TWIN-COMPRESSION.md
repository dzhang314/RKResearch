# Finite-jet compression of opposite-weight clock twins

Mathematical proof over a characteristic-zero field. All indices
are actual triangular stages; no positive weight assumption or
common diagonal assumption. The allowed class of strict-row repairs
is specified where used. No unrestricted stage-floor claim.

## 1. What the paid twin gives, and when direct compression is exact

Write \(v_i^h=(\Phi_i(\tau):|\tau|\le h)\) and
\(U_i^h=\sum_k A_{ik}v_k^h\) for the child-response row. Equal
stage jets through size \(h\) always mean all such rooted trees.
Suppose \(i<j\), \(c_i=c_j=c_*\), and \(b_i=-b_j\ne0\), with no
other output-active stage at \(c_*\) when that is indicated.
These opposite weights and equality of the degree-two defect
follow for an isolated two-site fibre if its degree-two defect is
nonzero at either site and both the first and second weighted powers
of that defect vanish on the fibre. With \(r\) distinct active clock
labels, order \(p\ge r+4\) suffices for these localized payments:
the clock selector costs \(r-1\) and the squared defect has stage
degree four. The first moment forces both defects to be nonzero;
subtracting the first moment times one defect from the second
then forces equality and hence opposite weights. More generally if that fibre annihilates all
\(Z_a\), the twins have identical \(v^{a+1}\): subtract the exact
stage polynomial of each tree evaluated at their common clock.
Even when the same cancellation is established by other means,
write \(m\ge2\) for a size through which the twins agree.

Delete \(j\), redirect its column to \(i\) in all surviving rows,
and put \(\widetilde b_i=b_i+b_j=0\), leaving other weights
unchanged. This is strictly chronological and preserves the
physical diagonal of every survivor. If the twin jet equality
holds through \(m\), the surviving jets agree through \(m+1\)
before other edits: induct on tree size, using the common child
jets (sizes \(\le m\)) when redirecting a donor.
In particular if the twins agree through \(p\), exact order
through \(p\) is preserved with one fewer stage and no repair.

Here is a literal sufficiency condition for that high jet equality
from the shorter paid equality. Collapse \(e_j\) onto \(e_i\) in
the row difference \(A_{j,*}-A_{i,*}\), and call the resulting
linear functional on predecessors of \(j\) \(L\). Thus
\[
 (A v^h)_j-(A v^h)_i=L v^h+A_{jj}(v_j^h-v_i^h).
\]
It includes the coefficient \(A_{ji}+A_{jj}-A_{ii}\) at \(i\).
Equality of the twins through \(m\) implies \(L v^{m-1}=0\).
If the stage columns through \(m-1\) already span the columns
through \(p-1\) when restricted to \(\operatorname{supp}L\), then
\(L v^{p-1}=0\). Induct on tree size in the displayed identity to
obtain twin equality through \(p\) (or through every size if
the column span is stable forever). A concrete version uses at
most \(m-1\) actual donor sites in \(\operatorname{supp}L\) with
distinct clocks. The power probes live in the low jet span and their
Vandermonde is full, so \(L=0\) and the twins agree at every order.
Equal physical diagonals are not used. For a common diagonal and
a nonzero direct twin edge \(A_{ji}\) the coefficient at \(i\) is
nonzero; a literal low-jet donor dependence is then necessary for
a twin with this edge.

Once the later-stage merge really preserves the required outputs,
the muted keeper \(i\) can also be removed if it has no path to a
surviving active output. In particular this holds when both twins
are unused by other surviving stages, or when all surviving strict
consumer coefficients to the pair sum to zero. More generally use
the finite-jet diagonal-preserving redirection test: for the
distance-to-active grades in the merged tableau, express \(i\)'s
jet of the required size by earlier retained jets of sufficient
grade; every strict consumer then accepts that substitution.
Muting weights alone does not justify deleting the keeper or
ignoring its strict consumers.

## 2. Response modules and the first branching test

Let \(\Delta=U_j^m-U_i^m\), a vector supported on child trees of
size exactly \(m\): its lower coordinates vanish because the twins
agree through \(m\). Indeed the only possible first difference at
tree size \(m+1\) is at a unary root. If \(\Delta=0\), raise \(m\)
to the next actual first difference, or use exact redirection.

Keep the combined weights \(\widetilde b\) fixed, require all
surviving jets through \(m\) to remain unchanged, and allow strict
row alterations in the specified retained donor sets. On a retained
row \(\ell\), denote by \(F_\ell\) the span of its permitted strict
donors' \(v^m\) intersected with the kernel of projection through
\(m-1\). Its high unary change \(X_\ell\) ranges exactly over
\(F_\ell\). Indeed killing the old donor combinations through
\(m-1\) is necessary and sufficient for preservation through
\(m\), by the unary equations and induction, and any element of
the intersection has a representing row. These choices can be
made simultaneously. Descendant feedback does not enter a
response whose child has size at most \(m\).

For \(0\le d\le m-1\), let \(\Gamma_\ell=v_\ell^{d+1}\),
viewed as the responses of root forests of total size at most
\(d\), with the constant for the empty forest. These are fixed
by the repair and \(\Gamma_*=\Gamma_i=\Gamma_j\).
All the rooted outputs with one distinguished child of size \(m\)
and other children of total size at most \(d\) are restored exactly
when
\[
 \sum_{\ell\ \mathrm{retained}}\widetilde b_\ell
                      X_\ell\otimes\Gamma_\ell
                 = b_j\,\Delta\otimes\Gamma_* .               \tag{1}
\]
Indeed a rooted response with just the one high child multiplies
its response by the fixed tag. Relative to the unedited merged
tableau the residual on these outputs is exactly the muted twin's
signed difference. These are paid on the original tableau when
\(m+d+1\le p\).

The first branching member is \([u,\bullet]\) at size \(m+2\),
\(|u|=m\). At \(d=1\) the two tensor coordinates are the unary
and \(c\)-marked equations. A single editable active slot at a
different clock may fix the order-\((m+1)\) unary term but cannot
fix this fork for nonzero \(\Delta\). For a literal two-site active
fibre, every other active slot is at a different clock.

When all earlier retained stages are permitted as donors and all
retained active slots may be edited, the \(F_\ell\) are nested.
Call a slot usable if \(\widetilde b_\ell\ne0\) and
\(\Delta\in F_\ell\). Then (1) is equivalent to
\[
       \Gamma_*\in
       \operatorname{span}\{\Gamma_\ell:\ell\ \mathrm{usable}\}.
                                                               \tag{2}
\]
For necessity, take a functional detecting \(\Delta\) modulo the
last unavailable active module (or an arbitrary detector if all
are usable). Every unavailable slot vanishes under it.
For sufficiency, represent the tag target by coefficients \(h_\ell\)
on usable slots and take \(X_\ell=(b_jh_\ell/\widetilde b_\ell)\Delta\)
there. At \(d=1\), (2) asks for the same clock or at least two
distinct usable clocks. If the pair was the whole active fibre,
the second option is the only one.
For prescribed nonnested supports or fewer editable rows, (1),
not the simplification (2), is the literal criterion.

In particular any retained active slot strictly after \(j\) is
usable with unrestricted strict donors: \(\Delta\) is in its
strict child span by collapsing \(j\) to \(i\) at size \(m\).
If \(m=p-1\), the unary equation is the only remaining output
test, so such a slot alone proves exact one-stage compression.
When \(p\ge m+2\), matching (1) does not match the order-\((m+2)\)
unary outputs. After choosing repairs satisfying (1) at \(d=1\),
use the actual new child jets through \(m+1\). Their top unary
residual, projected to child coordinates of size \(m+1\), must
lie in the weighted sum of the strict donor modules at that
grade to be repaired while freezing the newly matched jets
through \(m+1\). This is the ordinary exact last-active repair
test, and it is not automatic.

## 3. When usable clocks or tags are forced by paid order

A small sufficient rank test uses only pooled output quadrature.
Let \(R=\lceil p/2\rceil\). The \(R\)-by-\(R\) power Gram for
\(\widetilde b\) is the nonsingular Hilbert matrix: mute twins
at one clock without changing any pure clock moment.
If the Gram contribution of the unavailable active prefix has
rank at most \(R-2\), the usable suffix Gram has rank at least
two and thus at least two distinct actual clock labels. It is
enough that the prefix have at most \(R-2\) nonzero pooled labels.
In particular this holds when the later twin lies at \(j\le R\):
all surviving active slots after \(j\) are usable and at most
\(j-2\) prefix sites can contribute. Global clock Gram rank
alone does not force slots physically after \(j\).

A stronger theorem uses rather than assumes the necessary
rooted conditions. Suppose unrestricted chronological
donor prefixes and every retained active slot are allowed,
\(\Delta\ne0\), and
\[
                              p\ge 2(m+d)+1 ,
                 \qquad        0\le d\le m-1.                \tag{3}
\]
Then (2) is **forced** without a generic clock assumption.
For the first fork this is \(p\ge2m+3\).

Proof. If the target tag were outside the usable span, choose
a linear tag probe \(g\) of stage grade at most \(d\) with
\(g_i=g_j=g_*\ne0\) and zero at all usable sites; let \(G(X)\)
be its exact polynomial. Suppose that \(\ell_0\) is the last
unavailable retained active site. Since \(\Delta\) already has
zero lower coordinates, its failure to lie in \(F_{\ell_0}\)
says it is outside the full child span of the surviving strict
prefix of \(\ell_0\). Choose a functional \(\psi\) annihilating
that prefix with \(\psi(\Delta)\ne0\). Let \(f\) be the associated
stage test of grade at most \(m-1\) (apply \(\psi\) to actual
\(v^m\)), with exact polynomial \(P(X)\).
It vanishes at every original stage before \(\ell_0\), since the
omitted original stage, if earlier, equals the keeper at that
grade; in all cases \(f_i=f_j\).

The vector \((c-c_{\ell_0})gf\) has zero output after every paid
power mark: earlier surviving sites have zero \(f\), the boundary
site is killed, usable sites have zero \(g\), and the original
twins cancel at their common clock. Its model
\(H=(X-c_{\ell_0})GP\) has degree at most \(m+d\).
Through (3) all the integrals of \(X^aH\) for \(0\le a\le m+d\)
are available. The rational Hilbert Gram is nonsingular over
the field, so \(H=0\). Consequently \(G=0\) or \(P=0\).

Now \(g(A-A_{\ell_0\ell_0}I)f\) has exact model
\(G(J-A_{\ell_0\ell_0}I)P=0\), with \(J\) formal integration.
Its actual output from earlier or boundary surviving active
sites is zero by triangularity and removal of the boundary
diagonal; usable sites have zero \(g\).
The two old twins alone contribute
\(b_j g_*\psi(\Delta)\ne0\), a contradiction to the paid output.
If there was no unavailable active site, the marked outputs
of \(g\) alone all vanish (the twins cancel and every other
active site has zero \(g\)); the same Hilbert argument gives
\(G=0\). Use any \(\psi\) detecting \(\Delta\) and \(gAf\) to
reach the contradiction. This proof also covers no usable
site, with its target outside the zero span.

Thus at the first possible unpaid twin distinction after a
guaranteed jet of size 5 or 6 in the high-teen order range, the
first \(c\)-fork alone is **not** a valid blanket exclusion for
unrestricted repair. The theorem concerns only the specified
first high child and fixed low tags. Feedback of higher-child
responses may already enter at higher sizes; fixing them or all
outputs is not implied by (3).

## 4. The first genuinely nonlinear fork and an exact diagnostic

In the variables \(X_\ell\) of the first changed unary response,
the first two-high-child rooted test is \([u,v]\) of size
\(2m+1\), \(|u|=|v|=m\). Write \(U_\ell\) now for the
size-\(m\) child part of \(U_\ell^m\). For all such \(u,v\) its
necessary and sufficient test after the frozen-jet response
changes is
\[
 \sum_\ell\widetilde b_\ell
  (U_\ell\otimes X_\ell+X_\ell\otimes U_\ell+X_\ell\otimes X_\ell)
       = b_j(U_j\otimes U_j-U_i\otimes U_i).                  \tag{4}
\]
The terms are literal products of two high responses, not powers
of a unary readout. No repair that preserves the newly chosen
jets through \(m+1\) can change (4). This is the lowest nonlinear
root obstruction in these variables, not a claim that later child
feedback is linear.

The square condition is genuinely independent of successful
one-high transport under explicit frozen repair slots, even
starting with a tableau of full paid order. Fix \(m\ge3\) and
\(p=2m+1\), and start with any strict tableau of order through
\(p\) over the field. Append a zero leaf-only donor and \(m\)
star donors with distinct rational clocks \(x_k\) leading only
to that zero donor. Their stage responses are \(x_k^r\) on the
bush with \(r\) leaves and zero on non-bushes. Take rational
\(\delta_k=1/\prod_{\ell\ne k}(x_k-x_\ell)\), so its moments
through degree \(m-2\) vanish and its degree-\((m-1)\) moment is
one by the leading coefficient in Lagrange interpolation.

Append terminal profiles \(P(x)\) (only coefficient \(x\) to the
zero donor) and \(Q(x)\) (add \(\delta\) on the star donors).
They have common clock \(x\), agree through size \(m\), and
their unary response difference on the child bush \(u\) of
size \(m\) is one. For \(x\ne0\) their common degree-two defect
is \(-x^2/2\ne0\).
The response difference \(D_\tau(x)=\Phi_{Q(x)}(\tau)-
\Phi_{P(x)}(\tau)\) for \(|\tau|\le p\) is polynomial of degree
at most \(m\): every nonzero difference must use a child of size
at least \(m\), and each leaf contributes just \(x\).
Give the pair at \(x=c_*\ne0\) weights \((-1,1)\). Offset its
entire rooted contribution through \(p\) with opposite multiples
of the pairs at \(m+1\) other rational clocks, using Lagrange
evaluation at \(c_*\). Take \(c_*\) outside the finitely many
other original output labels. Attach also \(m+1\) exact cancelling
terminal \(P(d_\ell)\) pairs at distinct rational \(d_\ell\ne c_*\)
of weights \(+1,-1\). These additions preserve every original
paid order condition and the pair at \(c_*\) is its whole
active clock fibre. They can be placed before the departing pair;
none of the appended terminals feeds another.

Now remove the \(c_*\) pair, freeze all remaining weights and
all rows except the \(+1\) copies at \(d_\ell\), and preserve
their size-\(m\) jets. The one-high leaf tests for the child
\(u\) and \(0,\ldots,m\) leaves uniquely force its changes to be
\(X_\ell=L_\ell(c_*)\), the Lagrange evaluation coefficients on the
\(d\)-nodes. In fact adding \(X_\ell\delta\) on the strict star
donors matches **every** rooted output through \(2m\): any
nonzero difference has exactly one high child, its profile is
scaled by \(X_\ell\), and the only other nonzero factors are
leaves. At size \(2m+1\) the rooted square \([u,u]\) requires
\(\sum_\ell L_\ell(c_*)^2=1\), since each repair slot had old
high response zero and the removed pair had signed square one.
Choose rational \(c_*\) sufficiently large that the rational sum
of squares exceeds one; this is a nonzero rational discrepancy
over any characteristic-zero field. Thus no permitted repair
matches all paid rooted outputs; the first failure in this
specified repair class can be exactly the two-high fork.
The construction is a finite-jet obstruction, not a near-minimal
tableau or a claim of noncompressibility with arbitrary new
weights and donor edits.
