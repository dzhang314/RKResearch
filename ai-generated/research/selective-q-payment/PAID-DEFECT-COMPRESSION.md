# Paid defect dimensions and where a stage minimum must read them out

Mathematical companion, independent of common-diagonal scalar saturation.
The rank inequalities do not assume a prescribed graph, nonnegative
weights, strict support of all weights, or a common diagonal.

Let \(A,b\) satisfy rooted order through \(p\) over a characteristic-zero
field and set \(c=Ae\), \(e=1\). Use stage tree vectors \(\Phi(t)\)
and tree factorial \(\rho(t)\) as in the companion proof. Let
\(\mathcal A=\{i:b_i\ne0\}\) be the physical active set. Use
\[
 f_t=\frac{\rho(t)}{|t|}\Phi(t),\qquad z_t=f_t-c^{|t|-1}.
\]
For \(3\le q\le \lfloor(p+1)/2\rfloor\) put \(l=p-q+1\) and
\(r=\lceil p/2\rceil\). Define
\[
 Z_q=\operatorname{span}\{(c^a z_t)|_{\mathcal A}:\ a\ge0,\ |t|+a\le q\},
 \quad d=\dim Z_q,\qquad E_l=\operatorname{span}\{\Phi(u):|u|\le l\}
\]
and let \(E_l^{\rm act}=E_l|_{\mathcal A}\). Multiplying a stage
tree by \(c^a\) adds \(a\) leaves to its root. Thus \(Z_q\) lies in
the active stage span through \(q\), and in \(E_l^{\rm act}\).

Equip active coordinates with the nondegenerate (not necessarily
positive) signed form \(\langle f,g\rangle_b=\sum_{i\in\mathcal A}b_i f_i g_i\).
Joining the roots of \(t,u\) and adding \(a\) leaves gives order
\(N=|t|+|u|+a-1\), factorial
\(N(\rho(t)/|t|)(\rho(u)/|u|)\), and stage value
\(c^a \Phi(t)\Phi(u)\). Replacing \(t\) by its bush of the same
size gives exactly the same normalized output when paid. For
\(|t|+a\le q, |u|\le l\), we have \(N\le p\). Subtract to conclude
\(Z_q\perp_b E_l^{\rm act}\).

The active clock monomials \(1,c,\ldots,c^{r-1}\) lie in \(E_l^{\rm act}\)
since \(r\le l\). Their Gram matrix has entries \(1/(i+j+1)\)
(\(0\le i,j<r\)) by the paid bushes, since \(2r-1\le p\). This
Hilbert matrix is invertible over \(\mathbb Q\) (real polynomial
squares integrate positively), hence over the given field.
The clock subspace has dimension \(r\) and intersects \(Z_q\)
trivially. Because the full active form is nondegenerate, we obtain
the actual active-stage bound
\[
              |\mathcal A|\ \ge\ \dim E_l^{\rm act}+d\
                                  \ge\ r+2d.                 \tag{1}
\]
The two gains per defect mode are different: one is the new
orthogonal column beyond the nondegenerate clock block, and the
other is the complementary dimension needed to pair with that
radical mode in the ambient active form. This is not equality of
the two dimensions. It uses no positivity assumption on \(b\).
No general existence of a defect on an active stage follows.
For example, for a nonzero common diagonal the very first physical
row has \(z_{[\,[\bullet]\,]}=\gamma^2\) (because the normalized
three-vertex chain value is \(2(Ac)_1=2\gamma^2\)); it gives a mode
only if the row is active. If the active-stage count is at most
\(r+1\), (1) forces all the above normalized stage equalities at
every active stage. Inactive defects are not counted.

An individual \(z_t\) nonzero at \(m\) distinct active clock labels
supplies at least \(\min(m,q-|t|+1)\) modes when \(|t|\le q\):
a polynomial combination of \(z_t,c z_t,\ldots,c^{q-|t|}z_t\)
vanishes just when its polynomial vanishes at those \(m\) clocks;
ordinary Vandermonde evaluation gives that rank. This is a useful
unconditional rank constraint on the set of active defect clocks,
rather than a count of repeated physical copies.

## Additional forced high reduced responses at a true minimum

Now assume strict chronological triangularity and genuine physical
stage minimality for order at least \(p\) in a coefficient class
admitting diagonal-preserving triangular compression. Let \(D\) be
the full-stage column span of tree tests through \(p\) with only
size-\(p\) unary-root trees omitted, and set \(K=D^\perp\) for the
ordinary, unweighted row-column annihilator. The last-active
compression proof gives \(\dim K\le1\): the reduced readout rows
preceding the last active index are independent, and no inactive
suffix is present at a minimum. If the coefficient class is
also closed under topological reindexing, a nonzero member of
\(K\) has nonzero coordinate at every strict support sink (each
sink is active; move any such sink last before compressing).

Let \(W\) be the copy of \(Z_q\) in the full dual stage space that
multiplies its active coordinates by \(b_i\) and extends by zero
on inactive coordinates. Thus \(\dim W=d\). Paid root joining above
gives \(W\subset E_l^\perp\); also \(E_l\subset D\), since \(l\le p-2\).
Consequently the evaluation map
\[
                     W\longrightarrow (D/E_l)^*
\]
has kernel exactly \(W\cap K\), and rank
\[
                         d-\epsilon,\qquad
                \epsilon=\dim(W\cap K)\le1.                 \tag{2}
\]
The images of the actual trees with orders \(l+1,\ldots,p\) in the
retained test family span \(D/E_l\). Therefore at least
\(d-\epsilon\) independent combinations of the paid dormant modes
must be detected by these higher tests, none of which is an
order-\(p\) unary root. Equivalently, among the actual such tree
columns and the weighted defect rows there is a pairing minor of
rank \(d-\epsilon\). When a strict support sink has all \(Z_q\)
defects zero, \(\epsilon=0\) by the reindexing conclusion; more
generally \(\epsilon=0\) exactly if the possible one D-relation
direction is absent from \(W\). Lower-order unary roots in the
high band are allowed; only the highest unary roots are ruled
out as the sole observation mechanism.

Thus the paid pairing by itself gives the two-dimension active
rank budget (1). The compression invariant adds (2): it locates
independent observations that genuinely cannot be seen at the
lower paid grades, and lets at most one defect mode hide
only in the terminal top unary sector. Combining (1) with
(2) does not add a second count of the same modes to (1).
It does not imply a universal stronger numeric stage floor if
\(d=0\) or the structural hypotheses do not hold. The independent
common-diagonal result does give a universal numeric gain by
excluding scalar saturation.
