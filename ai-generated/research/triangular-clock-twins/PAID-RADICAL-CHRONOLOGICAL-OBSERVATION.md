# Paid invisible radicals and chronological deletion

Mathematics only. The new result concerns the actual frozen
chronological substitution indicated by a covector. It applies
to ERK and mixed-diagonal triangular methods; it does not equate
a paid adjoint rank loss with a global stage-count redundancy.

## 1. An exact one-pivot surgery and its rooted contexts

Let \(A\) be lower triangular, \(b^T\) the output, and use the
literal stage-tree values
\[
 \Phi(\bullet)=e,\qquad
 \Phi([u_1,\ldots,u_a])=\prod_{v=1}^a A\Phi(u_v),
\]
with componentwise products. Put \(C=\operatorname{diag}(Ae)\)
and \(D=[C,A]-A^2\). Let \(f\) be a nonzero row covector with
\(f(e)=0\), and let \(k\) be its latest nonzero coordinate.
Suppose \(k\) is explicit, \(A_{kk}=0\). In particular this
last condition follows over any field if \(fD=0\): the
\(k\)-th coordinate of \(fD\) is \(-f_k A_{kk}^2\).
Over a general ring the explicit condition should be imposed
separately; a square-zero diagonal need not vanish.

For an indeterminate \(t\) put
\[
      P_t=I-t e_k f,\qquad A_t=A P_t,\qquad b_t^T=b^T P_t.       \tag{1}
\]
Here \(e_k\) is the coordinate unit, not the all-ones column.
The only changed matrix entries lie at a strict receiver after
\(k\) and a column at or before \(k\), because
\(A e_k\) is zero through row \(k\). Thus every diagonal and
every stage jet at or before \(k\) is unchanged, the latter
by rooted induction. In particular
\[
                        f(\Phi_t(u))=f(\Phi(u))                 \tag{2}
\]
as a polynomial for every tree. At \(t=1/f_k\), column \(k\) of
\(A_t\) and weight \(k\) of \(b_t\) vanish. Delete that stage;
the remaining chronology and physical diagonals are inherited.
Over a commutative ring the same construction works when the
explicit condition holds and \(f_k\) is a unit. The identities
before this specialization use no division.

The output difference in (1) has an exact old-context
expression. Regard a rooted tree as having child **occurrences**,
so repeated isomorphic children are counted separately.
For an antichain \(M\) of vertices of a rooted tree \(\tau\),
let \(L_{\tau,M}(e_k)\) be its original scalar output with the
subtree stage argument at each vertex in \(M\) replaced by
the coordinate \(e_k\). The incoming \(A\) factor at each
marked edge is retained; a mark at the root replaces the
argument of \(b^T\). A root mark is a singleton antichain.
Writing \(\tau_v\) for the subtree below occurrence \(v\), one has
\[
 b_t^T\Phi_t(\tau)-b^T\Phi(\tau)=
  \sum_{\varnothing\ne M\ {\rm antichain}}
     (-t)^{|M|}L_{\tau,M}(e_k)\prod_{v\in M}f(\Phi(\tau_v)).
                                                               \tag{3}
\]
To prove this, set \(V_t(u)=P_t\Phi_t(u)\). At a vertex either
the ordinary term \(\prod A V_t(u_i)\) is chosen, or the term
\(-t e_k f(\Phi(u))\) is chosen, by (2). The latter terminates
the expansion below that occurrence. The same description
at the root feeds the fixed \(b^T\). Induction gives (3), with
no contribution from nested marks. It uses explicitness of
the pivot, not nilpotent powers of \(D\) as a surrogate for
rooted responses.

Consequently (3) evaluated at \(1/f_k\) is the exact finite
criterion for this chronological deletion to preserve all
rooted outputs through \(p\). If all \(f(\Phi(u))\) vanish in
sizes \(<L\), any term with two distinct marks needs two
disjoint subtrees of size at least \(L\) and their exterior
root, so has size at least \(2L+1\). In the paid range
\(2L+1>p\), the criterion is therefore exactly the **linear
one-hole test**
\[
       \sum_{v\in V(\tau)}
                    L_{\tau,\{v\}}(e_k) f(\Phi(\tau_v))=0
                           \quad (|\tau|\le p).                 \tag{4}
\]
It is the sum for each actual tree that must vanish; a
termwise zero condition is sufficient, not necessary.
A one-hole observation of \(e_k\) is relevant only when its
exterior cost \(|\tau|-|\tau_v|\) is at most \(p-L\).
Outside the affine paid range (3), not just an old linear
adjoint flag, is the correct test.

If \(L\le p\) is the actual first nonzero size and \(b_k f(\Phi(\tau))\ne0\) for a tree \(\tau\) of size \(L\),
this substitution cannot work: in a first residual tree
of size \(L\) only the root mark can contribute, and its
value is \(-b_k f(\Phi(\tau))/f_k\ne0\). This obstruction is
about the substitution given by \(f\), not about arbitrary
changes of other rows and weights.

## 2. Paid hits yield a sharper physical-minimum test

Let \(E_a\) be the span of actual stage columns of grade
\(|u|-1\le a\). From the paid Volterra calculus, an invisible
hit \(f\in \ker D^*\cap U_{j-2}D\) at reverse grade \(j\)
annihilates \(E_{p-1-j}\); invisibility here also includes
the constant moment. Thus it kills jets through size
\(p-j\). A live residual starts no earlier than \(L=p-j+1\),
and if \(2j\le p+2\) the complete paid surgery is affine.
The only additional tests are actual rooted contexts of
cost at most \(j-1\) in (4), including the output mark.
They are not implied by \(\ker D^*\), clock invisibility,
or the low-degree \(E_{p-1-j}\) pairing.

There is a linear minimality consequence. Over a field let
\(H\subseteq \ker D^*\cap U_{j-2}D\) be a subspace of such
invisible hits, at \(2j\le p+2\). For a coordinate \(k\)
that is a leading pivot of some \(f\in H\), let
\(H_{\le k}=\{f\in H:\operatorname{supp}f\subseteq[1,k]\}\).
Let \(\mathscr L_k\) be the linear map on \(H_{\le k}\)
whose coordinates are the sums in (4) using \(e_k\).
At a physical stage minimum for order through \(p\), in a class closed under this
inherited-diagonal surgery (for example ERK or unrestricted
lower triangular methods over the fixed field),
\[
               \ker\mathscr L_k\ \subseteq\
                        \ker\bigl(f\mapsto f_k\bigr).            \tag{5}
\]
Otherwise normalize a counterexample and use (1) to delete
its stage by (4). Equivalently the actual rooted-context sums
linearly detect the chronological pivot coordinate on this
subspace. This is more precise than saying a pivot must be
reachable from \(b\), or testing it only by clock-decorated
linear paths. It is a compression criterion rather than
another mask-only dimension count.

## 3. A uniform achieved-order counterexample to automatic surgery

For every \(p\ge4\) over \(\mathbb Q\) the following construction
has an actual nonzero paid hit at \(j=2\), with the **whole**
left kernel supported at clock zero, for which (1) fails at
an active latest pivot. It is not claimed stage-minimal.
It shows the hit itself does not justify the prescribed
chronological transfer.

Start with an independent nonsingular lower triangular
tableau \(A_B,b_B\) of order through \(p+1\). A rational
one exists by extrapolating implicit Euler blocks as checked
in Section 4 below. Place the following stages before
or alongside that block with no edges to or from the
base block, followed by the terminal rows described last.

Take five distinct zero rows (all explicit, hence clock zero):
\(o,o_x,o_y,o_h,o_{h'}\), and put
\(h=\epsilon_{o_h}-\epsilon_{o_{h'}}\), using coordinate
covectors \(\epsilon_i\). Append \(p-1\) implicit stars with
distinct nonzero rational clocks \(a_i\). Star \(i\) has
sole strict donor \(2a_i\) at \(o\) and diagonal \(-a_i\).
On every tree its stage value is \(\pm a_i^{|u|-1}\)
with a sign depending only on the tree, because a leaf child
gives \(a_i\), while a nonleaf child uses only the diagonal
and multiplies its value by \(-a_i\).
Choose the row \(u=\sum_i r_i\epsilon_{\mathrm{star}\ i}\)
by Vandermonde interpolation, with
\(\sum_i r_i a_i^m=0\) for \(0\le m<p-2\) and
\(\sum_i r_i a_i^{p-2}=1\). For example the \(r_i\) are
the leading coefficients of the nodal Lagrange polynomials.

Use two further explicit rows \(k,k'\) with strict rows \(u,2u\),
respectively, and put \(k'\) after \(k\). Both have clock zero.
Their stage values on nonleaf trees through size \(p-1\)
are zero. At size \(p\) only a unary root can have a nonzero
response, in which case the second row has twice the first
value. In particular on a unary root above a bush with
\(p-1\) vertices the values are \(1,2\).
Put weights \(1,-1/2,-1/2\) at \(k,k',o\), respectively;
all other stages of this group have weight zero. Its full
rooted output through \(p\) is zero, including its leaf sum.
The \(D\)-rows at \(k,k'\) are zero: \(C=0\) there and
\(u(C+A)=2(\sum r_i a_i)\epsilon_o=0\).
All neutral rows also have \(D\)-row zero.

Let \(A_0,b_0,C_0,D_0\) be the tableau so far, and put
\[
                f_0=\epsilon_k-\epsilon_o,\qquad
                g=f_0-b_0^T D_0 .
\]
The row \(g\) kills every child tree through size \(p-1\).
For \(f_0\) it follows from the stage calculation. For
\(b_0^T D_0=b_B^T D_B\) it follows from the base paid
order \(p+1\) and the degree-two zero-model property of \(D\).

Choose \(x=2,y=1\). Add four terminal explicit rows, all
using only the old prefix:
\[
 \begin{array}{ll}
 P_x:x\epsilon_{o_x}, & Q_x:x\epsilon_{o_x}+g+h,\\
 P_y:y\epsilon_{o_y}, & Q_y:y\epsilon_{o_y}+g .
 \end{array}
\]
Give them weights \((-1,1,1,-1)\) in that order.
Each pair has identical stage jets through \(p\), by the
child-size bound on \(g,h\), so the two pairs contribute
zero rooted output. The whole tableau has achieved
order at least \(p\). Its added \(D\)-row contribution
is nevertheless nontrivial: at a common clock \(x\), a
strict row contrast \(v\) contributes
\(xv-v(C_0+A_0)\) to the contrast of \(D\)-rows.
Here \(h(C_0+A_0)=0\), and subtracting the two pair contrasts
gives \((x-y)g+x h=g+2h\).
Consequently the actual full weight satisfies
\[
              b^T D=f_*=f_0+2h,\qquad f_*D=0.                  \tag{6}
\]
The latter equality holds because the participating stage
rows have zero \(D\). The covector is invisible to all pure
clock powers and to all tree jets through size \(p-1\).
Its latest coordinate is \(k\) with coefficient \(1\).

For completeness the whole left kernel really does live
at clock zero, rather than just the displayed hit.
Eliminate the rows with nonzero diagonal of \(D\), namely
the base stages and the implicit stars, by quotienting the
row space by their span. This projects onto the zero-mask
coordinates. Base coordinates project to zero. Each star
has \(D\)-row
\(4a_i^2\epsilon_o-a_i^2\epsilon_{\mathrm{star}\ i}\);
therefore its unit covector projects to \(4\epsilon_o\).
In particular \(u\) projects to zero, \(g\) projects to
\(f_0\), \(g(C_0+A_0)\) projects to zero (its gadget part
is \(u\) and its other part is in the base block).
The four projected terminal rows are thus
\[
 x^2\epsilon_{o_x},\
 x^2\epsilon_{o_x}+x(f_0+h),\
 y^2\epsilon_{o_y},\
 y^2\epsilon_{o_y}+y f_0 .
\]
They are independent: the two backing sites are distinct
and \(f_0,h\) are independent on the other earlier sites.
All remaining zero-mask rows have literal \(D\)-row zero.
Thus a left kernel covector has no terminal or nonzero-
diagonal coefficient, and the kernel is exactly the span
of the earlier neutral, \(k\), and \(k'\) coordinate rows,
all at clock zero. Since \(U_0=\operatorname{span}(b^T)\),
(6) realizes a nonzero invisible transported loss at the
paid step \(j=2\).

Finally the size-\(p\) unary tree above the \((p-1)\)-bush
has \(f_*(\Phi)=1\) at this actuation. The pivot \(k\) is
active with weight \(1\); the root mark is the only mark
that fits in size \(p\). The chronological substitution
given by \(f_*\) therefore changes that output by \(-1\).
This is an actual-order family disproving automatic
elimination by the given paid hit. Its other auxiliary
stages or independently chosen weight repairs are not
frozen by global minimality, and no statement excluding
all smaller methods is inferred.

## 4. A nonsingular rational base at every order

For a positive integer \(n\), take the \(n\)-stage backward
Euler substep block \(A_{ij}=1/n\) for \(j\le i\), zero
otherwise, with every weight \(1/n\). Its diagonals are
nonzero. On a tree \(t\), the \(i\)-th stage value is
\(n^{-(|t|-1)}P_t(i)\), where \(P_t\) is a rational polynomial
of degree \(|t|-1\), independent of \(n\). This follows by
induction: a unary factor for child \(u\) sums
\(P_u(1),\ldots,P_u(i)\) and adds one power of \(1/n\).
Polynomial summation raises degree by one and divides the
leading coefficient by the new degree. Thus the leading
coefficient of \(P_t\) is \(|t|/\rho(t)\), by the tree
factorial recursion. The block output
\(n^{-|t|}\sum_{i=1}^n P_t(i)\) is a polynomial in \(1/n\)
of degree at most \(|t|-1\) (the sum is zero at \(n=0\));
its constant coefficient is \(1/\rho(t)\).
A direct sum of blocks for \(n=1,\ldots,p+1\), with their
output rows weighted by the Lagrange evaluation coefficients
at \(0\) on the nodes \(1/n\), therefore has order through
\(p+1\). This supplies the specified rational nonsingular
base without any order-specific construction or search.
