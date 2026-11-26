# Localized rank from selective root Q-payment

Let \(K\) be a field, \(A\) a finite actual tableau, \(\mathbf b\) its
weights, and \(\mathbf c\coloneqq A\mathbf{1}\). Write
\[
 \mathbf Q(u)\coloneqq
 u!\,A\boldsymbol{\Phi}_u(A)-\mathbf c^{\odot |u|}.
\]
A multiset \(M\) of nonleaf child positions has cost
\(d(M)\coloneqq\sum_{u\in M}|u|\) and vector
\(E_M\coloneqq\bigodot_{u\in M}\mathbf Q(u)\).
Repeated positions are included. Put \(E_\varnothing=\mathbf{1}\).
The positive statements below need neither characteristic zero,
triangularity, ordinary positive weights, nor a fixed diagonal.
Each asserted payment must hold in \(K\). The counterexamples
are over any characteristic-zero field.

## 1. Selective payment, and ordinary clock fibres

For a nonempty \(M\) and \(k\ge0\) take the root with \(k\) explicit
leaves and children \(M\). Its order is \(n=1+k+d(M)\).
It is enough to pay the tree equation for each of its cuts, where
a discarded child \(u\) is replaced by \(|u|\) leaves. These trees
all have order \(n\); they include the same-order bush. The integral
root identity then pays
\[
 L(\mathbf c^{\odot k}\odot E_M)=0,\qquad
 L(f)\coloneqq\mathbf b\cdot f .
\tag{1}
\]
It does not require other trees of order \(n\), or any lower orders.
Once the bush equation holds, the single signed sum of the cut errors
is equivalent to (1). This does not force the individual cut equations. A family closed under these root cuts
therefore has an exact conversion at its own orders; a missing cut
is not paid simply by knowing the original uncut equation.

There is also a stage-space identity before imposing any output
equations. Define \(\mathbf N_t\coloneqq
\mathrm{forestFactorial}(t)\boldsymbol{\Phi}_t(A)\).
At fixed order \(n\), the span of the differences
\(\mathbf N_t-\mathbf c^{\odot(n-1)}\) is exactly the span of the
vectors \(\mathbf c^{\odot k}\odot E_M\) with nonempty \(M\)
and \(k+d(M)=n-1\). Indeed the unsigned root expansion writes
each difference as the sum of the nonempty residual terms, and
the signed expansion writes a residual term as an alternating
sum of same-order root columns. The latter signs cancel the
common bush vector. This identity is integral even over a
commutative ring; no factor \(n\) appears until the scalar tree
equation is formed. Taking the sum of these spans for orders
through \(a+1\) identifies the usual same-order-difference
space with
\[
 Z_a\coloneqq\operatorname{span}\{
       \mathbf c^{\odot k}\odot E_M:
       M\ne\varnothing,\ k+d(M)\le a\}.
\tag{2}
\]

**Support-aware clock selection.** For a vector \(z\) let
\(C_z\coloneqq\{c_i:b_i z_i\ne0\}\), and suppose the available
instances of (1) pay \(L(\mathbf c^{\odot k}\odot z)=0\) for
\(k\in B_z\). Here a linear combination of certified monomials
is allowed, with the budget charged to each. Fix \(\xi\in C_z\).
The exact linear criterion for isolating its fibre from these
moments is that the unit coordinate at \(\xi\) belongs to the
span of the vectors \((x^k)_{x\in C_z}\), \(k\in B_z\). In that
case some \(h_z(X)\in\operatorname{span}\{X^k:k\in B_z\}\)
restricts to \(\mathbf{1}_{\{\xi\}}\) on \(C_z\), and
\[
 \sum_{c_i=\xi} b_i z_i=L(h_z(\mathbf c)\odot z)=0.
\tag{3}
\]
The criterion is also necessary if only the listed moment
constraints on otherwise arbitrary grouped masses are used:
if the coordinate is outside their row span, their kernel has
a vector nonzero in that coordinate. This necessity does not
assert freedom of the grouped masses within the class of RK
tableaux. The mask can differ for each product and need not
kill clocks where its product already vanishes.

**Fibre rank barrier.** Let \(F_\xi\coloneqq
\{i:c_i=\xi,\ b_i\ne0\}\), and take subspaces \(U,V\) spanned
by linear combinations of the actual residual vectors in (2).
Let \(U_\xi,V_\xi\) be the
images on \(F_\xi\). Suppose (3) pays the first moments of a
generating set of \(U\) and the products of a generator of
\(U\) with a generator of \(V\). The diagonal bilinear form
\(\langle f,g\rangle_\xi=\sum_{i\in F_\xi}b_if_ig_i\) is
nondegenerate, so
\[
 U_\xi\subseteq\bigl(K\mathbf{1}+V_\xi\bigr)^\perp,\qquad
 |F_\xi|\ \ge\ \dim U_\xi+\dim(K\mathbf{1}+V_\xi).
\tag{4}
\]
Under full order \(p\), if \(U\subseteq Z_a,\ V\subseteq Z_b\),
a common ordinary Lagrange clock mask suffices whenever
\(a+b+|C|\le p\), where \(C=\{c_i:b_i\ne0\}\). Its degree is
\(|C|-1\); the root itself costs the extra one. The support-aware
criterion can do better and can use sparse paid exponents and
different cut families for the different generator pairs.

For \(U=V\), set \(e=\dim U_\xi\). If the fibre mass is nonzero,
then \(\mathbf{1}\notin U_\xi\) and (4) gives \(2e+1\) live
stages. If the mass is zero, the enlarged space
\(K\mathbf{1}+U_\xi\) is itself totally isotropic and gives
\(2\dim(K\mathbf{1}+U_\xi)\) live stages. The proof is for
actual fibre images, not formal independence of tree shapes.

## 2. A fixed-order barrier that really survives truncation

Fix one order \(n\ge2\) and pay its bush. For indices with
\(b_i c_i\ne0\), put
\[
 \lambda_i\coloneqq b_i c_i^{n-1},\qquad
 \eta_u(i)\coloneqq \mathbf Q(u)_i/c_i^{|u|}.
\]
These are the residual coordinates with the clock scale removed.
Choose a finite residual index family and give its variable
\(Y_u\) weight \(|u|\). For a nonconstant monomial \(Y^M\) of
weighted degree \(d(M)\le n-1\), use (1) at the single exponent
\(k=n-1-d(M)\). On nonzero clocks its summand is exactly
\(\lambda_i\eta(i)^M\). Consequently
\[
 \sum_{b_i c_i\ne0}\lambda_i\eta(i)^M=
 \begin{cases}
 0,&0<d(M)<n-1,\\
 -\displaystyle\sum_{c_i=0}b_i(E_M)_i,&d(M)=n-1 .
 \end{cases}
\tag{5}
\]
The bush makes \(n\) a unit and the mass on the nonzero clocks
is \(1/n\). In particular, on paying the required cuts at this
one order only, for all polynomials \(P\) of weighted degree
at most \(L=n-2\) one obtains
\[
 \sum_{b_i c_i\ne0}\lambda_i P(\eta(i))=P(0)/n.
\tag{6}
\]
Take \(L=n-1\) if all live clocks are nonzero or the zero-clock
terms in (5) are known to vanish at that boundary. The proof
requires only the cut cubes for the nonconstant monomials
actually used, with the common order-\(n\) bush; it does not
require any lower tree equations. Dividing by \(c_i\) happens
only in the field and on the nonzero-clock locus.

**Rank and localization in the normalized residual profiles.**
Group equal profile vectors \(y=\eta(i)\) and put
\(\mu_y=\sum_{\eta(i)=y}\lambda_i\). Let \(H\) be their effective
support, with zero aggregated weights removed. Let \(h(Y)\)
be any polynomial mask of cost at most \(w\), and set
\(T=\{y\in H:h(y)\ne0\}\). Values of \(h\) need not be one on
\(T\). Let \(V_a(T)\) be the image on \(T\) of polynomials of
weighted degree at most \(a\). If \(w+a+b\le L\), the pairing
between \(V_a(T)\) and \(V_b(T)\) with weights \(\mu_yh(y)\)
has rank at most \(\mathbf{1}_{h(0)\ne0}\): for representatives
\(F,G\) its value is \(h(0)F(0)G(0)/n\), by (6). Both spaces
contain the constant function, so the rank is exactly that
indicator. If \(T\) is empty, (6) forces \(h(0)=0\).
The ambient pairing on \(K^T\) is nondegenerate. Restricting
the map to the dual of \(V_b(T)\) gives
\[
 |T|\ \ge\ \dim V_a(T)+\dim V_b(T)
               -\mathbf{1}_{h(0)\ne0}.
\tag{7}
\]
This counts distinct effective profiles, and hence at least
as many actual live stages. It localizes by algebraic masks
on the normalized residuals, not by claiming arbitrary
ordinary-clock moments. For a single residual of cost \(d\),
either all effective nonzero normalized values disappear
under grouping, or there are at least
\(1+\lfloor L/d\rfloor\) of them: the first \(r\) positive
power moments cannot kill \(r\) distinct nonzero effective
values when \(r\le\lfloor L/d\rfloor\), by Vandermonde.

## 3. Why a fixed-order family cannot pay ordinary clocks

The obstruction is actual even for ERK. Use the two strict
three-stage blocks with clocks \((0,1,1)\): row two takes one
copy of stage one, and the last row takes one copy of stage
two in block \(A_+\) and stage one in \(A_-\). All other entries
are zero. Read both blocks only at stage three. For
\(u=[\bullet]\) their last residuals are \(+1\) and \(-1\),
since \(A_+\mathbf c\) and \(A_-\mathbf c\) there are \(1\) and \(0\).
Their signed difference with weights \(+1,-1\) kills all bush
outputs, at every order. For \(q\ge3\) the root with \(q-3\)
explicit leaves and child \(u\) has residual readout difference \(2\).

Under \(A_\pm\mapsto\alpha A_\pm\), every tree output of
order \(m\) and every cleared root residual readout of that
order scale by \(\alpha^{m-1}\). This follows by tree recursion,
or by the homogeneous cost \(k+d(M)\) for the residual.
Therefore add disjoint copies of the signed block at distinct
nonzero scales \(\alpha_j\), weighted by \(\omega_j\).
A Vandermonde system on \(p\) scales can impose
\(\sum_j\omega_j\alpha_j^{m-1}=\mathbf{1}_{m=q}\) for
\(1\le m\le p\). Added to an actual ERK of order \(p\), the
result keeps *every* bush and every other tree order through
\(p\), but fails the selected root residual at \(q\).
Thus even all the other orders and all bushes cannot replace
the missing cut payments.

A partly paid **same-order cube** also fails in general. Keep
the same first two stages, and set the final row coefficients
on stages one and two to \(1-x/2,x/2\), with \(x=+1\) or \(-1\).
Its final clock is \(1\) and its retained normalized factor for
\(u=[\bullet]\) is \(x\). In the signed difference with \(+1\) on
the \(x=-1\) block and \(-1\) on \(x=+1\), every bush cancels.
For any \(n\ge5\), take the root with two occurrences of \(u\)
and \(n-5\) leaves. The original uncut tree also cancels, since
the retained product is \(x^2=1\) on both blocks. But a cut
retaining just one child has retained factor \(x\) and does not
cancel; the double-residual readout changes by \(4\).
Add this perturbation to a fully paid base. If desired, the
same Vandermonde scale combination with exponent \(n-1\) singled
out retains all lower tree orders as well as that uncut tree and
all bushes. The missing shape is not supplied by those equations.

Already two scales \(\alpha=1,2\), with block weights
\(1,-2^{-(p-1)}\), suffice for an explicit failure of the full
clock-fibre inference when only order \(p\) and all bushes
are imposed. Choose \(p\ge6\) and a fully paid base whose live
clocks avoid \(1,2\) and whose live \(\mathbf Q([\bullet])\) vanish
stagewise; a construction is below. The two signed block pairs
are invisible at order \(p\), and at all bushes. The added
clock-one fibre consists of two live stages of mass zero,
with residual values \(+1,-1\). Its constant and residual
vectors span dimension two. Both \(E_{\{u\}}\) and its square
are supported, on live stages, at the added labels \(1,2\).
The mask \(2-X\) localizes clock one and would cost at most
\(1+1+2|u|=6\) under full order. Yet the two-stage fibre fails
the four-stage zero-mass bound from (4). Its first masked
residual moment is \(2\), unpaid by the truncated family.
This does not contradict (7): the normalized profiles of
each signed seed are the same across the two scales, and
their reweighted masses cancel.

## 4. The zero-clock correction is real, even for full order

For completeness an elementary ERK base useful in both examples
can be made by repeating polynomial integration layers. Take
\(p\) distinct nonzero nodes \(z_j\) and their Lagrange polynomials
\(\ell_j\). Begin with a single origin stage. The first layer at
the listed nodes takes row coefficient \(z_i\) from the origin.
Each of \(p-2\) further layers uses
\(\int_0^{z_i}\ell_j(x)\,dx\) on the immediately preceding
layer. The scalars are formal integrals of polynomials.
Put the output weights \(\int_0^1\ell_j(x)\,dx\) in the last
layer. A tree of height at most the layer index and order at
most \(p\) has exact column
\(\mathbf c^{\odot (|t|-1)}/\mathrm{forestFactorial}(t)\)
on that layer. Indeed layer one handles leaves and bushes;
each later primitive is exact for the donor monomials, then
the root products give the displayed coefficient. Hence the
terminal layer pays the trees through \(p\), and its
\(\mathbf Q([\bullet])\) vanishes for \(p\ge3\).
The nodes may avoid \(1,2\), or may include the node \(1\)
as needed in the separate examples. No optimal stage count
is asserted.

To see sharpness of (5) at every \(n\ge3\), start with this
ERK at \(p=n\) and take an existing terminal donor of clock
one. Adjoin probe stages at \(n+1\) distinct clocks
\(\alpha_0=0,\alpha_1,\ldots,\alpha_n\), each using coefficient
\(\alpha_j-1\) on the original origin and coefficient \(1\)
on that donor. At the probe, the integral of a leaf is
\(\alpha_j\); the integral of any nonleaf branch is independent
of \(\alpha_j\), because its origin column is zero. Thus for
every tree through \(n\) the probe column is a constant times
\(\alpha_j^a\), with \(a\) the number of its root leaves.
Choose weights equal to the leading coefficients of the
Lagrange polynomials for the \(n+1\) probe clocks. All those
weights are nonzero, and their moments of powers \(0,\ldots,n-1\)
vanish by polynomial interpolation. The probes leave every
tree equation through \(n\) unchanged.

Take a nonleaf \(u\) of order \(n-1\). At the new zero-clock
stage,
\[
 \mathbf Q(u)_0=u!\,(\boldsymbol{\Phi}_u(A))_{\mathrm{donor}}=n-1.
\]
The other original zero-clock coordinate has zero weight. Hence the right side
of (5) at \(d(M)=n-1\), \(M=\{u\}\), is nonzero. This is an
actual order-\(n\) ERK counterexample to omitting the boundary
term. Equations (6)–(7) should not be quoted one weight higher
without proving the zero-clock condition.
