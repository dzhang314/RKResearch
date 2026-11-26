# Projected bush residuals recover donor-ratio packets

Let \(A\) be an actual finite tableau over a field \(K\), with
\(\mathbf c\coloneqq A\mathbf{1}\). For a tree \(u\), write
\[
 \mathbf Q(u)\coloneqq
 u!\,A\boldsymbol{\Phi}_u(A)-\mathbf c^{\odot |u|}.
\]
At any stage \(i\) with \(c_i\ne0\), set
\(\eta_u(i)\coloneqq \mathbf Q(u)_i/c_i^{|u|}\).
The statements about stage rank below need no output equation
and no sign convention for the entries of \(A\).

## 1. Exact packet rank at a finite threshold

For \(c_i\ne0\), group donors by their ratio to the receiving clock:
\[
 D_i(r)\coloneqq \frac{1}{c_i}
        \sum_{j:\ c_j=r c_i} a_{ij}.
\tag{1}
\]
This is a mass-one finite packet, because the rows sum to \(c_i\).
A ratio can disappear through cancellation within its donor fibre.
Include only its net mass, not its number of taps. The donor stages
may themselves have zero output weights or zero clocks.

Let \(u_d\) be the bush of order \(d\) and abbreviate
\(\eta_d=\eta_{u_d}\). The reviewed formulas
\(u_d!=d\) and \(\boldsymbol{\Phi}_{u_d}(A)=\mathbf c^{\odot(d-1)}\)
give, for \(k\ge0\),
\[
 m_k(i)\coloneqq\sum_r D_i(r)r^k,\qquad
 m_0(i)=1,\qquad
 \eta_{k+1}(i)=(k+1)m_k(i)-1 .
\tag{2}
\]
In particular the self-diagonal contributes at ratio \(1\),
whether or not the diagonal is common.

**Packet rank theorem.** On any chosen receiver set with nonzero
clocks, let \(\mathcal R\) be a common ratio alphabet of \(N\ge1\)
distinct values, containing the nonzero packet masses of every
chosen receiver. Assume \(1,\ldots,N\) are nonzero in \(K\).
Write \(D\) for the matrix of masses on \(\mathcal R\). Then
\[
 \operatorname{rank}\bigl[\mathbf{1},\eta_2,\ldots,\eta_N\bigr]
       =\operatorname{rank}D.
\tag{3}
\]
In fact the column spaces agree. The matrix of \(m_0,\ldots,m_{N-1}\)
is \(D\) times the square Vandermonde on the distinct ratios,
and (2) is an invertible constant-column adjustment and scaling.
Two receiver rows have the same displayed residual profile
if and only if their packets agree.

If \(D\) has full column rank, the \(N-1\) projected residuals
of costs \(2,\ldots,N\) are independent even modulo constants.
For arbitrary rank \(r\) there are \(r-1\) independent projected
residuals modulo constants, chosen from the same list. The
threshold is exact for recovering arbitrary packets: fewer
than \(N-1\) nonconstant moment tests leave a nonzero
mass-zero kernel on \(N\) sites. This is not a claim that
particular structured tables cannot be detected earlier.
The linear-algebra sharpness also occurs on actual ERK receiver
rows without imposing output equations: feed preceding donors
of clocks \(r\in\mathcal R\) from an origin stage, then use a
mass-one packet for a new row of clock \(1\).

Here is a structural condition for full column rank. Suppose
\(\mathcal R=\{e,r_1,\ldots,r_{N-1}\}\) and the chosen rows include
an anchor of packet \(\delta_e\). In some order, let row \(i_j\)
have nonzero mass at \(r_j\) and zero mass at \(r_k\) for \(k>j\).
The resulting triangular mass block has nonzero diagonal.
This is a condition on grouped coefficients, not on labels
alone. Some broad special cases are:

- **ERK:** \(e=0\), an anchor fed only by zero-clock donors,
  and later pivot rows fed by zero-clock donors and one
  nonzero-clock ratio per row, with distinct ratios among
  the pivots. A live second stage of a strict tableau with
  nonzero clock is an anchor of this kind.
- **DIRK:** \(e=1\), an anchor fed only by equal-clock donors
  (for example the first diagonal stage with nonzero weight
  and nonzero clock). Each pivot may have arbitrary mass
  at ratio \(1\), plus one distinct other ratio. This includes
  lower bidiagonal DIRK with nonzero predecessor and receiver
  clocks, distinct predecessor/receiver ratios on the pivots,
  and a nonzero grouped predecessor coefficient. The diagonal
  need not be common. The variant allowing both zero-clock
  and equal-clock donors simply includes both endpoints in
  the common alphabet and uses (3) with the resulting \(N\).

## 2. Exact use of the fixed-order projective budget

Now keep stages with \(b_i c_i\ne0\); fix a paid order \(n\ge2\)
and give such a stage weight \(\lambda_i=b_i c_i^{n-1}\).
Use the projective residual variables with cost \(|u|\).
The selective root-cut result supplies
\[
 \sum_i \lambda_i P(\eta(i))=P(0)/n
 \quad\text{through weighted cost }L=n-2.
\tag{4}
\]
If no live clock is zero, or the exact boundary contribution is
zero for the monomials used, take \(L=n-1\). Only the same-order
cut cubes for the needed monomials and the bush are required.
The natural casts in (2) must also survive; this is automatic
from the order-\(n\) tall equation for the full order-\(n\)
tree family when \(N\le n\), but is a separate check for
arbitrary selected cut cubes.

Aggregate equal projected profiles with these \(\lambda_i\)
and discard profiles with zero net weight. The rank test is on
that **effective** support; a nonzero stage weight by itself
does not certify an effective anchor or pivot. On the bush
profile \((\eta_2,\ldots,\eta_N)\), packet grouping is identical
to profile grouping by (3). A finer profile list can be used
instead, while applying the rank test to its packet columns.

Let \(h\) be a polynomial profile mask of cost at most \(w\),
and let \(T\) be the effective profiles where \(h\ne0\).
The common packet alphabet need only cover \(T\), but must cover every contributing raw stage of each surviving profile, not just one representative. A grouped ratio pivot refers to nonzero net packet weight, after any coarsening of finer profiles.
Set \(r=\operatorname{rank}D_T\). If \(w+2N\le L\), the
masked projective rank theorem on the subspace
\(\operatorname{span}\{\mathbf{1},\eta_2,\ldots,\eta_N\}|_T\)
gives the concrete bound
\[
 |T|\ \ge\ 2r-\mathbf{1}_{h(0)\ne0}.
\tag{5}
\]
Thus an effective anchor and \(N-1\) effective triangular
pivots in the unmasked case force at least \(2N-1\) distinct
effective profiles and as many actual stages. The direct
square budget reaches this at \(n=2N+2\), or \(2N+1\)
with the stipulated zero-clock boundary improvement. These
are budget thresholds, not assertions of minimum stage
numbers. For a single unmasked step less, if \(D\) has full
column rank and \(N\ge2\), the spaces of costs \(N-1\) and
\(N\) already give \(2N-2\): the Vandermonde prefix has
rank \(N-1\). No extra order is charged for the projection.

**A verified thin-packet obstruction.** Let \(\ell_r(X)\) be
the Lagrange polynomial on \(\mathcal R\) for \(r\).
Each packet coordinate is an affine expression in the
displayed bush residuals:
\[
 D_i(r)=\sum_{k=0}^{N-1}[X^k]\ell_r(X)\,m_k(i).
\]
Its value at the zero residual profile is
\[
 D_*(r)=\sum_{k=0}^{N-1}\frac{[X^k]\ell_r(X)}{k+1}
         =\int_0^1\ell_r(x)\,dx ,
\tag{6}
\]
where the last notation is the formal polynomial integral
over \(K\). Thus any polynomial relation of total degree
\(j\) in these packet coordinates holding on \(T\) also
holds at \(D_*\), if \(h(0)\ne0\) and \(w+jN\le L\).
Apply (4) to the relation times \(h\), using affine
reconstruction to bound the weighted cost. This holds
even if the mask changes the weights on \(T\).

For example, if no row in \(T\) carries two nonzero masses
among a chosen pair of ratios, their coordinate product
vanishes on \(T\). At the square threshold it is impossible
for both corresponding \(D_*\) coordinates to be nonzero.
More generally, a row support cap of \(j-1\) on a set of
ratios rules out \(j\) nonzero reference masses there if
\(w+jN\le L\). No positivity of the stage weights is used.
There is a simple sufficient reference test over an ordered
field: if every ratio lies outside the open interval
\((0,1)\), then every \(D_*(r)\ne0\). Up to a nonzero scalar,
all linear factors of \(\ell_r\) can be written as
nonnegative combinations of \(X\) and \(1-X\), each with
a positive coefficient. The product has positive integral
since
\(\int_0^1 X^a(1-X)^b\,dx=a!b!/(a+b+1)!\) is positive.
This certifies, for example, a square-budget obstruction
to rows with just one non-endpoint donor ratio if the
alphabet has at least two non-endpoint ratios of that type.
The interval assumption is sufficient, not necessary;
one may use an exact check of (6) instead.

**A cheap selector, not a general coordinate product.** When the
alphabet holds on the whole effective support, the affine packet
coordinates give genuine profile masks of cost at most \(N\).
A singleton indicator is representable at this cost by a linear
packet functional exactly when that indicator is in the column
space of \(D\). In particular, if one ratio has a nonzero mass on
only one effective packet \(y_0\), its recovered coordinate alone
selects that packet up to an invertible scalar. No product of
separating residual columns is needed for that selector.

At the square budget this has a further consequence. Apply (4)
to \(D(r)\) and \(D(r)D(s)\), using their affine representatives.
For the private ratio \(r\) only \(y_0\) survives, so
\[
 \mu_{y_0}D_{y_0}(r)=D_*(r)/n,\qquad
 \mu_{y_0}D_{y_0}(r)D_{y_0}(s)=D_*(r)D_*(s)/n.
\]
The first value is nonzero. Cancelling it shows \(D_{y_0}=D_*\).
Thus a ratio cannot select a single nonreference effective
packet under the square payment. This is a structural partial
replacement for full-series coordinate isolation. It does not
claim that an arbitrary packet indicator is affordable.

## 3. Why chronology alone cannot give independent live residuals

Even with all equations through order \(n\), there is no
positive universal rank of the projected residuals with
\(|u|\le n-1\), for ERK or for SDIRK with any prescribed
common diagonal \(\gamma\). The following is an actual
finite construction over any characteristic-zero field.

Choose \(n\) distinct nonzero nodes \(z_j\), with Lagrange
polynomials \(\ell_j\), and assume \(n\ge3\). Start with a
single diagonal stage \(\gamma\). In the first full layer
put diagonal \(\gamma\) on each row, and coefficient
\(z_i-\gamma\) from the initial stage. Then add \(n-2\)
more layers on the same nodes: the only strict block into
row \(i\) is the immediately preceding layer, with entries
\[
 B_{ij}=\int_0^{z_i}\ell_j(x)\,dx-\gamma\delta_{ij}.
\]
At every full layer the row sums, including the self-diagonal,
are the prescribed \(z_i\). Give weights
\(\int_0^1\ell_j(x)\,dx\) only to the final layer.

On layer \(l\), every tree of height at most \(l\) and
order at most \(n\) has the exact column
\(z_i^{|t|-1}/\mathrm{forestFactorial}(t)\).
Layer one handles leaves and bushes by consistency. For
later layers, previous-layer child values are exact by
height, and current-layer child values by structural
induction at that layer. The preceding block integrates
the child polynomial and subtracts its current scaled
evaluation; the self-diagonal restores exactly that
evaluation. Root multiplication gives the assertion.
The terminal layer therefore pays all trees through order
\(n\). Its stage integral also gives
\(\mathbf Q(u)=0\) there for every \(|u|\le n-1\), since
the previous layer already sees those child values.
All live clocks are nonzero, yet every affordable projected
residual is zero on them. At \(\gamma=0\) this is strict
ERK, and at nonzero \(\gamma\) it is SDIRK. It is only an
obstruction to unconditional independence, not an efficient
or minimum-stage construction.

For \(n\ge1\), the zero-residual construction can also have exact order \(n\): take terminal clocks \(-1,\ldots,-n\). The monic node polynomial \(\prod_{j=1}^n(x+j)\) vanishes at the terminal clocks and has a nonzero rational integral, as its coefficients are positive rationals. Because quadrature pays the lower powers, the first unpaid bush fails. The construction uses no additional stages and works for every prescribed diagonal in characteristic zero.
