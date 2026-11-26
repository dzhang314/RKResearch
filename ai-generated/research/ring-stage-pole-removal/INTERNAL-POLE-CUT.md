# Internal pole splitting and minimum two-sheet cuts

Source-only mathematics. The replay construction is over a commutative
ring. The sharp node count and exact signed cut optimization are for
domains as stated below. No arbitrary-tableau stage optimum is claimed.

## 1. Literal stage pencils and regional replay

Let \(R\) be a commutative ring and \(\ell\) a non-zero-divisor; put
\(S=R[\ell^{-1}]\), \(t_*=\ell^{-1}\). Thus \(R\to S\) is injective.
An \(s\)-stage triangular tableau over \(S\) has coefficients in \(R\)
except possibly the strict part of one row \(i\), which is
\(a_0+t_*r\) with \(a_0,r\) over \(R\). Its physical diagonal, like
every other one, is fixed in \(R\). For an earlier-donor child tree
\(u\) write \(r_u=\sum_{k<i}r_k\Phi_k(u)\). Assume \(r_u=0\) when
\(|u|<d\), for an integer \(d\ge1\). Here
\[
 \Phi_j(\bullet)=1,\qquad
 \Phi_j([u_1,\ldots,u_a])=\prod_{v=1}^a\sum_k A_{jk}\Phi_k(u_v).
\]
No factorials or coefficient divisions are needed for this recursion.

Choose copied indices \(D\subseteq\{i,\ldots,s\}\) containing \(i\).
Define \(\Psi^D_j(T,u)\) for \(j\in D\) by the stage recursion over
\(S[T]\), with source strict row \(a_0+Tr\). For a strict donor in
\(D\) use its own polynomial; for one outside \(D\) use its **original**
stage value, constant in \(T\). The diagonal uses the same polynomial
stage as its own donor, on a smaller tree. At \(T=t_*\) all these
polynomials specialize to the original jets by induction on tree size.

Let \(\delta_j\) be the shortest length of a strict nonzero-support
path from \(i\) to \(j\) contained in \(D\), with \(\delta_i=0\).
An unreachable site has no \(T\)-dependence. For \(h\ge1\),
\[
       [T^h]\Psi^D_j(T,u)=0\quad\text{if } |u|<hd+1+\delta_j.       \tag{1}
\]
For the induction, a direct \(Tr\) term consumes a child of size
at least \(d\). In another row, a degree-\(h\) child response from
\(k\in D\) needs \(|u_{\rm child}|\ge hd+1+\delta_k\); along a
strict edge \(k\to j\), \(\delta_j\le\delta_k+1\).
A diagonal donation has \(k=j\) and hence needs one more child
vertex, not one less. In multiplying root factors the positive
degrees add, and their child-size lower bounds add. With at
least one such factor this leaves \(hd+\delta_j\) child vertices,
plus the root. If a stage is unreachable, so are all its
contributing strict donors in \(D\). This proves (1).

Take finitely many integral nodes \(t_\nu\in R\). Replace each \(j\in D\)
by consecutive copies indexed by \(\nu\), with no strict edges between
copies of the same physical stage. A copied receiver takes the old
coefficient to an unsplit donor or to the **same-sheet** copied donor.
Its own diagonal is unchanged; the source copy has strict row
\(a_0+t_\nu r\). An unsplit receiver uses integral interpolation weights
on copies of each old copied donor. Do the same at output taps of copied
stages; unsplit weights stay fixed.

Specifically, an old coefficient \(c\) on such an edge or tap only
needs to be represented through the relevant **child** horizon \(H\).
For protection of every unsplit stage through size \(p\), \(H=p-1\)
at edges and \(H=p\) at output. A sufficient moment budget is
\[
 q_j(H)=\max\!\left(0,\left\lfloor\frac{H-1-\delta_j}{d}\right\rfloor\right),
 \qquad
 \sum_\nu w_\nu t_\nu^h=c/\ell^h\quad(0\le h\le q_j(H)),              \tag{2}
\]
taking \(q=0\) if the relevant response is constant or the stage
is unreachable. Moment zero allocates the old total coefficient.
Equation (2) gives
\(\sum_\nu w_\nu\Psi^D_j(t_\nu,u)=c\Psi^D_j(t_*,u)\) for the paid
sizes. A simultaneous size induction gives exactly the original
jets at unsplit stages and exactly \(\Psi^D_j(t_\nu,u)\) at the
copies: verify each child factor by the interpolation equation for
a crossing edge, and use the same-sheet recursion for a copied
receiver. Output interpolation then gives all original rooted outputs
through \(p\). No contiguity of \(D\) is required. In particular
an unsplit stage between copied stages can be reconstructed and
then shared by all later sheets.

The same proof works with stage horizons \(0\le h_j\le p\), if
active stages have \(h_j=p\) and every allowed strict donor has
\(h_k\ge h_j-1\) for a receiver \(j\). Include the support union of
\(a_0,r\) when assigning source donors (or simply give all stages
earlier than \(i\) horizon \(p\)). Crossing into \(j\) now uses
\(H=h_j-1\); with no child tests no interpolation is required.
These are equality-of-rooted-output statements. A particular
rooted-order normalization can be imposed in \(S\) or \(R\) when
its target scalars are available.

For \(2d>p-1\), (1) makes all paid profiles affine. At \(q=1\)
and \(c=\ell u\) use nodes \(0,1\) with weights
\((\ell-1)u,u\); at \(q=0\) assign \(c\) to sheet zero.
Thus **internal edges inside the copied region need no divisibility**.
Copying its whole forward cone removes every edge-boundary test.
An inactive source's size-\((2d+1)\) square is also irrelevant when
its protected **child** jets end at \(2d\).

## 2. Ring interpolation and exact obstructions

With \(q!\ell^q\mid c\), nodes \(0,\ldots,q\) satisfy (2) without
any factorial units: if \(c=q!\ell^q u\), then the weights are
\[
(-1)^{q-j}\binom qj u\,\prod_{0\le k\le q,\ k\ne j}(1-k\ell).
\]
These are the Lagrange expressions after clearing denominators.
The identities hold in the universal integral polynomial Laurent
ring in \(\ell\) and hence after specialization. For different
budgets use the needed initial part of a single node list. If the
largest factorial is a unit, \(\ell^q\mid c\) suffices.

More generally if \((\ell,Q!)=R\) for the maximum budget \(Q\),
choose \(v\) with \(1-\ell v\in Q!R\) and use \(v,\ldots,v+Q\).
Again \(\ell^q\mid c\) suffices: write \(1-\ell v=q!u_0\).
For \(j>0\), the Lagrange numerator at \(t_*\), after multiplication
by \(\ell^q\), contains the factor \(q!u_0\) from the zero offset;
its signed denominator \(j!(q-j)!\) divides \(q!\) in the integers.
Take the zero-offset weight by subtracting all others from \(c\).
This uses polynomial expressions with integral coefficients, not
cancellation of possibly nonregular factorial elements of \(R\).
One can verify the expressions before imposing \(t_*=v+q!u_0/\ell\)
as the evaluation point and then specialize using the relation.

In \(\mathbb Z\), for \(c\) integral and \(\ell\ne0\), the exact
full-moment condition with any integral nodes is
\[
             c\in \ell^q\prod_{\pi\mid\ell}
                            \pi^{v_\pi(q!)}\mathbb Z.              \tag{3}
\]
Indeed \(c\binom{1/\ell}{h}\) must be integral for all \(h\le q\),
since binomial polynomials are integer-valued at every integer
node. The same tests suffice on \(0,\ldots,q\) by their
unit-triangular evaluation matrix. The power moment \(h=q\) first
forces \(\ell^q\mid c\). In
\(\prod_{k<h}(1-k\ell)/h!\), a prime not dividing \(\ell\)
has numerator valuation at least that of \(h!\), by counting
one residue in each complete block modulo its powers. A prime
dividing \(\ell\) divides none of those factors, so \(h=q\)
forces the extra part in (3), which then suffices at all smaller
\(h\). For instance even \(\ell\) can obstruct a quadratic split
with \(c=\ell^2\): integral moments satisfy \(m_2=m_1\bmod 2\).

The local stage tests can **force** the moment conditions. Suppose
a size-\(d\) child \(u\) has \(r_*=r_u\ne0\). The source root with
\(h\) copies of \(u\) has size \(hd+1\) and response
\((x+Tr_*)^h\): the fixed self-diagonal's response on \(u\) is
constant. For a copied stage \(j\) at finite distance \(\delta_j\),
let \(P_j\) be the signed sum of the products along shortest
internal paths. The \(\delta_j\)-fold unary lift of that source
fork has size \(hd+1+\delta_j\) and its degree-\(h\) coefficient
at \(j\) is
\[
                                  P_j r_*^h.                      \tag{4}
\]
To check this, at size \(hd+1\) only \(i\) can carry degree \(h\),
by (1). A unary lift acts on the positive-degree column by the
restricted constant matrix on \(D\), plus for \(h=1\) a forcing
at \(i\) alone. A forcing in one of the subsequent lifts has
fewer than \(\delta_j\) remaining hops and cannot reach \(j\).
In \(\delta_j\) hops a diagonal loop would leave too few strict
hops, so the transfer coefficient is the signed shortest-path
sum. This proves (4) also for \(h=1\).

If \(P_j r_*\ne0\) in a domain, the leaf and these lifted forks
form a triangular family of degrees \(0,\ldots,q_j(H)\)
with nonzero leading entries. Consequently replaying an
individual nonzero coefficient \(c\) on these profiles forces
every moment in (2). In a general ring the same conclusion
holds if the leading entries are non-zero-divisors; nonzero
alone is not enough. In a domain with nonunit \(\ell\), the
moments force \(\ell^q\mid c\) and at least \(q+1\) distinct
integral nodes. Otherwise the product of the node factors has
degree at most \(q\), vanishes on the copies, and is nonzero at
\(1/\ell\). Thus the first paid quadratic at \(2d+1+\delta_j\)
requires three nodes in this architecture. A direct receiver
must lift it once more before it can appear in that receiver's
stage trees. Shortest-path cancellation invalidates the
nonzero-leading premise; distance gives an upper degree bound,
not observable rank. The actual truncated profile is decisive.

There is a separate ring-intrinsic first-order obstruction.
If a direct source receiver \(k\) satisfies \(A_{ki}r_*\notin\ell R\),
its size-\((d+2)\) unary jet on the source's first affected tree
is not in \(R\). All other donors at size \(d+1\) are integral
by (1) applied to the whole forward cone (a strict hop costs one).
Its value differs from the integral \(T=0\) baseline by precisely
\(A_{ki}r_*/\ell\). No integral tableau can preserve that
receiver's jet if this size is protected. This does not say that
an unrelated method must preserve individual receiver jets.

For actual affine profiles \(V^0_j+T H_j\), exact replay of
one edge uses weights \(c-w,w\); it is equivalent to
\[
                          (\ell w-c)H_j=0                         \tag{5}
\]
on its paid coordinates. The leaf fixes the total. Over a domain
the test is precisely zero slope or \(\ell\mid c\); over a
general ring it is \(c\in\ell R+\operatorname{Ann}(H_j)\).
If several old edges may compensate in the same row, use the
summed old child vector in the allowed integral prefix module
instead; (5) is then not necessary individually.
With the entire affine forward cone copied, let
\(M=\sum_j RH_j\) in output jet coordinates. Balanced combined
weights \(b_j-w_j,w_j\) exist exactly when
\(\sum b_jH_j\in\ell M\). If the outputs are integral and \(M\)
is \(\ell\)-saturated in the ambient jet module, this holds
without coefficientwise output divisibility.

A pole on the **diagonal itself** has different payment. For a
source diagonal \(\gamma+T\eta\), assume the combined low
residue \(r_u+\eta\Psi_i(0,u)\) vanishes below size \(d\), and
take its nonzero value \(r_*\) at size \(d\). A unary chain
of \(h\) lifts of that child has size \(d+h\) and top coefficient
\(\eta^{h-1}r_*\): each extra factor \(T\eta\) may reuse the
previous perturbed self-stage. The bound for degree \(h\) is
now \(d+h\), by induction (a degree-\(h\) branch costs at least
\(d+h-1\) child vertices). A first quadratic can therefore
occur at the unary size \(d+2\). These variable-diagonal sheets
would not preserve a fixed common diagonal, and cannot use the
fixed-diagonal \(2d+1\) cutoff.

## 3. Worked explicit nondivisible crossing

Take \(R=\mathbb Z[1/6]\), \(\ell=5\), \(p=4\). Use four
strict stages: a zero row \(o\); a stage \(v\) with only
\(A_{vo}=1\); a source \(i\) with row
\(-o/5+v/5\); and a receiver \(k\) with only \(A_{ki}=1\).
The output weight is \(b_k=5\), all others zero. Here row notation
lists donor coefficients. The source residue \((-1,1)\) kills
the leaf and has value \(1\) on the size-two unary child, so \(d=2\).
The source's size-three chain value is \(1/5\); the receiver's
size-four chain value is \(1/5\). Thus the output chain value
is \(1\), but \(k\) cannot be left with the same protected jets
in an integral tableau: \(A_{ki}=1\) is not divisible by \(5\).

Copy the region \(\{i,k\}\). The source rows are \(0\) and
\(-o+v\); the two copies of \(k\) each take coefficient \(1\)
from the source on their own sheet. Their output weights are
\(4,1\). All coefficients are now integral over \(R\) and all
rooted outputs through size four agree by the preceding theorem.
In particular their respective size-four chain responses are
\(0,1\), with weighted sum \(1\). This block illustrates
literal output preservation, not by itself an order-four
normalized method (its leaf output is \(5\)). For an exact
order-four example, take an independent classical RK4 block
and append this original block together with an independent
integral six-stage copy of its realization with negated output
weights. The extra rooted outputs cancel through order four,
and replacing the singular block preserves the full order.

## 4. Minimum-cut width in the affine replay architecture

Use a domain and \(p\le2d\). Fix the protected horizons from
Section 1, and require **independent** replay of each crossing
coefficient and each copied stage's output contribution. Count
one extra physical stage for each declared copied index (or
any nonnegative rational/integer penalty per index). The source
is required to copy. Coalescing copies afterwards or allowing
joint cancellations between crossing columns changes this
optimization problem.

### A least robust cut

If no signed cancellation is to be used, deem an edge \(j\to k\)
from \(j\in D\) unsafe when \(A_{kj}\notin\ell R\) and
\[
                             d+1+\delta_D(i,j)\le h_k-1.
\]
Add \(k\) to \(D\) whenever such an edge crosses. Start at \(\{i\}\)
and repeat. The closure operator is monotone: enlarging \(D\)
can only shorten internal distances. It has a unique least
fixed region, which every robust feasible region contains.
At its output sites require \(\ell\mid b_j\) whenever a response
of size \(d+1+\delta_D(i,j)\le p\) could be visible. If an
unsafe output remains, no larger region can remove that robust
violation. Otherwise the least region minimizes every
nonnegative copy cost in this robust class. This is a sufficient
topological rule in a signed domain, not an exact rule if paid
path sums can cancel.

### Exact frontier optimization with signs

The exact signed cut problem is finite and can be optimized
without treating signed paths as independently observable.
Let \(\Phi^0\) be the wholly integral global pencil at \(T=0\),
and \(F_j^0(u)=\sum_k A^0_{jk}\Phi_k^0(u)\) its baseline child
factor. On vectors of tests through size \(p\) define the
integral operator
\[
 (G_j x)([u_1,\ldots,u_a])=
       \sum_v x(u_v)\prod_{w\ne v}F_j^0(u_w), \qquad
 (G_jx)(\bullet)=0,
\]
and \(L_j=(I-A_{jj}G_j)^{-1}G_j\), a finite geometric sum
since \(G_j\) raises the first possible nonzero size.
Let \(R_\sharp=(r_u)_u\), with zeros below \(d\).
For a region's actual slope use \(H_j=0\) at an unsplit index
and otherwise use
\[
              H_j=L_j\left(\mathbf1_{j=i}R_\sharp
                                      +\sum_{k<j} A^0_{jk}H_k\right).
                                                                    \tag{6}
\]
To check independence of the region in these operators,
a positive-degree branch requires a child of size at least \(d\);
its other siblings have total size at most \(p-1-d<d\).
All these constant sibling factors are unchanged from the
global baseline, even if an unsplit predecessor elsewhere
has a pole at higher size. Expanding the coefficient of \(T\)
therefore gives (6) after eliminating self-donation by the
finite sum. In particular the slope vectors in (6) are in \(R\)
although some old evaluated jets live only in \(S\).

Scan the actual stages chronologically. At stage \(j\):
* An unsplit choice is allowed exactly when every nondivisible
  incoming edge from a previously copied stage has zero slope
  on the required child sizes. Record zero slope at \(j\).
* A copied choice computes (6), and is allowed exactly when its
  output is divisible or that output's required slope is zero.
  Record the new slope and charge the copy cost.
* At \(i\) keep only the copied choice. Once an earlier slope has
  no remaining consumer, discard it. Truncating a slope beyond
  all its remaining required child sizes is also harmless.

By (5), these are exactly the feasibility tests under
independent replay. The open chronological frontier consists
of already processed indices having remaining consumers.
Options with identical slope data on it have identical feasible
continuations; their past taps have already been checked.
Keeping the smaller cost at each equivalent state gives a
shortest-path optimization through the chronological layers.
The minimum final cost is the exact minimum for this two-sheet
model. This uses only the ring equality and divisibility
relations; it makes no computational-complexity or
divisibility-oracle promise for arbitrary presented domains.

### Signed diagnostic: an optional copy can shrink the exact minimum

Take \(R=\mathbb Z\), \(\ell=5\), \(d=4\), \(p=8\). Use a zero
donor and star stages at clocks \(0,1,2,3\), each using only the
zero donor. The strict source row is \(r/5\) on these stars,
with \(r=(-1,3,-3,1)\) and zero baseline. It kills all tree
sizes below four, since it kills clock powers of degrees
\(0,1,2\) and the star's non-bush responses are zero. Its
first value on the size-four bush is \(r_*=6\).

After the source put two relays \(v_1,v_2\), each with sole
source coefficient \(1\), and an optional relay \(w\) with
sole source coefficient \(5\). A join \(z\) takes coefficients
\(1,4,-1\) on \(v_1,v_2,w\). Finally take \(N\ge2\) receivers,
each with sole coefficient \(1\) on \(z\) and output weight \(5\).
Only these final receivers have output weight. All diagonals
are zero. This is a cut diagnostic for those literal outputs,
not a normalized order-eight method.

The source, \(v_1,v_2,z\) must copy: their incoming
nondivisible edges detect the source's sizes five and six
on the required child horizon seven. Without copying \(w\),
the join's size-seven first slope is \((1+4)r_*\ne0\);
all \(N\) final receivers must then copy. With \(w\) copied,
the two-hop transfer sum is \(1+4-5=0\), and the **entire**
join slope through child size seven vanishes: at the first
possible size only successive unary lifts fit, so every affected
entry at that size has this same factor. The receivers can stay
unsplit. A possible slope at size eight at the join is irrelevant
because it is not active and no protected consumer uses that
child size. Consequently the exact minimum is five copies,
whereas the robust least cut has \(4+N\). The optional relay
is permitted to remain unsplit in the robust plan because its
incoming coefficient is \(5\); it improves the signed exact
plan by changing the cut's actual jet transfer. This is why
a source-side graph closure alone cannot promise signed
optimality.
