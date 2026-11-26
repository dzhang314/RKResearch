# Paid beta-Hankel rank and timed support cuts

## Scope

Let R be a nontrivial commutative ring with identity. Let (A,b) have literal rooted-tree order p>=1 and c=A1. Set B=A-gamma I, where gamma is a scalar. The paid moment calculation works for any such scalar shift. To interpret B as the **physical off-diagonal** support, assume every physical diagonal entry of A is gamma. An edge i -> j means B_ij != 0; it points from a receiving row to a donor. The support may be cyclic. We use walks of prescribed length; for an acyclic DIRK support they are paths, but different paths can still visit the same physical stage at different hops.

No sign, ordered-field, domain, or characteristic-zero hypothesis is used for the lower bound. The example in Section 4 only concerns rank, not order.

## 1. Paid rank input, with exact indices

Literal tall order gives $n!(\mathbf b\cdot A^{n-1}\mathbf1)=1$ for 1<=n<=p, so 1,...,p are units. Every residue field has characteristic zero or greater than p. Define the actual normalized probe
```
M^(h)_(k,a) = b · ((1−c)^k ⊙ B^h c^a) / (k! a!).
```
Powers on c are componentwise. The maximum literal order is h+k+a+1. Expand into stage forests, with c of grade one, A adding one, and componentwise multiplication adding grades. Taking the inner product with the output weights adds one to the forest degree. Literal order evaluates these terms by c -> X, A -> J, and the output readout -> I, where J X^j=X^(j+1)/(j+1) and I X^j=1/(j+1). The factor for each J is exactly the size of the attached subtree. Thus B becomes J-gamma. The formal beta identity I[(1-X)^k X^j]=k!j!/(k+j+1)! follows from I(U')=U(1)-U(0) and induction on k. Under the indicated payment,
```
M^(h)_(k,a) = u_(k+a+1),
u_d=sum_(ell=0)^h binom(h,ell)(-gamma)^(h-ell)/(d+ell)!
   =[z^(h+d)] (1-gamma z)^h E_m(z),    E_m(z)=sum_(j=0)^m z^j/j!,
```
for every h+d<=m<=p. No factorial index above the paid order is needed.

For h>=1 and r>=1, take k=0,...,r and a=0,...,r-1. At p>=m=h+2r this matrix has rank r over **every** residue field. Indeed, a nonzero column kernel (v_a) in such a field gives
```
Q=sum_(a=0)^(r-1) v_a z^(r-1-a),
g=1-gamma z,  W=g^h Q.
```
The coefficients h+r,...,m of E_m W vanish. Its truncation P through h+r-1 is nonzero, since the initial term of Q survives, and P=E_m W modulo z^(m+1). Define U=gQ and V=gQ'+h g'Q, so UW'=VW and deg V<deg U (or V=0). The polynomial U(P'-P)-VP is nonzero by its leading term -UP and has degree at most (r-1+1)+(h+r-1)=m-1. But it is zero modulo z^m: substitute E_m W using the congruence and use E_m'-E_m=-z^m/m!. This is a contradiction. In particular, gamma need not be inverted in R or its residue field.

If h=0, or if gamma=0, the square k,a=0,...,r-1 suffices at p>=h+2r-1. Its entries are 1/(h+k+a+1)!. Multiplying row k by (h+k+r)! yields in column a a monic polynomial in k of degree r-a-1, so its determinant is a signed Vandermonde in 0,...,r-1 times paid factorial units. The square determinant is itself a unit in R.

## 2. Timed cuts: factorization over R, path witnesses over residue fields

Form the hop-expanded graph with vertices (t,i) for 0<=t<=h, and edges (t,i)->(t+1,j) of weight B_ij for each nonzero B_ij. The sources at t=0 are the active stages b_i != 0; all stages at t=h are possible endpoints.

One may also add two disjoint sets of boundary vertices for start and end clock labels. The start node with label xi feeds (0,i) of that clock with edge weight b_i when b_i!=0. Each (h,j) feeds its end label c_j with weight 1. The external start and end probes at a boundary label are (1-xi)^k/k! and xi^a/a!, respectively. The resulting weighted path sum is exactly M^(h). Boundary nodes are optional; even at h=0, start and end copies are distinct.

**Cut factorization.** If a set C of timed vertices and optional boundary nodes meets every eligible walk, the full matrix M^(h) factors through |C| coordinates **over the original ring**. For x in C, sum all prefixes from the start to x with no earlier cut visit, including their start probes and edge weights, into the column indexed by x. Sum all suffixes from x to an endpoint, including their edge weights and end probes, into the corresponding row. Each complete walk occurs once, split at its first cut visit. Conversely, each such prefix/suffix pair concatenates to an eligible walk first hitting C at x. Multiplying these two matrices gives M^(h). Every argument here is a finite sum/product identity; the factorization itself even works over a semiring given weighted probes. Zero divisors and cancellation do not affect it.

In particular rank over any residue field is at most |C|. One can instead reduce A,b first, rebuild the graph and clock groups there, and apply the same bound in that field: reduction can delete edges or active stages and merge clock labels. If the original-ring graph was used, its factorization simply reduces; it does not require distinct original clocks to remain distinct modulo each maximal ideal.

**Path extraction.** Conversely to the *rank bound*, not to numerical sufficiency of topology, a nonzero r-by-r minor in a residue field gives r walks with distinct vertices at every fixed hop and with pairwise distinct start clocks and pairwise distinct end clocks in that field. For this, factor the actual matrix through the start-label matrix, the entry grouping by active stages, the h copies of B, the exit grouping by clock, and the end-label matrix. Iterated Cauchy-Binet selects one nonzero product of minors through r distinct indices at each factor. A nonzero term of each transition determinant supplies a matching between its two selected index sets. Concatenate those matchings. The endpoint groups enforce the two clock distinctions. These walks lift as walks in the original support because every used b_i and B_ij remains nonzero after reduction. Distinctions in the field imply distinctions in R. A physical stage may nevertheless be used by different walks at different hop numbers. This conclusion does not assert that the existence of such walks ensures numerical rank.

If q is any such cut capacity, common-diagonal order must satisfy p<=h+2q+1 for h>=1. Indeed, otherwise the paid rank with r=q+1 contradicts the cut factorization. When gamma=0 this improves to p<=h+2q. At h=0 the bound is p<=2q for either case.

## 3. Physical gates with variable arrival times and clock-labeled bypasses

Given an ordinary set S of physical stages, for each i in S let T_i(h) be the set of t such that an active-start prefix of length t first meets S at i, and a suffix of length h-t from i exists. Time zero is included if applicable. Suffixes may visit S again. For the h-walks entirely avoiding S let e_in and e_out be their numbers of distinct start and end clock labels, taken to be zero when there are no bypasses. A valid cut has capacity
```
q_h = sum_(i in S) |T_i(h)| + min(e_in,e_out).
```
Use the timed first-hit vertices for walks that hit S, and all the bypass labels on the cheaper side for walks that avoid it. These are capacities in the same graph, original or reduced, whose rank is being bounded. They are not counts of physical stages alone. For a mandatory gate there is no bypass term. If a gate vertex has maximum suffix length d_i, then t>=h-d_i and its contribution is at most min(h+1,d_i+1); if every first hit has the same hop, its contribution is at most one.

As one consequence, suppose S is inactive and every active-start walk that avoids S has length at most d. At h=d+1 the gate is mandatory and each first hit has 1<=t<=d+1. Thus
```
p <= d+2+2(d+1)|S|
```
in the common-diagonal case, with one saved when gamma=0. The exterior could have arbitrarily many stages and the core may contain cycles. Exact arrival sets or short suffix depth can improve this crude capacity.

## 4. Rank-only sharpness of variable timing

For any r>=1 choose h>r. Take r active leaves s_1,...,s_r with private directed arms of lengths 1,...,r to a single gate v, and a common tail v=u_0 -> u_1 -> ... -> u_h. The underlying undirected graph is a tree, the active leaves are an antichain, and deleting one physical vertex v separates all these h-walks from their endpoints. Their first-hit times at v are exactly 1,...,r. The unique h-walk from s_j ends at u_(h-j).

Work over the rationals with gamma=0. Give every nonlast vertex one outgoing B entry, pairwise distinct rational weights greater than 1. Take b_(s_j)=1/r and all other weights zero. The actual c=A1 at a nonlast vertex is its outgoing weight, so the start clocks and endpoint clocks are each pairwise distinct. If pi_j is the nonzero product along the unique walk, the r-by-r probe square at k,a=0,...,r-1 factors as
```
[(1-c_(s_j))^k/k!]_(k,j)
  diag(b_(s_j) pi_j)
[c_(u_(h-j))^a/a!]_(j,a).
```
Both outer matrices are nonsingular Vandermondes up to unit factors. The rank is r; the one physical gate has exactly r needed timed copies. This example is acyclic and can be numbered as a strict triangular tableau. It deliberately fails second-order RK order, since $\mathbf b\cdot\mathbf c>1$ instead of 1/2. It proves that ordinary separator size or ordinary tree topology cannot replace the timed capacity **from ranks alone**. It neither fits the paid beta values nor asserts any high-order method or general stage-count lower bound.
