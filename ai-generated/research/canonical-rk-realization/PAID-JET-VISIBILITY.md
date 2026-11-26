# What finite RK order can see of the actual strict graph

**Scope.** Pure mathematics, no inferred unstructured stage floor. The statement distinguishes paid stage data from raw support, and does not use the full-series context-rank result. A length-ambiguity counterexample remains after ordinary reachability pruning and with distinct clocks; it does not exclude more powerful finite-order algebraic compression.

## 1. Exact row-fibre criterion and paid coordinate selectors

On a fixed physical stage set, write Phi_A(tau) for the vector of elementary stage weights of a rooted tree: leaf weight 1, and at each root the componentwise product of A applied to the children's weights. Fix p>=2. The full finite stage jet is the collection for |tau|<=p, stronger information than the scalar paid RKOC alone. Put
```
V_(p-1)(A) = span { Phi_A(tau) : |tau|<=p-1 }.
```
For any A', equality of their entire finite stage jets through p is equivalent to
```
(A'-A) V_(p-1)(A) = 0.
```
Necessity: for each |tau|<=p-1 the unary lift has stage weight A Phi_A(tau), and it too is paid. Sufficiency: induct on tree size. The child vectors agree; their A and A' images agree by the annihilator hypothesis, so their componentwise products agree. This proof works over a commutative ring using the generated submodule. In particular c=A1 is unchanged, and if b is kept fixed, so are all paid scalar outputs.

Over a field, fix a strict chronological prefix P_i of allowable donor coordinates of row i, and keep the physical diagonal gamma fixed. The available changes of that row preserving the finite jet are exactly the annihilator of the restriction W_i=V_(p-1)(A)|_(P_i). Hence the entry at j in P_i is rigid on the finite-jet fibre precisely if the coordinate vector e_j belongs to W_i:
- If e_j=sum a_tau Phi_A(tau)|_(P_i), the entry is the paid linear combination sum a_tau [Phi_A([tau])_i - gamma Phi_A(tau)_i]. Here [tau] is the unary lift.
- Otherwise a row in W_i^perp has nonzero j-th coordinate. A multiple changes the entry to any prescribed field value without changing the finite jet. Over an infinite field all mutable entries of one row can be made nonzero at once, by avoiding finitely many proper affine hyperplanes; rows can be changed independently.

This is an exact **paid projector criterion**, not a claim that the order equations force all such projectors. A simple sufficient case is at most p-1 distinct clock labels on P_i: the clock-fibre selectors are Lagrange polynomials in c of degree at most p-2, hence combinations of paid bushes. Then total row coefficient into each fibre is rigid; if its clock labels are distinct this reads each strict entry. With more information one may similarly prune a zero-output stage whose size<=p-1 response row is a linear combination of earlier ones by redirecting each later donor use. Such a reduction is different from inferring the raw graph. Full-series indicator expansions are not automatically paid here.

## 2. Same finite jet, sharply different path-length ambiguity

Work over an infinite field and let p>=4. Start from an adjacent common-diagonal tableau with physical rounds h=0,...,D=p-1, a single initial stage at h=0, terminal-only output, and an actual b-active strict path of length D. Assume round 1 has w<=p stages with pairwise distinct clocks. Keep the existing coefficients and add p-w new sites in that round to make p distinct clock sites x_1,...,x_p; the new sites choose fresh clocks, distinct from all old ones. Their only strict donor is the initial stage, with entry x_i-gamma, and they have the same physical diagonal gamma. Initially no old row uses the new sites. This collocation-free step is just enlargement inside round 1. The original rows of round 1 are also of this form, since they have only that initial donor.

The initial stage's response to tau is gamma^(|tau|-1). For a round-1 site of clock x, its stage response is a polynomial R_tau(x): for each child eta multiply its factor
```
(x-gamma) gamma^(|eta|-1) + gamma R_eta(x),
```
starting with R_leaf=1. Induction gives degree R_tau<=|tau|-1, uniformly across every site in the enlarged round. In particular these responses for |tau|<=p-1 have degree <=p-2. This works for zero and nonzero gamma.

Use the barycentric row w_j=1/prod_(k!=j)(x_j-x_k) on this reservoir. Its entries are all nonzero. Taking the leading coefficient in Lagrange interpolation on the p sites gives
```
sum_j w_j f(x_j)=0        if deg f<=p-2,
sum_j w_j x_j^(p-1)=1.
```
Thus adding any multiple of this row to the strict reservoir columns of any later receiver leaves c and every individual stage response through p unchanged by Section 1. Choose nonzero multiples generically to keep every previously nonzero entry in that block and make all reservoir entries nonzero. Only finitely many scalar choices are excluded, one per such entry.

Make two tableaux on this **same physical stage set**:
1. In both, make the reservoir live by adding these multiples from the receivers in round 2 only. The first tableau is still adjacent, and all its reservoir sites are reached via the already existing depth spine. Its only active-to-reservoir strict walk length is D-1.
2. In the second, also add one such null multiple from every later round h>=3 to the reservoir. These are the only new skip edges. No strict walk can take more than one: once it is in round 1 it can only proceed to round 0. Retain the old D-step spine. For any k=1,...,D-1, follow k-1 of its original adjacent edges and then take the nonzero edge into a chosen reservoir site from round D-k+1. Thus each such site has all distinct feasible lengths 1,...,p-2.

The two tableaux now have identical b and c, and identical full stage jets through p. Every new stage has an actual strict route to terminal support and its own clock, so dead-stage pruning and clock twins do not account for this difference. If all prototype sites were live they remain live. Both have the old depth p-1, and if exact order p was witnessed by the first unpaid bush, it remains exact since c,b are unchanged. The difference is already visible in the first unpaid stage expression A c^(p-1), of tree size p+1: at a newly modified later row it changes by its nonzero multiplier, by the barycentric equality at degree p-1. This is consistent with the stronger visibility of full-series filtered context probes.

## 3. Standalone supply of prototypes and consequence

For an explicit prototype at any prescribed real-algebraic common gamma, choose h+1 distinct rational nodes in each positive round h=1,...,p-2 and p distinct rational terminal nodes greater than 1. The single initial node is gamma. For adjacent rows, apply J=I_0-gamma to the previous round's cardinal polynomials and evaluate at the receiving sites, then put gamma on the physical diagonal. Choose the nodes sequentially to avoid previous clocks and the finitely many zeros of these cardinal primitives; each is nonzero since J raises leading degree by one. Hence all adjacent entries are nonzero. Their strict sums are J1(x)=x-gamma, so the clocks are exactly the chosen nodes. In the terminal round use the integrals of the terminal cardinal polynomials as weights. Each is nonzero because its numerator has constant nonzero sign on [0,1] (all terminal nodes are >1).

The stage grade of a tree τ is |τ|−1. For stage grade <=h at round h, the actual response equals the exact I_0 model at the nodes: induct on the tree size. The children have grade <=h-1, and their exact polynomial values are available at both h and h-1. The previous h nodes interpolate them exactly, and adding the same-row gamma term to J restores I_0. The leaf case includes the initial round. Thus terminal quadrature through degree p-1 gives literal order p. Its monic node polynomial has degree p and nonzero integral while vanishing on every terminal node; after lower-degree exactness this makes the first unpaid bush fail. All sites are live and globally distinct in clock. The prototype count is p(p+1)/2, and the enlargement adds p-2. Alternatively, starting with one of the verified adjacent matched-width prototypes with single round-1 site, the same proof adds only p-1 stages.

Consequently even the full paid stage jet does not determine the raw path-length spectrum or force a p-independent bound on its ambiguity: the two graphs differ from one versus p-2 arrival lengths at the same live, distinct-clock stages, although every path uses at most one newly permitted skip. For any grading that increases by at least one on each edge, all the exhibited lengths use the same endpoints, so their additive skip surpluses differ by p-3. The largest surplus is therefore at least p-3, regardless of the choice of grading. The result neither proves nor refutes such structure after admissible algebraic compression, or at a genuine unrestricted stage minimum. A proof using raw graph separation needs either directly paid coordinate/quotient witnesses, or an additional reduction premise; finite RKOC alone do not identify these raw edges.
