# Bounded-skip physical support windows and exact scalar packing

## Assumptions and rank input

Let (A,b) have literal order p>=1 over a nontrivial commutative ring, with every physical diagonal entry equal to gamma. Put B=A-gamma I and c=A 1. Number the physical levels backwards from the terminal output level by d=0,...,D, and let w_d count their stages. Assume b is supported on d=0 and each nonzero B(i,j) has 1<=d(j)-d(i)<=L, where L>=1. Empty levels are allowed below the terminal in the inequalities. We do not replace B by a clock commutator; strict same-clock edges are allowed.

Use the [beta-Hankel rank theorem](QUADRATIC-ADJACENT-LAYER-WIDTH.md) for the actual matrix
```
M^(h)_(k,a) = b · ((1−c)^k ⊙ B^h c^a) / (k!a!).
```
At h=0 it has rank at least r_0=floor((p+1)/2) in every residue field. For 1<=h<=H=max(0,p-2) the (r_h+1)-by-r_h block has full column rank, where r_h=floor((p-h)/2), by the paid budget h+2r_h<=p. If gamma=0 instead take H=p-1 and r_h=floor((p-h+1)/2), using the paid square block. The order assumption makes every 1,...,p a unit, as required by that theorem. The scope here is only transfer from these ranks to physical stage counts; the contact proof is not repeated.

## Exact structural cut windows

Fix 1<=t<=h<=H. Factor B^h=B^t B^(h-t) in the measured matrix. A cut index j can contribute only if there is a t-edge strict path to j from terminal support and a continuation of h-t strict edges. The first t edges imply t<=d(j)<=Lt; the last h-t edges imply d(j)+h-t<=D. Therefore the rank-r_h factorization passes through the physical indices in
```
I_(h,t) = [ t, min(Lt,t+D-h) ] intersect the integers,
sum_(d in I_(h,t)) w_d >= r_h.
```
A window need not be filled or reachable in a particular graph. It is the sharp enclosure from the stated hop and depth constraints alone: every enclosed depth can be obtained by summing t integers in [1,L] and then continuing by h-t unit hops in the full allowed graph. The restriction argument works over R, and rank is tested in any one of its residue fields. At t=h one can additionally group by the reduced start clock because the right factor is c^a/a!. At intermediate cuts only the physical stage count is asserted, not separation by that cut clock. At h=0 all rank is on d=0, so w_0>=r_0.

In particular D>=H: at h=H, the nonzero measured output contains a nonzero term along an H-edge physical B path from terminal support. The path has H distinct nonterminal depths.

## Exact no-double-counting inequality

For any finite family of integer intervals I=[a,b] within depths 1,...,D, impose nonnegative integer widths and scalar demands w(I)>=q_I. Their exact minimum possible nonterminal width sum is
```
max { sum_(I in C) q_I : C consists of pairwise disjoint intervals }.
```
The lower bound is direct summation. For the converse let P_j be the maximum packed demand from intervals ending at or before j, with P_0=0. The P_j are nondecreasing integers; an optimal packing at a-1 can be extended by [a,b], so P_b>=P_(a-1)+q_[a,b]. Thus widths w_j=P_j-P_(j-1) satisfy every demand and sum to P_D. Equivalently the prefixes are longest weighted paths on vertices 0,...,D, with weight q_[a,b] edge a-1 to b and zero edges j-1 to j. Take q_(I_(h,t))=r_h to incorporate all synchronized cuts; if demands share an interval, retain the largest. This optimum is for scalar interval inequalities, not a converse construction of an RK tableau.

If a baseline occupancy u_d is known, replace each demand by max(0,q_I-sum_(d in I)u_d) and add sum u_d back. This is exact for these scalar constraints with w_d>=u_d. Examples include all nonempty levels (u_d=1) or the occupied depths of an identified physical chain (u_d=0 or 1). The terminal count r_0 is added only once, separately.

## Closed width bound from endpoint windows, independent of D

The endpoint windows are W_h=[h,min(Lh,D)], 1<=h<=H. Their demands r_h decrease weakly in h. Set
```
h_1=1,    h_(j+1)=L h_j+1,
J=max{j : h_j<=H}, with J=0 if H=0.
```
Consecutive chosen windows are disjoint; later h cannot occur after a cap truncates the previous window at D, since H<=D. Thus
```
s >= r_0 + sum_(j=1)^J r_(h_j).
```
This is exactly the consequence of the endpoint scalar inequalities alone. Place r_(h_j) units of width at d_j=min(L h_j,D) and zero at other nonterminal depths. Every h between h_j and the next start (or through H for the last block) satisfies h<=d_j<=Lh, and r_h<=r_(h_j), hence its window demand is met. Equivalently, greedily choosing the earliest h in every disjoint interval packing is optimal for the nonincreasing demands. For all synchronized cuts combined, the same optimum remains attainable in the abstract scalar model if D>=L H: then I_(h,t)=W_t and r_h<=r_t.

For L=1, h_j=j, yielding exactly the adjacent quadratic width bound. For fixed L>=2,
```
h_j=(L^j-1)/(L-1),
J=floor(log_L(1+(L-1)H)),
r_0+sum_(j=1)^J r_(h_j)=(p/2) log_L p+O_L(p).
```
Here sum_j h_j<=L H/(L-1), so the asymptotic statement is about the lower-bound expression, not attainability or the actual stage asymptotics. When L is large the exact finite formula is the useful version.

## Retain the actual long path without double counting

Even when the H-edge physical chain C is known only to exist and its depths are not specified, pairwise disjoint intervals I_j with demands q_j give the bound
```
s >= r_0 + sum_j q_j + max(0,H-sum_j min(q_j,|I_j|)).
```
Indeed, the H nonterminal chain stages have distinct depths. Only min(q_j,|I_j|) can be charged to the q_j credited stages of an interval, and total overlap cannot exceed H. Take the union of a chosen q_j-stage subset of each interval, the chain, and the separately counted terminal stages. With no intervals this gives s>=r_0+H, of size about 3p/2, even when skips are unbounded but the terminal-only hypothesis remains. For L=1 the singleton capacity sum for the chosen adjacent windows equals H, so no already-counted stage is added.

The bounds are specific to actual bounded-skip levels and terminal-supported output. The exact scalar converse supplies no approximation of beta values and no RK order construction. A fixed physical cut crossed at different hop times was not treated as a single rank factor: the valid rank factor above is a synchronized cut with its exact window.

The [rank-only construction](RANK-ONLY-DIAGNOSTIC.md) shows why fitting
these ranks is weaker than satisfying the paid order equations.
