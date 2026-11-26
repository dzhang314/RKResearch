# Overlap-aware lower bounds from tight cuts and path-length ambiguity

Pure mathematics, no adjacency assumption or global improvement asserted. The previously proved delayed-cut ranks and ERK tight-cut transport are the only rank inputs. All graph walks below use the **actual** strict part of a triangular tableau, directed from a receiving row to its donor and starting at a b-active stage. Thus the graph is acyclic even if there are skip edges. Stages, not time-tagged copies, are counted.

## 1. Joint Beta support bound without disjoint feeding cones

Use a strict ERK tableau of literal order p over a field with the paid factorial units. Fix a synchronous separator S of exactly r stages at hop t along every d-step walk, with t>=1 and d+2r-1<=p. Put b_budget=p-d-r. The proven tight-cut transport gives distinct y_i=1-c_i for i in S and nonzero net prefix weights w_i. For each i, the signed weights b_l(A^t)_(l,i)/w_i on active clock labels eta_l=1-c_l have moments through b_budget
```
sum_l [b_l(A^t)_(l,i)/w_i] eta_l^j
       = y_i^j / binom(t+j,j).
```
This is a Beta(1,t) moment functional scaled by y_i; no actual weight positivity is assumed.

Take any nonempty I subset S. Let h=|I|, h'=#{i in I:y_i!=0}, and let L_I be the number of distinct active labels on **at least one** t-step path to I. This can be replaced by the smaller union of labels with nonzero net weight at at least one gate. It is a common pool; a label seen by many gates is counted only once. Then
```
L_I >= max(h, ceil(h' (b_budget+1)/(h'+1))).
```
The first inequality is the rank-h Vandermonde on y_i, after unit row factors, through j=h-1<=b_budget. Its actual factorization uses only the common L_I labels.

For the second, abbreviate L=L_I. If L>b_budget it is immediate. Otherwise let P be the monic annihilator of the L labels and v=b_budget-L. For each nonzero y_i and each k=0,...,v, the paid polynomial test (y_i-z)^k P(z) is zero on the shared actual support. In the reference Beta functional this is exactly
```
t y_i^k integral_0^1 (1-u)^(t+k-1) P(u y_i) du = 0.
```
By the polynomial beta identity, this is t(t+k-1)! y_i^(-t) times J^(t+k)P evaluated at y_i, where J is the zero-origin primitive. All scalar factors are units in the field, and no degree beyond t+b_budget<=p is used. Hence F=J^(t+v)P vanishes to multiplicity at least v+1 at each of the h' distinct nonzero y_i, since its derivatives through v are the earlier primitives. It also vanishes to multiplicity at least t+v at zero. Subtracting these multiplicities from degree(F)=L+t+v gives L>=h'(v+1), as claimed. If one gate has y_i=0 and L<=b_budget, that gate forces P(0)=0 and contributes an extra unit to the multiplicity at zero.

Thus a tightly synchronized gate family with many different nonzero clocks cannot all use a small shared pool: if h'>0 and a graph bounds L_I by L*, it imposes b_budget+1<=L*+floor(L*/h'). As h' grows this approaches the entire moment budget, rather than the half-budget from one local quadrature. Conversely, b_budget+1 arbitrary distinct labels can fit every column of this moment transcript by solving a separate Vandermonde system for its signed weights; this is a moment-only diagnostic, not a tableau. In particular do not add the local support quotas absent other structure.

## 2. Physical stage inequality at antichain gates

In the tight-cut setting let I be any nonempty **reachability antichain** within S (the whole S need not be an antichain). Keep h,L_I from above and put u=d-t. For u>0 define sigma as the maximum, over physical vertices strictly downstream of I in the backward support, of the number of feasible arrival times 1,...,u from I on u-step suffix walks. An arrival time is feasible only if the prefix extends to u steps. Then
```
physical stages >= h + max(t,L_I) + max(u+h-1, ceil(h u/sigma)).
```
When u=0 the last term is 0. The two maxima are needed; no assumption is made that the active source cones of distinct gates are disjoint.

Proof of disjointness of the *three regions*: any vertex on a strict prefix into I, including any feeding active start, lies above I and outside I. It cannot be strictly downstream of another gate in I, since composing those paths would make two gates comparable or yield a cycle. Thus the gates, counted upstream stages, and counted downstream stages are physically disjoint by the antichain hypothesis. Upstream there are at least L_I physical active indices, and one t-step prefix (w_i!=0) uses t stages before its gate; take their maximum rather than summing them.

The actual right cut factor has full row rank on the whole tight cut, so its h rows from I have rank h. Iterated Cauchy-Binet through the u strict factors chooses h paths from these gates that are vertex-distinct at every synchronized suffix time and terminate at h distinct endpoints. Select an endpoint not strictly reachable from any other endpoint in this finite endpoint set. Its path of length u contains none of the other endpoints (all outside I), proving at least u+h-1 downstream stages. The same h paths have h u downstream visits; one physical vertex contributes to at most sigma of these visits, because the chosen paths are distinct at a fixed time. This proves the ceiling bound without treating distinct times as distinct stages.

A nonzero-shift variant of the suffix count needs no Beta law: at a synchronous antichain cut of size q, a positive witnessed delayed two-bank rank r gives r such suffix paths from selected cut stages. Count q cut stages, one t-prefix, and at least max(u+r-1,ceil(r u/sigma)) downstream stages for u>0. Do not claim the ERK shared-pool quota for this variant.

**Explicit skip class.** If all chosen gates have a common integer potential g and every edge strictly increases g by at least one, suppose each relevant u-step suffix has total surplus sum(Delta g - 1)<=K. Any prefix reaching v has length in [g(v)-g(I)-K, g(v)-g(I)], hence sigma<=K+1. This permits arbitrary detours consistent with the budget. For example, at most J skipped edges per relevant suffix, each of span at most L_skip, gives K=J(L_skip-1). The lower bound can use ceil(h u/(K+1)); it is quadratic when h,u scale linearly with order and K is bounded, but those are architecture premises, not unrestricted conclusions.

## 3. Exposure bound for all supported lengths, even without an antichain

Let E_d be the physical set of endpoints of strict d-step walks from active support, and choose any covered length range with paid rank quotas r_d. The two-bank endpoint case t=d gives, for a nonzero common diagonal over a paid field, r_d=min(floor(p/2),floor(2(p-d)/3)), with the ordinary r_0=ceil(p/2) at zero steps; the audited Haar/square gates give the corresponding strengthened quotas when available. For strict ERK, r_d=floor((p-d+1)/2) for 0<=d<=p-1. All are cardinality lower bounds on E_d.

Each vertex v is counted at most kappa(v)=#{d:v in E_d}. Therefore
```
sum_d r_d <= sum_v kappa(v),   hence s >= ceil(sum_d r_d / max_v kappa(v))
```
when the right-hand denominator is positive. More generally choose nonnegative weights on the paid lengths whose total incident weight at each physical vertex is at most 1; the weighted rank sum is a physical stage lower bound. This is an overlap accounting inequality, not a claim of distinct stages at different lengths.

A second explicit class allows b-support anywhere in a potential strip of width W and skip edges anywhere: g increases by at least one and each relevant active-start walk has total surplus <=K. Then every feasible d at vertex v lies in [g(v)-g_min-W-K, g(v)-g_min], so kappa(v)<=W+K+1. In particular the ERK sum is floor((p+1)^2/4), giving the exact conditional floor ceil(floor((p+1)^2/4)/(W+K+1)). This is a bounded **total** skip surplus assumption, not merely a bound on individual hop size. When combining it with the antichain result, take the maximum of the bounds unless a separate overlap certificate permits adding credits.
