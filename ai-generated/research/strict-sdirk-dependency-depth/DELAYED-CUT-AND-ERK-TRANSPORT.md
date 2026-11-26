# Delayed paid-word cut rank and saturated ERK cut transport

**Scope:** pure mathematics on the actual strict support with arbitrary skips. No adjacent-layer or terminal-only-output hypothesis. Neither part implies an unrestricted extra physical-stage floor: timed gate copies need not be distinct stages. The scalar inputs are the rectangular shifted factorial rank and the negative-diagonal Haar argument from the [matched-width proof](UNIFIED-MATCHED-WIDTH.md).

Let c=A1, B=A-gamma I with an actual common physical diagonal gamma, and Y=diag(1-c). Draw i -> j when B_ij != 0 (from receiving stage to donor) and start walks at b-active stages. True SDIRK/ERK support is acyclic in this orientation, but below only the indicated finite walk length matters. Assume literal order p, giving units 1,...,p from the tall factorial tests. Let I_0 denote the zero-origin polynomial primitive and ell integration over [0,1], interpreted as paid polynomial coefficients. The formal shifted operator is J=I_0-gamma; in y=1-X coordinates its adjoint is T=V-gamma, V the primitive in y.

## 1. Two banks with a delayed separator: stronger nonzero-shift rank

Fix d>=t>=0 and a timed separator C all of whose vertices are (q,i) with q>=t, meeting every d-step walk from active support. The cut can be synchronous or not. Use just these two row banks, each on c^a/a!, 0<=a<r:
```
b^T Y^j B^d,          b^T B^t Y^j B^(d-t),        0<=j<=b_budget.
```
They are paid at d+b_budget+r<=p: Y expands into leaf multiplications, B into A or a diagonal scalar, and b^T pays the output root. In every actual term the multiplier is at time 0 or t, and hence all its factors lie weakly before the first hit in C. Attach a multiplier exactly at the cut to the prefix. Splitting each walk at its first hit therefore factors the whole two-bank matrix through |C| coordinates, with the pure suffix B^(d-q)(c^a/a!) independent of the row choice. This is a finite product/sum identity over the original ring with no path cancellations assumed.

After formal adjunction the bank tests are T^(d-t) times the two families T^t M^j1 and M^j T^t1, M multiplication by y. For gamma!=0 their exact span for j<=b_budget is
```
T^m Poly_(<=nu),    m=d-min(t,b_budget),    nu=b_budget+min(t,b_budget).
```
Proof: in the factorial basis T is multiplication by z-gamma and M is z+z^2 derivative. At budget j, the degree is at most t+j and the (z-gamma)-valuation is at least max(t-j,0). Induct on j inside the first t operators. The top bank T^t M^j1=j! z^j(z-gamma)^t supplies the one newly possible highest degree. For j<=t, M^j T^t1 also has exactly the newly possible lowest valuation t-j: each application at positive valuation lowers by one with leading multiplier gamma^2 times that valuation. These two are independent modulo the earlier span. Beyond j=t only the degree increases. This uses only nonzero gamma and paid factorials over a field, not a sign.

Choose b_budget=p-d-r, and put s=p-d>=1. If nu>=r, use tests T^m(y^j/j!), 0<=j<=r. Pairing them against X^a/a! gives the shifted factorial Hankel with exponent m. The audited rectangle is paid because m+2r<=m+nu+r=d+b_budget+r<=p. Thus the timed cut must satisfy
```
|C| >= min(floor((s+t)/2), floor(2s/3))          (gamma!=0).
```
Indeed r<=b_budget+min(t,b_budget) is exactly 2r<=s+t and 3r<=2s. If the square in this test family is known nonsingular, e.g. the audited negative real diagonal Haar proof, one may use nu+1>=r instead and obtain
```
|C| >= min(floor((s+t+1)/2), floor((2s+1)/3)).
```
For t=0 and d>0 the first bound recovers the earlier rectangular endpoint bound; when t>=floor(s/3) it reaches floor(2s/3), a genuinely stronger obstruction to late narrow funnels. A physical gate S whose first hits are all at or after t must be charged by the number of its feasible hop-tagged copies, not just |S|; if synchronized at t, the number of feasible copies is at most |S|, and equals |S| only if each gate is used. Over a paid commutative ring the sign-free nonzero-shift bound holds when gamma is not nilpotent, by localizing at gamma and taking a residue field. The graph can shrink in this base change, but the original separator still cuts all remaining walks.

For gamma=0 these two ideal banks instead span V^d Poly_(<=b_budget). They give the ordinary rank floor((s+1)/2) by the unit reciprocal-factorial square. There is no late cut rank gain from that span alone; the next result uses their proportionality rather than their dimension.

## 2. ERK: local signed Beta quadratures at a tight cut

Now gamma=0, so B=A. Let S be a synchronous separator at hop t among d-step walks, with q=|S|, and fix r>=1 with d+2r-1<=p. Put b_budget=p-d-r (so b_budget>=r-1). For i in S let
```
y_i=1-c_i,
U_j(i)=sum_l b_l y_l^j (A^t)_(l,i),    w_i=U_0(i),
R(i,a)=(A^(d-t)c^a)_i,                0<=a<r.
```
These are actual cut factors. All d-walks are cut at hop t, so localization to S is exact regardless of other active weights or skipped edges. The first r top rows against the r columns have targets j!a!/(d+j+a+1)!, and are invertible: after factorial rescaling, multiply row j by (d+j+r)! and obtain reversed-degree monic polynomial evaluations at j=0,...,r-1. Thus R has column rank r.

For every j<=b_budget, compare the checkpoint row to the top row on these columns. Their formal adjoints are, respectively, (t+j)! y^(d+j)/(t!(d+j)!) and j! y^(d+j)/(d+j)!. Therefore the actual row defect
```
Delta_j(i)=w_i y_i^j-binom(t+j,j) U_j(i)
```
annihilates R. All these pairings pay at d+j+a+1<=p. In particular, over a field,
```
rank(Delta_rows) <= q-r.
```
This linear constraint can be tested even when a cut is not tight. It does not equate the actual rows unless the cut factor is injective in this direction.

When q=r the two actual square cut factors are invertible (over the paid commutative ring as well, since their product determinant is a unit), so Delta_j=0 for every paid j. Thus
```
U_j(i)=w_i y_i^j / binom(t+j,j).
```
The first r of these rows are a Vandermonde on the actual y_i with column weights w_i and row unit factors. Consequently every w_i is nonzero and the y_i are pairwise distinct over a field (indeed w_i and all clock differences are units over the paid ring).

Assume t>=1. At any cut stage i with y_i!=0 over the field, group the signed net weights b_l(A^t)_(l,i) by the actual active clock labels, divide them by w_i, and scale each label to u_l=y_l/y_i. Their moments through b_budget are
```
sum_l (b_l(A^t)_(l,i)/w_i) u_l^j
    = 1/binom(t+j,j)
    = integral_0^1 u^j t(1-u)^(t-1) du.
```
The last equality is the formal Beta(1,t) coefficient identity. This does not require positive actual weights, or that the scaled labels lie in [0,1].

A supported measure fitting these moments needs at least n=floor(b_budget/2)+1 distinct nonzero-mass labels. For a paid-field proof, pair u^a against (1-u)^j, a,j<n. The ideal matrix is t a! (t+j-1)!/(t+j+a)!. Rescale rows and columns, then multiply each row by (t+j+n-1)! to obtain reversed-degree monic polynomial evaluations. This is a unit factorial Vandermonde; largest index t+2n-2<=t+b_budget<=p. Actual pairing factors through the label support, proving the claimed quota. Each nonzero net mass requires an actual t-step route from an active stage of that clock. At most one tight-cut clock is 1; thus all the other cut stages force this separate ancestry quota. If their source cones are disjoint in physical active stages, the quotas count disjoint active indices. Without such a premise, the quotas can overlap. Even disjoint source cones need not be disjoint from other cut gates; no general additive stage bound follows.

The two conclusions are distinct: the nonzero-shift case raises rank at a delayed allowable cut; the ERK case keeps the ordinary rank but extracts an exact extra structural constraint at saturation, or a bounded defect rank near it.
