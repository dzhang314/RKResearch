# A smaller physical layered construction by erasing only paid scalar errors

This is a source proof of a construction, not a checked Lean result
or a stage minimum. It uses the same ordinary adjacent-layer tableau
shape as the [published finite-band unrolling](QUADRATIC-STAGE-BOUND.md). It does **not** use
smaller coordinate frames for the full reference columns. It pays
the scalar output without preserving those intermediate columns.

## Exact statement and count

Work over a characteristic-zero field K. Write I for the polynomial
primitive with zero constant, ℓ(f)=(If)(1), J=I−γ id, and fix integers
p≥2 and 1≤D≤p−1. Put L=p−D and s_h=L+h. Assume distinct terminal
clocks x_1,...,x_q in K, 1≤q≤p, with quadrature weights integrating
ℓ through degree p−1. Let

    λ_d(f) = ℓ(J^d f).

Assume the shifted exact-flow target is zero on every paid tree of
height greater than D. This is the same omitted-paid condition as
in the finite-band theorem; it is automatic for D=p−1, and for
D=p−2 it is exactly λ_{p−1}(1)=0. Heights count edges.

The following independent layer widths are feasible:

* r_0=1 and r_D=q. The former is a leaf-only layer; the latter
  uses the original clocks and weights unchanged.
* For 1≤h<D with 3≤s_h≤q, use r_h=s_h−1.
* If some 1≤h<D has s_h=2≤q, one may likewise use r_h=1 provided
  λ_{D−h}(1)≠0. Otherwise leave it unreduced.
* For all remaining 1≤h<D, use r_h=min(q,s_h).

Earlier output weights are zero. The strict part B has rows only
from the immediately preceding layer and A=B+γ I_stage. This is a
physical lower-triangular constant-diagonal tableau of order at
least p, with depth at most D. It has depth exactly D whenever
λ_D(1)≠0. It has order exactly p if the terminal quadrature misses
the degree-p moment, or if λ_p(1)≠0. A next-order tall witness is
valid because T_p is taller than D and all smaller trees are paid.

Here is a closed count. With [u]_+=max(0,u), set
m=min(D,[q−L−1]_+) and let e_2 be 1 precisely when L=1, D≥2, q≥2
and λ_{D−1}(1)≠0; otherwise e_2=0. The number of stages is

    1 + mL + m(m+1)/2 + (D−m)q
      − [min(D−1,q−L) − max(1,3−L) + 1]_+ − e_2.

For the customary 2≤q≤p−1, p≥3, the generic sharp-depth case
D=p−1 improves U(p,q)=qp−binom(q,2) by q−2+e_2. At the
exceptional sharp depth D=p−2 it improves U(p,q)−2 by q−2.
The formula covers empty improvement ranges. The separate
p=2,D=0 midpoint branch is unchanged and not an instance of this
D≥1 construction. The maximum fibre still has size q. These
are stage-count and early physical-fibre improvements, not a
smaller terminal support.

## The necessary split hulls can be chosen over K

At a reduced layer h put d=D−h and r=s_h−1. We need a monic
polynomial H_h of degree r with r distinct K roots such that

    λ_d(H_h) = 0.                                             (1)

There is no positivity or interval constraint on these early roots.
For r=1, take H_h=X−λ_d(X)/λ_d(1) when the denominator is nonzero.
For r≥2, the following elementary argument applies whenever
λ_d(1), λ_d(X) are not both zero.

Write R_u=∏_{i=1}^{r−1}(X−u_i), initially with free u. The
polynomials in u given by λ_d(R_u) and each
λ_d((X−u_i)R_u) are nonzero: on the repeated-value line u_j=t,
they specialize to λ_d((X−t)^{r−1}) and λ_d((X−t)^r);
both are nonzero as polynomials in t by the coefficients of
λ_d(1), λ_d(X) and characteristic zero. Multiply them and all
differences u_i−u_j. The product is a nonzero K-polynomial,
so it does not vanish on all of Q^{r−1} (induction on the
number of variables using the infinite subfield Q). Choose a
rational tuple avoiding its zero set and take

    z = λ_d(XR_u)/λ_d(R_u),           H_h=(X−z)R_u.

All points are in K, and z≠u_i by the collision polynomials.
The argument equally allows any infinite prescribed subset of Q
for each free variable. It does not control the location of z.

The nonzero premise holds for every γ in K. Indeed
X=J1+γ, so λ_d(X)=λ_{d+1}(1)+γλ_d(1). For γ=0 the constant
moment is 1/(d+1)!. Otherwise the binomial expansion of J^d gives

    λ_d(1)=(-γ)^d L_d^{(1)}(1/γ)/(d+1).

The adjacent-index recurrence
(d+1)L_{d+1}^{(1)}=(2d+2−x)L_d^{(1)}−(d+1)L_{d−1}^{(1)},
starting with L_0^{(1)}=1, excludes a common zero of successive
polynomials by descending induction. In particular λ_d(1) and
λ_{d+1}(1) cannot both vanish. When r=1 and λ_d(1)=0 no monic
linear H can satisfy (1), since then λ_d(X)≠0. This is an exact
boundary for this local cancellation recipe, not a no-tableau result.

For all unreduced h with s_h≤q choose any s_h terminal nodes.
For all unreduced h with s_h≥q take the original q terminal
nodes. The alternatives coincide at equality when that cut is
not reduced. Take any one dummy clock at h=0, for example 0:
the initial physical clock is γ, not this label.

## Actual rows and proof that every paid tree is preserved

For each layer h let ρ_h be Lagrange interpolation on its own
nodes, acting on polynomials by evaluation then interpolation.
It is the polynomial remainder by the monic hull H_h: agreement
at the distinct points proves divisibility of the difference,
and the representative has degree below r_h. In particular it
never increases polynomial degree and fixes constants at every
layer, including h=0. For x_{h,i} a receiving node, and L_{h−1,j}
the actual cardinal on the preceding layer, use the explicit row

    B_(h,i),(h−1,j) = (J L_(h−1,j))(x_(h,i))

and zero everywhere else. In particular B1=x_{h,i}−γ for h≥1
and B1=0 at h=0; hence A1 uses exactly the claimed physical
clocks, including at the final layer. Since q≤p, the supplied
weights equal the terminal cardinal integrals: test the paid
law on each cardinal, of degree q−1. Thus the readout of the
terminal interpolant is ordinary ℓ.

Fix a tree t with order |t|≤p and height ≤D. Place it at the
terminal layer and assign each vertex v at edge distance d
below the root to layer h=D−d. The stage column at a vertex
is represented by the polynomial obtained as follows:
multiply J applied to each child's interpolated polynomial,
and interpolate the product at the current layer. A leaf uses
the empty product 1. This recursion is the literal RK stage
recursion for the displayed B: at each child layer its
interpolant is the unique sum of the cardinal polynomials with
coefficients the actual child stage entries. Thus the final
scalar is ℓ of the interpolant at the root. If a vertex lies
at h=0 it must be a leaf, since height≤D.

Remove interpolations one vertex at a time in ancestor-first
order, starting at the root. Throughout this process every
polynomial attached to a subtree of n vertices has degree
≤n−1: J raises degree by at most one, multiplication adds
bounds, and both interpolation and the identity are
degree-nonincreasing. The same bound applies to the raw
product F at the current vertex before reduction.

Consider one removal at a subtree of size n, lying d edges from
the root. All strict ancestors have already been changed to the
identity. Every sibling factor stays fixed in this comparison,
regardless of which of its own interpolations have been removed.
The change of scalar is therefore exactly

    ℓ(W (ρ_h F − F))

for a polynomial W of degree at most d plus the total sizes
of the sibling subtrees along the ancestor path, hence at most
|t|−n. To see this, begin at the root with test 1. At each
ancestor multiply the current test by the product of the factors
of the siblings of the path child, then apply

    J* V = ℓ(V) − IV − γ V,

using ℓ(V J Z)=ℓ((J* V) Z). The identity follows by integrating
the derivative of (IV)(IZ); J* increases the degree bound by
at most one. This computation is linear only in the single
polynomial being changed, which is all that telescoping needs.

There are four cases.

1. At h=0 the raw polynomial is 1. There is no error.
2. At an unreduced layer with full terminal nodes, the error
   is divisible by the terminal hull and vanishes at the q
   clocks. Multiplying by W preserves those zeros and has
   degree ≤(n−1)+(|t|−n)≤p−1. The supplied paid quadrature
   kills it, including at the root and at the first transition
   to the unreduced q-node region.
3. At any other unreduced layer, the number of nodes is s_h
   and n≤|t|−d≤p−d=s_h, so deg(F)<s_h and the error is zero.
4. At a reduced layer a nonzero error is divisible by H_h of
   degree s_h−1 and has degree ≤n−1≤s_h−1. Thus n=s_h and it
   is a scalar multiple of H_h. The equality n=p−d forces
   |t|=p and no sibling subtrees anywhere on the ancestor path.
   Consequently W=(J*)^d1 and the change is zero by (1).
   This is true even at the cut s_h=q.

This proves that **all the reductions can be performed together**
and that the full scalar equals the one with every interpolation
removed. No assumption that unchanged siblings agree with the
dense reference was made, and no unobserved column equality
was used. In the fully polynomial recursion, binomial expansion
over edges picking I or −γ id gives the shifted exact-flow
target on the literal tree: identity edge choices contract
those edges. Equivalently this is the standard diagonal-shift
formula applied to the formal polynomial model (I,ℓ).
For a taller tree the B-readout is zero by adjacent-layer
chronology. Apply the inverse diagonal shift: all paid tree
conditions are satisfied for A=B+γ I_stage, not just bush and
tall conditions. The shifted target on T_D detects sharp
depth via B^D1. At order p+1, a next tall discrepancy, if used,
survives shifting since contractions lower order. Otherwise
the stated degree-p quadrature failure is directly the physical
bush discrepancy, since final clocks and weights do not change.

## Comparison with full-column ranks and actual lower bounds

For the fixed dense split reference M=Ahat−γ I_stage on the q
terminal nodes, the earlier accepted coordinate frame construction
uses the full span of profiles with height≤h and order≤s_h.
For h≥1 this span has rank exactly min(q,s_h). The bushes
1,(x−γ),...,(x−γ)^{min(q,s_h)−1} are independent there.
When s_h≤q, integration of any lower-degree branch is exact on
the q-node reference, so the profile of a tree of order≤s_h
is an evaluated polynomial of degree≤s_h−1; this supplies the
matching upper bound. At h=0 the span is just the constant
column. Replacing bases, or compressing with a linear decoder
that must recover every full reference column, cannot beat those
ranks. The construction above is different: its errors need
only be zero under the paid scalar readout, not equal as columns.

For any adjacent-layer realization of order at least $p$ with
common diagonal $\gamma$ and weights supported on the terminal
layer, there is also a readout-only width bound.
For h≥1 let d=D−h and m_h=ceil(s_h/2). The m_h-square moment
minor for a,b=0,...,m_h−1, given by

    G_ab = λ_d((X−γ)^(a+b)),

has rank at most the width of layer h. In fact attach d unary
ancestors to a bush with a+b children. It is paid since
1+d+a+b≤p. Its shifted readout is the a+b moment at layer h
with effective weights given by $((B^d)^\top\mathbf b)_i$ at each stage $i$ of that layer. This factors G through
the evaluations of powers of the actual B1 values at that layer.
Replacing the powers (X−γ)^a with X^a is a unit triangular
basis change. The resulting determinant is a polynomial in γ
of degree exactly d m_h: its leading coefficient is, up to
sign, the nonsingular rational Hilbert determinant. Its value
at γ=0 is also nonzero, by the definite form
∫_0^1 (1−x)^d P(x)^2 dx/d!. Therefore width ≥m_h at every
γ where this minor is nonzero, in particular generically;
at d=0 the determinant is nonzero for every γ. This is not
a full-column lower bound for arbitrary tableaux. In particular
ceil(p/2) is a genuine terminal width minimum for methods with
terminal-only weights, attained there by minimal Gaussian
quadrature. The new construction does not claim to attain the
internal moment minors as width lower bounds.

## Order 20, depth 18, ten contributing clocks

Use the published ten-point Gaussian terminal rule, p=20,
D=18, so L=2. Let γ be a reciprocal of a root of L_19^(1).
The only omitted paid tree is T_19, whose shifted target is
zero, while λ_18(1) and λ_20(1) are nonzero by the recurrence.
This yields exact order 20 and exact depth 18.

Layers h=1,...,8, including s_8=q=10, each lose one stage.
The widths are

    1; 2,3,4,5,6,7,8,9; then ten layers of width 10.

The total is 1+44+100=145, versus the published 153-stage
full-column construction. The output still uses exactly the
ten original Gaussian clocks with positive weights.

One can choose these eight altered meshes explicitly without a
root approximation. The monic polynomial (-1)^19 19! L_19^(1)
is Eisenstein at 19: the coefficient of x^k for k<19 has a
factor 19!/k!, and the constant has valuation exactly one.
Hence the degree of γ over Q is 19. For h=1,...,8 set

    R_h(X)=∏_{j=1}^h (X+j),      d=18−h,
    z_h=λ_d(X R_h)/λ_d(R_h).

Use clocks −1,...,−h,z_h at that layer. Each denominator and
collision polynomial λ_d((X+j)R_h) is a nonzero rational
polynomial in γ of degree at most d<19. Its leading coefficient
is ±ℓ(R_h) or ±ℓ((X+j)R_h), respectively, and those integrals
are positive on [0,1]. None can vanish at γ. Thus the meshes are
distinct, lie in Q(γ), and require no new coefficient extension
beyond the same Gaussian splitting field compositum with γ as
before. When γ is real, these clocks are real algebraic. In
particular the [known coefficient-field minimum](COEFFICIENT-FIELD-ENDPOINT.md)
of degree 72,960 at this ten-clock depth-18 endpoint remains
attained, now with 145 stages. This is not a stage minimum.

More generally early reduced clocks can be taken in Q(γ) by the
rational free-choice argument; unchanged ones are subsets of the
given clocks. With rational γ and a rational terminal rule, every
entry and clock in the construction is rational. For example the
published q=p−1 rational rules missing degree p supply exact
order under the same shifted paid-height criterion. Earlier
clocks need not lie in [0,1] or increase in stage order.

## Independently replayable rational case

At p=4, D=3, γ=1 use terminal clocks 1/8,1/2,7/8 and weights
8/27,11/27,8/27. Symmetry and second centered moment 1/12 give
degrees 0 through 3, and degree 4 fails. At h=1 the reduced
clock is λ_2(X)/λ_2(1)=(5/24)/(1/6)=5/4. At h=2 use free
clock −1 and z=λ_1(X(X+1))/λ_1(X+1)=(-7/12)/(-5/6)=7/10.
Group sizes are 1,1,2,3: seven stages, versus nine without
these two reductions. In stage order by those groups, the strict
nonzero entries of B (indices 0 through 6) are

    B_10=1/4,
    B_21=−2, B_31=−3/10,
    B_42=−317/1088, B_43=−635/1088,
    B_52=1/68,     B_53=−35/68,
    B_62=259/1088, B_63=−395/1088.

Set A=B+I_stage; the first four weights are zero. Direct rational
tree recursion gives the eight values through order 4:
1; 1/2; 1/3,1/6; 1/4,1/8,1/12,1/24, the inverses of the
respective tree factorials. The order-five bush gives 51/256
instead of 1/5. The strict height-three tall readout is 1/24,
so dependency depth is exactly three. The [companion exact-arithmetic check](check_paid_width_rational_case.py)
replays these facts without a search.
