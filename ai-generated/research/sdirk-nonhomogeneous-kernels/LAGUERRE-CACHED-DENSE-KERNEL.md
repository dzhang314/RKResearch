# A nonhomogeneous Laguerre kernel with cached dense RK modes

Pure math; positive prescribed common diagonal gamma, especially rational.
There is no long homogeneous Euler or midpoint prefix. The construction is
an actual lower-triangular SDIRK stage DAG with scalar constant entries over
a real algebraic field. It gives compact dense-flow kernels, not a new
unrestricted ordinary-order upper bound. All accuracy claims are for
every indicated rooted tree, except where expressly called scalar.

## 1. Stage chart and a two-grade orthogonality band

Put J P(x)=integral_0^x P(t)dt and T=J-gamma Id. Define the monic
polynomial
    W_k(x)=k! T^k 1=k!(-gamma)^k L_k(x/gamma),
where
    L_k(z)=sum_{j=0}^k binom(k,j)(-z)^j/j!.
Then T W_k=W_(k+1)/(k+1). These are the monic orthogonal polynomials
for the normalized positive measure dmu=(1/gamma)e^(-x/gamma) dx
on (0,infinity). Indeed the explicit coefficients give the Rodrigues
identity W_k=(-gamma)^k e^(x/gamma) (d/dx)^k(e^(-x/gamma)x^k).
Integration by parts gives orthogonality to degrees <k, and the
sign-change argument gives k distinct positive roots. Multiplication
by x takes W_j into span(W_(j-1),W_j,W_(j+1)): lower coefficients
vanish by moving x across the inner product. The W_(j-1) coefficient
for j>=1 is the positive squared-norm ratio. Write this recurrence as
    x W_j=W_(j+1)+beta_j W_j+alpha_j W_(j-1),  alpha_j>0 (j>=1).
Consequently consecutive W's have no common zero. All their algebraic
data and the exponential moments m! gamma^m are exact over Q(gamma)
before adjoining sampled real roots.

Write a stage chart as a polynomial-valued constant row combination
of actual observations H_i=h f(Y_i). Its normalized profile for tree t
is f_(k,t)(x) (the h^|t| F_t/sigma(t) coefficient). Start chart 0
identically zero. In layer k>=1, at each of the k roots z of W_k
take one actual stage
    Y=y+(T chart_(k-1))(z)+gamma h f(Y).
The strict prestate is an affine combination of earlier observations;
there are no within-layer strict inputs. Layer 1 is one plain gamma
stage with clock gamma. For k>=2 the old chart has bullet profile 1,
so every new actual clock is the specified z: T1=z-gamma.
Set chart k to the Lagrange polynomial of degree <k for its new
observations. This full (untrimmed) version has 1+...+r stages
through layer r. The error proof below lets one replace many of
these nodes by cached modes.

The exact derivative profile is psi_t(x)=|t| x^(|t|-1)/t!, with
t! the product of the subtree sizes. It satisfies psi_bullet=1 and
psi_[t1,...,tm]=product_i J psi_ti. Let G_(k,t)(x) denote the
unprojected polynomial stage profile for the same row construction
at a formal x, before taking remainder modulo W_k. Thus recursively
    G_(k,[t1,...,tm])
      = product_i (gamma G_(k,ti) + T f_(k-1,ti)).
At W_k nodes it is the physical stage-weight recursion, and
f_(k,t)=rem_(W_k) G_(k,t). Both have degree <= |t|-1. This is a
recursion on smaller child trees, not an assumption about an
implicit polynomial-valued global solve.

For every tree t of grade n,
    psi_t - f_(k,t) uses only W_j with j >= 2k+1-n.                (A)
The same holds for G_(k,t) before reduction. Negative cutoffs
place no restriction. Prove by induction on layer k, from chart 0,
and on the child sizes at a fixed layer. The child primitive
difference for size m is
    J psi_s - (gamma G_(k,s)+T f_(k-1,s))
      = gamma(psi_s-G_(k,s)) + T(psi_s-f_(k-1,s)).
It begins at Laguerre index at least 2k-m: T raises an index by one.
In the product difference at the root, all other factors have
total degree <= n-1-m, and multiplication cannot lower a
Laguerre index by more than the factor's degree. Thus every product
difference begins at index >=2k+1-n. Finally reduction changes a
polynomial of degree <=n-1 by W_k times a polynomial of degree
<=n-1-k, which again begins at index >=2k+1-n. This proves (A).
The proof never substitutes divisibility by degree for actual
rooted-tree multiplication.

Consequences:
* f_(k,t)=psi_t for |t|<=k, since the error has too high an index.
  At |t|=k+1 the error is precisely (|t|/t!) W_k, determined by its
  leading coefficient. In particular the real physical stage
  observations at the W_k sites are exact derivative profiles
  through k+1; their stage states are exact through k (apply
  the same child-primitive bound at their roots).
* For any fixed degree m polynomial test R, the exponential output
  integral of R times the chart pays every tree of order n with
  n+m<=2k. This follows by orthogonality of (A).
* At n=k+d, d>=1, the non-universal parts of the vector-valued
  error can appear only in the at most d-1 modes of index <k.
  Modes >=k are just the known high part of x^(n-1) times the
  exact-flow elementary-coefficient vector. Thus the span of
  the clock-dependent grade-n error vectors has dimension <=d
  (or the stronger count from the actual index interval). This
  is a rank across clock modes, not a claim that an arbitrary
  order residual lies in a small universal dictionary.

With R=1 this is an all-tree superconvergence of order 2k for
the exponential-Laplace readout. It realizes
    y+(R_gamma(y)-y)/gamma  through grade 2k,
where R_gamma(y)=integral Phi_(xh)(y) dmu=(Id-gamma*h D_f)^(-1)y
as a formal flow average. Indeed h f(Phi_(xh)) is the time derivative
in x of that flow and integration by parts gives the factor 1/gamma.
It is not the ordinary time-one flow. The scalar readout of the full
untrimmed diagram is exactly 1+z/(1-gamma z): its final row functional
annihilates T on every polynomial (integrate J by parts), so b^T A
=gamma b^T, and b^T1=1. Signed low-degree output weights alone do
not turn this superconvergence into ordinary order 2k.

## 2. Cached compression uses fewer physical nodes and fewer field generators

Fix a paid cap P>=2. At level k<=P, put
    L_k=max(0,2k-1-P),   d_k=k-L_k=min(k,P+1-k).
Levels can be stopped at any r<=P. Reproduce the full chart through
every tree of grade <=P using only d_k new stage nodes at level k:

1. Cache W_j coefficients for j<L_k from layer k-1. For every
   n<=P these coefficients are already exact-model coefficients
   in both charts, by n+j<=2k-2. No new moment receipt is assumed.
2. Sample the actual stage row using the cached-and-reconstructed
   chart k-1 at any d_k distinct roots of W_k. Inductively the new
   samples equal the corresponding full diagram's samples through
   grade P: a child precedes the current root in grade, and all
   the preceding chart rows are actual fixed affine forms.
3. Subtract the low-mode contribution at the new sampled nodes
   and recover the missing d_k high coefficients by a single
   constant linear system. This gives the entire chart, including
   the unpaid high modes of each tree in the declared cap, equal
   to the full diagram's chart within that cap.

The high-mode interpolation is always invertible on *any* such
subset. On W_k roots, backward iteration of the three-term
recurrence expresses W_(k-1-j)(z)=P_j(z) W_(k-1)(z), with P_j
degree j and nonzero leading coefficient. (Start with W_k=0
and W_(k-1) !=0, then solve the recurrence downward.) Thus
evaluation of span(W_(L_k),...,W_(k-1)) is a Vandermonde basis
of degree <d_k times a nonzero pointwise scale. This proves the
actual stage construction, with no interpolation or rank oracle.

The number of physical stages through r is exactly sum_{k<=r} d_k
in this construction (coincident or removable rows would not
invalidate the upper count). In particular
    r=P-1: floor((P+1)^2/4)-1,
    r=P:   floor((P+1)^2/4).
The stop at r=P-1 uses the ordinary r through r+1 readout below.
The split field need contain only the selected node coordinates,
not all conjugate roots of each W_k. Chart coefficients are obtained
by arithmetic on these coordinates and gamma, plus rational
polynomial integrals. For a readout to clock a, the actual
coefficient field is exactly Q(gamma, selected clocks, a): these
clocks are the physical row sums and a is the sum of the output
weights. There is no additional root requirement from recovery.
All selected clocks can be positive and <1 by taking gamma small
enough; this follows from finitely many positive roots at scale
gamma=1. The formal proofs do not require this interval restriction.

## 3. Ordinary dense time and the exceptional nodes

Integrating chart r from 0 to a is an actual output from the same
stage observations (no extra node), with polynomial weights in a.
It has ordinary order r at every nonzero clock a, provided the
paid cap is >=r. If cap >=r+1, its common first error is
    (coefficient vector of exact derivative grade r+1)
                                      * integral_0^a W_r(x)dx.
It therefore has ordinary order r+1 at precisely the nonzero
roots of that integral, and otherwise fails already at the next
grade. Directly from the binomial coefficients,
    integral_0^a W_r(x)dx
       = r!(-gamma)^r (a/(r+1)) L_r^(1)(a/gamma),
    L_r^(1)(z)=sum_j binom(r+1,r-j)(-z)^j/j!.
L_r^(1) is orthogonal for x e^(-x) on (0,infinity) by the same
Rodrigues argument with weight x, hence has r distinct positive
roots. Thus one shared coefficient table has r higher-order
readouts; for absolute step a=1 choose gamma as a reciprocal
root. That choice adds only its own algebraic generator. For
rational gamma, a rational a is allowed for the ordinary
nonexceptional readout.

No readout of a single height-r table here can reach ordinary
order r+2 at any nonzero a, even using all earlier layers: the
strict part B=A-gamma Id satisfies B^r=0. Scalar order r+2
would force b^T B^r1=b^T B^(r+1)1=0 to equal the two paid
integrals of T^r1 and T^(r+1)1 on [0,a]. These are proportional
to consecutive L_r^(1) and L_(r+1)^(1) at a/gamma; their
orthogonal three-term recurrence rules out common roots.
Consequently the quadratic saving is a dense-kernel saving,
not a way to read off p=2r ordinary order.

**One rational enrichment.** Stop at r=P-1 with cap P.
For any rational z with W_r(z)!=0, use one additional actual
stage with strict prestate (T chart_r)(z). At its clock it has
the exact derivative through r+1, because chart r is already
exact through r. Let H_z be that stage observation. Then
    chart_enriched(x)=chart_r(x)
                 +(W_r(x)/W_r(z)) (H_z-chart_r(z))
is exactly the full derivative polynomial through r+1,
using the explicit one-shape error above. Thus the last
node can be rational (e.g. z=0), and the full dense order
P kernel costs floor((P+1)^2/4), adjoining no root at the
last level. For example cap P=10 through r=9 gives 29 stages
with dense order nine and nine exceptional order-ten readouts;
one rational node gives dense order ten everywhere, at 30.
This needs neither a previous ordinary order-19 method nor
a long nominal prefix.

## 4. A scalar-exact high-depth tail, and an exact leading nonlinear gate

Use a dense order-q kernel, q<=p, and keep its actual rows.
It contains a direction V_q starting at grade q with exact
flow derivative G_q=D_f^q id as its leading elementary
combination: take (q-1)! times the x^(q-1) coefficient of
the exact derivative chart as a fixed row combination.
Nothing of lower grade survives. The tall coefficient of
G_q is one. The first physical stage at prestate y supplies
the known H(0)=h g_gamma(y).

One new stage per further grade gives
    V_(j+1)=H(V_j)-H(0),   H(V)=h g_gamma(y+V),   j>=q.
Its leading vector is Df[G] if G led V_j: a unary root,
with tall coefficient still one. All these prestates are
fixed affine combinations of retained observations. This
is a response chain of signed differences, not a homogeneous
Euler row schedule. As the scalar leading degrees are distinct,
triangular reweighting pays scalar stability through p without
touching any order <=q of the dense step to a=1. The actual
stage count is
    floor((q+1)^2/4)+p-q.
No extra field is required for the tail. For example p=20,
q=12 starts at 50 stages with ordinary order >=12 and scalar
order >=20. This is an actual starting tableau; saying “scalar
order 20” is not saying order 20. Its nonlinear continuation
is the unsolved part.

There is an exact first nonlinear defect formula when the
initial chart q is reproduced through q+1 (use cap q+1, through
level q, count floor((q+2)^2/4)-1). Write mu_q=integral_0^1 W_q.
The base grade-(q+1) residual is mu_q G_(q+1)/q!. The first
scalar-tail update cancels the tall by adding mu_q J_root G_q/q!,
where J_root grafts one unary root. Its leading vector actually
cancels **all** unary-root terms: the raw coefficient of
F_[t] in G_(q+1) is (q+1)!/[sigma(t)(q+1)t!],
exactly the raw coefficient of F_t in G_q. Thus after the
whole scalar tail the first grade's residual is
    (mu_q/q!) times the branching-root projection of G_(q+1).
This is one explicit universal vector (not an arbitrary mixture
of all trees at that grade). Its mixed child-size directions
use only the exact G_j donors already in the kernel.

It can be corrected by one rational-clock receiver, rather
than separately evaluating each mixed branch stencil. The
difference H_z-chart_q(z) of Section 3 has leading vector
W_q(z) G_(q+1)/q!, and no lower grade. Subtract from it the
already available scalar-tail rows needed to remove its scalar
response through p. Its grade-(q+1) vector is then
W_q(z)/q! times the same branching-root projection, since only
the first unary tail appears at that grade. With the right
weight it pays the full first nonlinear defect with p tall
orders preserved. Alternatively enrich before setting up the
tail and restart it at q+1; that uses the first tail slot
for the richer receiver rather than adding a stage. Nothing
in this argument pays all subsequent nonlinear grades, or
asserts scalar equality beyond the paid band after reweighting.

## 5. Why this route is distinct, and what remains to improve an upper

No nonzero exact polynomial carrier of grade <=q can vanish on
the predecessor-closed dense order-q kernel. Its actual chart
would give zero for that expression at every clock, while the
exact model of its chart is the nonzero polynomial. Thus the
earlier supported grade-three or grade-four lower bounds for
a retained Euler/midpoint prefix do not transfer. The main
kernel has at most q levels and is repeatedly recombining
independent clock modes across stages; its long scalar path
comes only from the separate tail. The exact field and the
clock-dependent residual-rank property give targets for
mixed nonlinear continuations without broad table search.

There is still a general useful retention check (not a new
ordinary upper). Since B^q 1 vanishes on the whole closed
kernel, q! B^q1 is a supported carrier with exact model W_q.
Using B on supported expressions raises a mode, while
M-(j+1)B-beta_j Id on a carrier of W_j gives alpha_j W_(j-1).
So at grade G>=q+1 the supported model space contains the
consecutive indices
    max(0,2q+1-G) <= j <= G-1.
These identities concern actual supported rows, not moment
substitution inside the retained kernel. Applying the usual
invertible Pi=[M,A]-A^2 descent, level l with G=p-2l can
contribute min(2l+1, number of those indices) independent
outside directions for sufficiently small positive gamma.
To verify the hypothesis, use as left tests x^0,...,x^(d-1)
against d consecutive selected indices. Its determinant is
nonzero at the limit gamma=0, where W_j=x^j and this is a
positive moment matrix for the weight x^(first index).
The finitely many determinants are polynomial in gamma;
their nonvanishing is uniform for gamma sufficiently small.
One still requires gamma!=0 in the actual Pi inversion.
Paid proof: divide a dependence by its first Pi power and
use these left-test rows, just as for the earlier positive
supported-carrier staircase, with grade
G+2(l-l0)+2l0<=p. Thus the outside count is at least
    sum_{l: p-2l>=q+1} min(2l+1, min(p-2l,2(p-2l-q)-1)).
For illustration, p=20,q=12 gives 12 outside beyond the
42-stage dense kernel, hence at least 54. The scalar tail
uses eight of those; an actual 54--58 continuation is not
decided. The deeper q=13 dense starting point cannot improve
59 under this small-gamma retention test. These are formulas
for a new architecture, not a finite-order feasibility search.

The construction supplies dense all-tree order at about
one quarter of the squared dense order, a cheap exact scalar
end-cap, a known first branch defect, and no extra root field
at reweighting. To improve the unrestricted table one must
still match the remaining nonlinear residual beyond the first
paid new grade, with actual coupled physical rows. Neither
the exponential kernel's 2r band nor the scalar end-cap is
an ordinary p-order upper bound.
