# Late common-diagonal corrections: positive sharing and scalar limits

**Pure mathematical analysis.** Work over a real characteristic-zero
coefficient field with common nonzero diagonal γ; the constructions
are rational over the input fields plus any chosen real Gaussian
nodes. This does not assume a prefix shape for the physical base or
continuation. No unrestricted stage endpoint changes.

There is a useful low-cost dense-state and quadrature reduction for
late mixed corrections. There is also a sharp scalar obstruction to
the ordinary repeated-cell extrapolation route, and a stage-price
obstruction to independently lifting scalar-active corrections at
the virtual clock nodes. Neither excludes genuinely coupled
zero-tall corrections. No tested high-order residual of a small
base is identified with the cheap correction family below.

## 1. Dense virtual anchors with no new base stages

Let an actual common-diagonal base (A,b) pay order P, and choose
integer d≥1 with 2d−1≤P. Let C=diag(A1). For a stage vector v
define the polynomial Q_v of degree <d by its d moments

    ∫₀¹ x^a Q_v(x) dx = bᵀ C^a v,       0≤a<d.

The rational unit-interval moment matrix is invertible. If v is
the actual rooted profile Φ_t(A) for |t|≤d, the paid scalar
substitution gives Q_v(x)=|t|x^(|t|−1)/t!. Indeed multiplying
by c^a attaches a leaves at the same root, and |t|+a≤2d−1.
This recovers the whole polynomial profile as a signed
physical covector, without claiming any individual stage is
locally exact.

Write the linear integral of this projection as β(x)ᵀv,
where β(x)ᵀv=∫₀^x Q_v. Then
y+hΣ_i β_i(x) f(Y_i) is dense output for the exact flow
through order d. Using the same already evaluated stages,
define

    z̄(x)=y+hΣ_i (β_i(x)−γ β′_i(x)) f(Y_i).

Its jet through degree d is the virtual clock state

    z*(x)=(id−γ h f)∘flow_f(xh)(y),

because the x derivative of the exact flow is
h f(flow_f(xh)(y)). This is the state underlying the QSym
character exp(x Γ) T_γ^−1. It is an **affine causal mean
state**, not an assertion that one actual real prefix
history realizes that character. No new dense-output
implicit stage or Gaussian-clock prefix fiber is required.

## 2. Cross-clock quadrature of one known late defect

Suppose an actual common-diagonal correction map on an
input z has Φ(z)=z+C_h(z), with C_h=O(h^t), and suppose the
required residual of a base construction is known to be

    flow_f(h)(y) − Base_h(y)
      = ∫₀¹ C_h(z*(x)) dx + O(h^(p+1)).                   (A)

The correction can use additional shared earlier data
independent of x, computed from y, as long as its onset is
uniform in the remaining state argument. Alternatively
one may already have actual affine anchor states at
distinct clock labels agreeing with z* through d=p−t:
d+1 such states suffice, since the h^j coefficient of
z* has degree at most j in x, so Lagrange interpolation
recovers that jet at a fresh clock.

In either situation with d=p−t available, each coefficient
at h^(t+j), j≤d, of C_h(z*(x)) has degree ≤j in x by Taylor
expansion. Use a real q_t=ceil((p−t+1)/2)-node Gaussian
quadrature and put the correction at its actual affine
states z̄(x_j). Replacing z* by those states changes the
first omitted order only. The updates are actual causal
common-diagonal rows: z̄(x_j) is y plus a row of previous
slope increments, and feeding that row to each stage
of Φ retains its strict chronology and self γ. Return
the increments of Φ, not another copy of the state z̄.

Thus (A) gives a verified order-p construction with

    S = S_base + S_shared + q_t S_local

stages if the stated donor and local correction blocks
are physically disjoint as counted. If Base pays t−1,
its existing rows automatically suffice for the dense
anchors whenever t≥ceil(2p/3): then
t−1≥2(p−t)−1. At greater t this can use far fewer than
ceil(p/2) copies of a correction, and it does not need
real history realizations of the virtual characters.
Gaussian nodes may enlarge the real algebraic field;
signed (d+1)-point rational quadrature is an alternative
if that enlargement is unwanted. This is a conditional
compression rule, not a proof of the residual (A).

## 3. Cheap genuine late maps which have zero tall response

There is no general claim that a correction with onset t
needs t stages. For example form the actual r-step prefix
difference

    V_r(z) = (T_a−I)^r id(z),    a≠0,

where T_a is pullback by the common-diagonal Euler move
E_a(z)=z+a h g_γ(z) with
g_γ(z)=f(z+γ h g_γ(z)). This is an actual affine linear
combination of previously computed slope increments and
has leading term a^r h^r D_f^r id(z). It needs r stages
when evaluated at z; it can also be computed once at
the common initial y and reused as shared input data.

Now use mth ordinary finite difference of the slopes
at inputs z+j V_r, j=0,...,m, with the same γ:

    C_h(z) =
       h Σ_(j=0)^m (−1)^(m−j) binom(m,j) g_γ(z+jV_r).

All lower powers in the Taylor direction cancel. Its
first possible and actually nonzero degree is rm+1,
with leading elementary differential combination

    a^(rm) D^m f(z)[D_f^r id(z),...,D_f^r id(z)].

Nonzero can be seen on the finite polynomial jet of
f(y)=exp(y) at zero, without using a numerical test.
For m≥2 the correction is identically zero on linear
fields at every order, since g_γ is linear then.
It costs r+m stages when the unshifted input slope is
reused from the prefix. With V_r computed at y once,
a q_t-copy version costs only r+q_t(m+1) extra
stages. All coefficients in the correction are rational
over γ and any chosen nonzero rational a.

This exhibits cheap nontrivial late mixed continuations
that evade a scalar pole obstruction. It does not give
an arbitrary correction: at its first affected grade
the root has m children of the indicated grade-r
direction. It cannot repair a missing tall condition,
and a generic high-grade residual need not be in this
narrow multilinear span. Several directions and partial
polarizations can be used, but their actual shared
donors and nonlinear residuals must be proved.

## 4. Sharp limitation of ordinary refinement extrapolation

A different standard tactic is one regular repeatable
common-γ cell M_ε, using at most r stages per cell, to be
repeated n times at ε=1/n and extrapolated to ε=0.
Assume M_0 is the identity on the paid jet. On the
linear test its stability function has form

    R_ε(z)=P_ε(z)/(1−γz)^r,       deg_z P_ε≤r.

Coefficients are regular at ε=0. The coefficientwise
refinement limit is

    exp(G(z)),       G(z)=∂_ε R_ε(z)|_(ε=0),

by logarithm of the cell through the paid jet. Since
G has the same single-pole denominator and numerator
degree ≤r, matching the true generator z through p
is impossible if r<p. Clearing denominators would
make its numerator equal to z(1−γz)^r of degree r+1.
This is an obstruction for **regular refinement limits**,
not a proof against all tuned finite mixtures.

The cost r≥p is sharp for that generator problem,
including all trees: use p−1 forward common-γ moves
E_γ and interpolate their endpoints in the iterate
count at −1 through order p−1. This yields an affine
state equal to E_γ^−1(z) through that order. One more
stage evaluates g_γ there, hence f(z) through p−1.
Take its output with coefficient ε, giving a p-stage
regular cell M_ε whose limiting generator is exact
through p. This local sharpening is not an attractive
global stage count.

If the effective denominator order is r and the
generator pays exactly through r before repair, its
unavoidable next scalar defect is explicit:

    G(z)−z = −(−γ)^r z^(r+1)/(1−γz)^r.

Indeed truncate z(1−γz)^r to degree r in the numerator.
In particular no late repair starting at t can make
such an extrapolated limit of smaller cells exact
if r<t−1. In a fixed-cost refinement architecture
even one genuine branch with n≥3 costs at least
3p stages for the exact generator, above every
verified free upper at p≤20. This statement counts
the actually repeated cells; it does not presume
arbitrary degenerate sample cells have the generic
cost. More invariantly, the full derivative generator
must have pole order ≥p after cancellation. Its
nonzero Laurent coefficient forces at least that pole
order in the cell for all sufficiently small nonzero
ε, and exact scalar representation of an n-fold
branch then needs ≥pn stages by pole multiplicity,
even with literal sharing.

Two common variations also fail in the stated scope:

* Any composition of such refinement limits, with
  fixed durations, has scalar log a linear sum of
  generators. With a common γ and r bounding their
  sizes, the same numerator obstruction requires
  r≥p. Conjugation by processors cancels on the
  scalar test and cannot mend it.
* A signed consistent mixture of their limiting
  maps (or of compositions of them) does not evade
  the bound if each scalar log is z+O(z^t) with
  2t>p. Squared defects are unpaid, so the scalar
  comparison again requires a linear combination
  of the same rational generators to be z through p.
  To evade by a mixture of smaller cells one needs
  earlier defects, active nonlinear interactions, or
  an actual additional scalar-correcting block.

The ordinary even-error shortcut is not automatic
either. If a **regular same-γ family in ε** obeys
R_ε(z)R_(-ε)(z)=1 through p with p≥2r, the numerator
after clearing denominators has degree ≤2r, so it
obeys it exactly. Both functions have their only
possible pole at 1/γ; their zeros can then be only
there too, so R_ε must be an integer power of
1−γ z normalized at zero. The first coefficient is
discrete in ε and cannot have the required nonzero
derivative at ε=0. Thus one cannot borrow reversible
midpoint parity with a tiny regular common-diagonal
cell. This does not rule out the earlier virtual
inverse construction or sampled values with no
regular same-γ limit.

## 5. Even cross-clock quadrature is too costly for
independent scalar-active late copies

Suppose in (A) the **common local correction** has
nonzero scalar response starting at exactly order t.
On the linear problem the virtual state is
(1−γz)e^(xz)y. Therefore correction quadrature
through p requires, after canceling the common
nonzero leading scalar series, ordinary moments
through d=p−t at the chosen time nodes. At least
q_t=ceil((d+1)/2) real nodes are necessary even with
signed weights, by squaring the monic hull otherwise.
Thus the reduced Gaussian node count in Section 2
cannot be made smaller on this scalar-active route.

Each independent common-γ correction copy with scalar
increment starting at t needs ≥t stages: its stability
minus 1 has numerator degree at most its stage count,
so it cannot be nonzero and have a zero of order t
at the origin if there are fewer than t stages.
This bound is sharp (the tth endpoint difference
of one prefix has scalar increment
(a z/(1−γz))^t). For independent copies with no
cross-clock stage sharing, the total cost satisfies

    S ≥ S_base + t ceil((p−t+1)/2).

The base itself must already pay order t−1 if these
corrections start at t. The usual common-diagonal
commutator bound gives
S_base ≥ (t²−1)/8. For reference, at paid order m
the actual invertible commutator
R=CA−AC−A² is pure and raises feature grade by two;
its diagonal is −γ². In grade j its image of the
grade-(j−2) space is independent of the monomials
1,c,...,c^min(j,m−1−j) by the paid Gram tests.
Thus the size is bounded below by the larger parity
sum of min(j+1,m−j), which is at least m(m+2)/8
(equal for even m; for odd m the larger parity is
at least half the total). Set m=t−1.

For t≥p/2 the resulting lower bound is at least

    [−3t²+4(p+1)t−1]/8.

It is concave in t. For p≥8 its lower endpoint value
on [p/2,p] is (p²+4p−1)/8 at t=p; for p≤8 use the
minimum with (5p²/4+2p−1)/8 at t=p/2.
The integer bounds so obtained are never below the
verified free upper at any p≤20 (and strictly above
it for p≥8). Thus even Gaussian compression of the
virtual clock integral does not make independent
scalar-active late tails a free-upper construction.
If their scalar action starts later than their
nonlinear one, or the copies share a genuinely mixed
physical bridge, this comparison does not apply.

## 6. Exact remaining opportunity

There is no competitive family from ordinary refinement
or separable scalar-active repair. The positive
replacement is precise: use an actual base's dense
covectors to get the virtual inputs, share real
prefix-derived directions, integrate only at the
smaller late Gauss rule, and supply the missing
nonlinear residual with a physically coupled bridge.
For a cheap purely nonlinear repair the base must
already have its tall response correct through p.

Even the leading finite-difference directions in
Section 3 do not automatically span an actual base's
high residual. For example if the first discrepancy
is a modified-flow term E of grade t with 2t>p,
its propagated response against Y=hD_f is the
one-insertion Duhamel term
∫₀¹ exp((1−x)Y) E exp(xY) dx through p:
expanding words with one E gives the beta coefficient
1/(i+j+1)! at Y^i E Y^j. It includes a later
variational transport, not just a local function
evaluated at a clock and one direction. That is a
genuine two-sided constraint. No general near-table
realization of this paid residual was found.
No grids, numerical search, or new free endpoint
are used here.

Only shared data available as causal affine combinations of earlier slopes can be supplied to an actual tableau without paying additional stages. Replacing a local difference direction V_r(z) by one shared direction V_r(y) generally preserves only the leading correction; the full late residual identity must be checked for the shared variant as well. The pole price for exact replacement of the whole rational map does not imply the same price for matching a finite Taylor jet.
