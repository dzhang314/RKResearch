# Physical hull descent beyond adjacency: a paid signed bypass

A two-receiver skip can preserve all paid trees and the coefficient field of an adjacent construction. The proof gives hull criteria in this particular class; it does not give an unrestricted stage bound. The retained field is a number field when the starting data are algebraic.

Use a characteristic-zero coefficient field K and common diagonal
γ. Write c=A1, B=A−γI, J=I_x−γ id (I_x integrates from 0 to x),
ℓ=∫₀¹dx, and T=V−γ id for the scalar adjoint in y=1−x, with
V integrating from 0 to y. A strict edge goes from its donor
to its receiver. Paths below are traced *backwards* from terminal
output to donors. The terminal rule is kept fixed.

## 1. What is lost at an arbitrary skip edge

For a fixed d and decorations k_0,...,k_d of total at most b,
the actual row

    b_outᵀ Y^(k₀) B Y^(k₁) ... B Y^(k_d),
    Y=diag(1−c),

reads endpoints of strict paths of length d, not a prescribed
chronological level. If r+d+b+1≤p, its application to H(Y)1
for deg H≤r is a paid combination of literal RK outputs.
Exact-flow substitution and integration by parts give

    actual row applied to H(Y)1 = ℓ(H W_k),

where W_k is the corresponding ancestor test. This proves the
ordinary annihilation for the **union** of its possible endpoint
clock labels (with any path cancellations taken into account).
It does not give the moment for the hull of one selected level
if another clock leaks into the same row. Simply knowing the
assigned levels or their ordering does not isolate it.

Here is the exact extra linear observation for this proof
mechanism. Let U index combinations of the paid words; let
φ:U→C(d,b) be the map to their ideal test polynomials. For a
target set S of stages let Λ:U→K^(outside S) record the
actual row coefficients outside S. For a hull zero on S,

    ℓ(H φ(u)) = sum_(i outside S) Λ(u)_i H(1−c_i).

The ideal tests which admit a row supported entirely in S
are exactly the kernel of the well-defined map

    C(d,b) → im Λ / Λ(ker φ),    φ(u) ↦ [Λ(u)].

Indeed a leakage lying in Λ(ker φ) can be subtracted without
changing the ideal test, and no other leakage can be removed
in that way. This identifies the precise missing observations
for arbitrary-column row isolation at that budget. One can
instead use the leakage functional restricted to the image
of polynomial evaluations, or just its scalar value on a
particular H; those are weaker, hull-dependent observables.
An exact inhomogeneous leakage receipt is not the same as an
independent zero-moment gate.

A purely clock-polynomial mask which vanishes on a complement
with a distinct labels costs at least degree a, unless some
labels need not be masked. Multiplying by that mask also
changes the ideal test and spends the same order budget.
It cannot distinguish repeated physical stages of the same
clock. Thus generic skips do not extend the adjacent descent
lemma just by assigning a new distance to each stage.

## 2. Two compensating skip receivers

Start with an attained adjacent cardinal-row construction, with
stages on levels 0,...,D, where L=p−D is 1 or 2. Write r_h for
its physical widths and let ρ_h denote cardinal interpolation
on the assigned sites at each positive level (the initial
level only contributes its singleton/leaf data). Use an
index 1≤k≤D−2 such that levels k and k+1 use identical grids
in the same order; denote their common projector by ρ.
This is compatible with the adjacent paid gates whenever
r_k=r_(k+1): use the later hull at both. At fixed r the total
d+b=p−1−r is fixed and C(d,b) is nested towards terminal,
by its T-power formula (or the y^d formula at γ=0).

Take a∈Q with a≠0,1 and put b=−a/(1−a). Replace the rows
only at receivers k+1 and k+2, as follows.

* At k+1 take (1−a) times the ordinary J-cardinal stencil
  from k, and a times the J-cardinal stencil from k−1.
* At k+2 take (1−b) times the ordinary J-cardinal stencil
  from k+1, and b times the J-cardinal stencil from k.

A stencil from a donor grid means apply J to each of its
cardinals and evaluate at the receiving sites. In particular
both new receivers have scalar row-sum multipliers 1, so
their physical clock sums are unchanged:
γ+(J1)(x)=x. The unchanged terminal weights together with
the actual diagonal and clocks recover exactly the same
field of assigned nodes as before. Conversely every new
matrix coefficient is obtained using only that field and
the rational a,b. No new hull or coefficient field is
needed. Signed weights are essential to this identity; no
claim of nonnegative strict coefficients is made.

The only additional profile input is the low-order equality

    G_k(u)=G_(k−1)(u) for |u|≤M,
    M=ceil((L+k−1)/2),                                     (B)

where G_h(u) is the *ordinary adjacent interpolated polynomial
profile* at level h of the strict tree u. This does not
require equality of every hidden tree column. Here is a
simple sufficient width check, independent of the nodes:

    r_j ≥ M−(k−1−j) for 0≤j≤k−1,  and r_k≥M.               (C)

Indeed M≤k since L≤2 and k≥1. Every tree of order ≤M fits
in both levels. On an address at depth l within such a tree,
raw degree is at most M−l−1, so every interpolation acts
as identity under (C); at level zero only a leaf is used.
Both profiles are therefore exactly the same unreduced
J-tree polynomial. In particular (C) holds if the widths
up through k are nondecreasing with jumps at most one and
r_(k−1)≥ceil((L+k−1)/2). This includes the full higher-budget
and explicit matched profiles wherever they have the indicated
flat width, and can also be checked directly for mixed cuts.

## 3. Why every paid rooted tree survives the bypass

Let F be the modified strict interpolated polynomial profiles.
The G and F profiles agree through level k. For a tree u with
children u_i put

    Q_i = J G_(k−1)(u_i),    Δ_i = J(G_k(u_i)−G_(k−1)(u_i)).

The shared projector gives three exact formulas:

    G_k(u)       = ρ ∏ Q_i,
    G_(k+1)(u)   = ρ ∏ (Q_i+Δ_i),
    F_(k+1)(u)   = ρ ∏ (Q_i+(1−a)Δ_i).

The input from the two donors combined by the receiver k+2,
before applying J, is

    (1−b) F_(k+1)(u) + b G_k(u)
             = [F_(k+1)(u)−a G_k(u)]/(1−a).

Expand this as a polynomial in the individual Δ_i. In
degrees zero and one the coefficients are exactly those
of G_(k+1)(u); all other terms involve at least two Δ_i.
For such a term to be nonzero, (B) forces two different
children of u to each have order ≥M+1, hence

    |u| ≥ 2M+3 ≥ L+k+2.

But a paid child of a tree of local order ≤L+k+2 at level
k+2 has order ≤L+k+1. Thus on every such child the combined
input is exactly G_(k+1)(u). This includes an empty child
product/leaf without any separate assumption.

Consequently F_(k+2)(t)=G_(k+2)(t) as actual interpolated
polynomials throughout the local order band |t|≤L+k+2.
Every level above is ordinary adjacency; induction on the
decreasing order of each child gives equality at every level
h≥k+2 for its paid band |t|≤L+h, in particular all literal
terminal readouts of order ≤p. This nonlinear cancellation
proves actual all-tree sufficiency; it is not an inference
from decorated word equality alone. The argument includes
the tall-zero band, where each strict profile past its
available level height is automatically zero.

The same proof can install several such bypasses at
k_1<...<k_j, successive k differing by at least three.
For the next pair the two lower donor levels already agree
with the ordinary profiles on the smaller band needed for
(B), and its two receivers are not among those previously
modified. Apply the expansion to the current lower profiles, not to all the original profiles. The original profiles are needed only on the low-order band in (B). Hence stage count, all paid trees,
fixed terminal support and coefficient field are unchanged
for all these pairs simultaneously.

After adding γI, agreement of B through p implies agreement
of the full tableaux through p by paid edge contractions.
The nonzero deepest paid tall target, when present, retains
exact depth D, since the graph still cannot have a path
longer than D. The separate first-unpaid witnesses below
retain exact order in the standard sharp profiles.

## 4. Actual paid-word isolation for the bypass class

The linear word calculation works for any actual tableaux
with the following block relations, not just those built
by cardinals. Use receiver-row/donor-column orientation.
In the window write

    B_(k,k−1)=S,             B_(k+1,k−1)=a S,
    B_(k+2,k+1)=(1−b)R,     B_(k+2,k)=b R,

with the matching clock grids Y_k=Y_(k+1). The remaining
edge k+1←k is the usual adjacency (arbitrary for this
linear cancellation), and there are no other skips in the
window or outside the designated separated windows.
The cardinal construction above has precisely these four
block equalities. For example the S stencils have the
same donor k−1 and identical receiving sites in k,k+1.

A shortened path across the full window, from k+2 down to
k−1, can use either middle level k or k+1, with the same
number of B applications. For any intervening Y power m,
their matrix contributions add to

    b R Y_k^m S + (1−b) R Y_(k+1)^m a S = 0.

The endpoint multipliers and every other factor coincide.
Thus all completed shortened passages cancel even in the
actual decorated words, at any budget. For separated windows
the same cancellation is grouped at any one shortened
complete passage, since the entry and exit levels are fixed
before and after the pair. The ordinary no-skip word of
length d can end only at h=D−d. The sole possible uncancelled
extra endpoint is a truncation inside a window at its k:
from k+2 take its direct skip and stop, so d=D−k−1 and
the ordinary endpoint is k+1. The two endpoints use the
same hull. No other path mixture can change the endpoint
because a skip in a complete window has already canceled.

Therefore a hull vanishing at the ordinary endpoint h
annihilates the entire actual paid row, including the
possible equal-hull extra layer. Every original adjacent
local moment condition is necessary in this physical
block class. In particular a saturated invertible cut
continues to force its split hull and field, without a
new discriminant argument. Conversely, for the stated
width/purity condition, the split hull choices construct
a tableau in this class by Section 3. The two statements
are a true hull-field feasibility criterion in this
restricted class, not sufficiency for arbitrary rows
merely obeying the block equalities.

The adjacent one-clock exact-order witness also survives.
For D=p−1 and p≥3, a length d=p−2 word ending at the
ordinary level 1 can only leak into level 0; that is a
completed shortened passage since every k≥1, so it
cancels. If a width-one level 1 could pay p+1, its linear
hull would therefore annihilate C(p−2,1). For γ≠0 this
is T^(p−3) Poly_(≤2); its three tests against degree ≤1
have the published full-rank rectangular beta-Hankel block
(largest factorial index p+1). This is impossible. Thus
the original Gaussian terminal rule can still be kept at
odd p without assuming a failing next bush or nonzero
first-unpaid shifted tall target. At γ=0 or the sharp
shallow exceptional branch use the existing tall witnesses.

## 5. Genuine skips, and why convex routing is different

Suppose the deepest paid tell is nonzero, and for a shared
grid all diagonal J-cardinal entries (J L_j)(x_j) of the
common-grid stencil are nonzero. A nonzero term of that
depth-D tall word uses an ordinary edge at every level.
At receiver k+2 on that path, suppose the ordinary
predecessor index on k+1 is j. The direct skip entry
from index j on k is also nonzero because that stencil
is the same R with a different nonzero scalar. The
ordinary edge from j on k to j on k+1 also exists by
the nonzero common-grid diagonal. Thus the very same
stage at level k now has two strict paths to the same
terminal output, with different lengths. This graph
cannot be regraded into strict adjacency while keeping
terminal output at a single level. This is stronger
than a gap in a chosen numbering.

The nonzero diagonal guard is an exact, auditable
polynomial evaluation condition. It holds uniformly at
each eligible plateau for sufficiently large |γ| in
the usual split ranges when the reused hull is saturated
or terminal Gaussian: at infinity the saturated hull
tends to the simple ordinary Legendre hull by the normalized
moment system, so each I_x L_j evaluation stays bounded.
Subtracting γ dominates (and the Gaussian case is fixed).
For example the full nonzero profile offers the flat
widths at s=3i+1,3i+2 wherever these are eligible, with
the width check (C). No particular special-order numerical
stage or root search is required. At other admitted diagonals
the nonzero check suffices if one wants to certify actual
non-regradability; paid sufficiency itself does not need it.

In contrast there is a clean obstruction to a **convex**
routing version of this design. If every edge takes a
nonnegative scalar times J and each positive layer's
scalars sum to one, the unprojected strict tall profile
at D has scalar weight (W^D1)_D, for W the routing matrix.
This is the survival mass after D donor moves for a chain
starting at D and stopping at level zero. Any reachable
positive skip has positive probability of a shorter path,
so this number is <1. Thus a purely unprojected
nonnegative routing reference cannot match a nonzero
deepest tall target if it has such a skip. This does not
forbid general nonnegative projected tableaux or imply a
stage-count bound. The signed bypass succeeds because
two shorter words cancel and the remaining nonlinear terms
require two separately late child profiles.

## An exact order-six example

For \(p=6\), \(D=5\), \(\gamma=10\), take widths \(1,1,2,3,3,3\),
\(k=3\), and \(a=1/2\) (so \(b=-1\)). On layers 3, 4, 5 take the same
shifted Legendre nodes \(1/2,1/2\pm\sqrt{15}/10\). Their monic cubic
\(H_*(y)=(y-\tfrac12)((y-\tfrac12)^2-\tfrac3{20})\) is orthogonal to
quadratics (odd symmetry, \(\int (y-\tfrac12)^4=1/80\), and
\(\int (y-\tfrac12)^2=1/12\)). Division therefore proves cardinal
terminal quadrature through degree five, and its hull pays both
width-three internal gates. At levels 1 and 2 the test spaces are,
respectively, the spans of \(T^4 1\) and \(T^3 1\). Use the linear
monic hull with root \(\int yT^4 1/\int T^4 1\), and the degree-two
hull with roots \(-1,\int y(y+1)T^3 1/\int(y+1)T^3 1\). Both means
are rational and in \((0,1)\); for \(m\le5\) the relative absolute
nonconstant terms of \(T^m1\) on \([0,1]\) are bounded by
\((1+1/10)^m-1<1\). The same bound for \(J^5 1\) proves
\(\lambda_5\ne0\). The initial site is the required \(x=10\).
Here \(M=2\) and (C) holds. For the common cubic grid, the product of
the two node separations for any cardinal is at least \(3/20\), so
\(|\mathcal I_xL_j(x_j)|\le20/3<10\). The nonzero guard holds on every column. The signed-bypass construction therefore yields a
genuinely non-regradable tableau of exact order six, depth five, over
the very same \(\mathbb Q(\sqrt{15})\) as its adjacent baseline.
The next bush combination \(H_*^2\) witnesses exactness directly.
No minimization or claim at arbitrary fixed fields or diagonals follows.
