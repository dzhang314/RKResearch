# Sharp order by number of constant blocks in variable-prefix SDIRK

In each branch take A=B+γI with
the same γ≠0, where B_(i,j)=τ_j for j<i within that branch and
there are no other strict entries. The increments τ_j can vary
and output weights at individual stages are arbitrary signed
scalars, not required to be the branch's own increments. Exact
literal prefix sharing changes nothing. Count blocks in the
history of increments *preceding* each stage with nonzero output
weight; a block consists of consecutive equal increments. There is no restriction on the number of branches. The proof works over a characteristic-zero field; a real prescribed algebraic diagonal gives real algebraic coefficients. This is not a result about other triangular rows.

For an integer s≥1, if all those histories have at most s blocks,
the maximum attainable order at each fixed γ≠0 is exactly

    2s+2  if s is odd;
    2s+2  if s is even and γ=1/(s+2);
    2s+1  otherwise.

The upper here means actual attainment in this prefix class, with
no useful stage-count bound implied. Rational increment choices
suffice, with output coefficients in Q(γ). The result is uniform,
not a special-order scan. For example order 20 requires nine
blocks somewhere in this class, and nine are sufficient if stage
count is unbounded. No unrestricted numerical upper changes.

## 1. The actual prefix evaluations

Work with a formal step h in a characteristic-zero field K, and
an autonomous polynomial vector field f. Define the formal field
g(y)=f(y+γ h g(y)), unique by coefficient recursion. For an
increment τ put E_τ(y)=y+τ h g(y) and let T_τ act by pullback,
T_τ φ=φ∘E_τ. At the current branch state z, the implicit
physical stage is Y=z+γ h f(Y), so its evaluated slope is
g(z). After the increment τ, the branch state is E_τ(z).
Thus for a chronological history w=(τ_1,...,τ_m) the stage
slope is T_τ1 ... T_τm g. The same holds when no natural
branch update is used as the final output: the RK readout
is y+h times the linear combination of these slopes with
the actual stage weights b_i. This is exactly the lower
prefix matrix described above.

For a composition α=(a_1,...,a_l) of positive integer parts,
of degree |α| and length l, define the monomial quasisymmetric
function

    M_α(w) = ∑_(i₁<...<i_l) τ_(i₁)^a₁ ... τ_(i_l)^a_l.

The empty composition gives 1. Put W_0=I and, for k≥1,
W_k φ = (h^k/k!) D_y^k φ[g,...,g], with g frozen inside
the derivative at its current point. Thus
T_τ=Σ_(k≥0) τ^k W_k. Without commuting any operators,

    T_τ1 ... T_τm g = Σ_α M_α(w) W_(a₁)...W_(a_l) g.      (1)

Terms of degree ≥p can be discarded in a stage slope for
order p.

For clarity the vectors W_α g are linearly independent in
this universal jet interpretation at the degrees where
they are paid. First take an unrestricted field g_0 with
no formal-step dependence. The degree-d rooted slope
coefficient for a tree with d nonroot vertices, up to
its nonzero rational symmetry normalization, is the strict
ordered-label enumerator of the forest of those vertices:
choose an earlier increment index for each child vertex,
strictly earlier along its path away from the root, and
multiply the corresponding increments. This follows directly
from the literal explicit B recursion for g_0. Choose the
orientation with leaves at the smallest indices. Disjoint
forests multiply their enumerators; grafting a common parent
appends a singleton last block, i.e. maps M_α to M_(α,1).
The single-vertex forest has M_(1).

These operations generate the full span of all M_α in
every degree. Induct on total degree, and within a degree
on the last part k. Last part 1 is the grafting case.
For k>1 multiply the known smaller-degree M_(β,k−1)
by M_(1). In the quasi-shuffle product, merging into the
last position gives M_(β,k) once. Every other term has
last part 1 or k−1 (insertion or an earlier merge). This
product rule is just partitioning the choices of indices
according to the location of the new singleton. Thus the
forest coefficient rows span all composition coordinates.
The M_α are linearly independent as polynomials on long
enough histories, by their distinct ordered exponent
patterns. Comparing these forest rows with (1) proves
independence of the leading degree-d vectors W_α g_0.

One can test independence of the elementary differentials
used in this comparison without an external analytic
assumption: for a selected rooted tree use one variable
per vertex, and take the component at a vertex to be the
product of its child variables (1 at a leaf). At the zero
input the component at the root picks out just that tree
shape, with a nonzero integer factor, by its recursive
derivatives. Finally g(y;h)=f(y)+O(h). Looking at the least
degree in any proposed dependence gives exactly the free
field leading vectors just shown independent, and induction
clears all degrees. This also justifies testing the literal
RK order by formal equality for all such polynomial fields.

## 2. Every nonlinear order test becomes an explicit moment

In the preceding notation E_γ=(id−γ h f)^−1 exactly:
its defining equation is the implicit Euler stage relation.
Consequently

    E_(γ+z)∘E_γ^−1 = id+z h f,
    h D_f = T_γ^−1 T′_γ,                                  (2)

where D_f differentiates functions in the direction f and
the prime varies τ, holding g fixed. The order of the
pullbacks in (2) is important. It follows either by
differentiating the first identity or by direct composition.
The exact formal flow is exp(h D_f) applied to the identity
coordinate function.

Compute it in the h-filtered noncommutative algebra of
the W_k. In T_γ^−1 T′_γ, the coefficient of a nonempty
word a of length l is

    (−1)^(l−1) a_l γ^(|a|−1).

Indeed expand the inverse of T_γ=I+Σ_(k≥1)γ^k W_k
geometrically; only the last letter comes from the
derivative. In the exponential, partition a word into
consecutive nonempty blocks. Each block contributes its
last part; choosing the preceding block endings produces
the elementary symmetric polynomial in the parts before
the final letter. On the identity coordinate only a last
letter W_1 can act nontrivially among nonempty words,
and it gives h g. Thus the coefficient multiplying
W_α g in the slope of the exact target is

    λ_α(γ)=Σ_(j=0)^l (−1)^(l−j) e_j(α) γ^(|α|−j)/(j+1)!,
    l=length α.                                            (3)

Here e_0=1; all γ powers are nonnegative and λ_empty=1.
The desired target is symmetric in the parts of α even
though the observed prefix evaluations are ordered.

It follows from (1) and independence that full classical
order p is equivalent to exactly the following moments:

    Σ_i b_i M_α(w_i) = λ_α(γ)       for every |α|≤p−1.      (4)

This is a characterization of the whole nonlinear rooted
system for prefix rows, not just of stability or univariate
quadrature. The full unrestricted prefix observation space
in this paid range has dimension 2^(p−1): the independent
compositions in the successive degrees. That dimension is
not a stage lower bound for the one prescribed target.

As a consistency check, with one block M_α(w)=binom(N,l)τ^|α|.
It cannot distinguish (3,1) from (2,2), but (3) gives
λ_(2,2)−λ_(3,1)=γ²/6. This is the first mismatch at order five.
The previously derived variable-spacing defect on a history
is exactly
2(M_(3,1)−M_(2,2)+M_(2,1,1)−M_(1,1,2)).
The last two target values agree by symmetry, so (4) pays
that defect at −γ²/3. The now-essential freedom is not an
extra field degree but time ordering of unequal increments.

## 3. Span of observations from at most s constant blocks

Fix degree d and length l. For a history taking N_b copies
of spacing τ_b in block b=1,...,s, with zero-count blocks
allowed, put S_i=Σ_(j≤i) a_j. Select counts k_b≥0 of the
chosen indices from the blocks, and write j_b=Σ_(v≤b) k_v.
Then

    M_α(w)=Σ_(Σk_b=l)
            ∏_b binom(N_b,k_b) τ_b^(S_(j_b)−S_(j_(b−1))).

Thus each term depends on at most s−1 interior prefix sums
of α. Conversely the coefficient of the product basis
element ∏ binom(N_b,k_b) τ_b^v_b, as a vector on the
compositions, is exactly the indicator of the chosen
prefix-sum values, including d=Σ v_b and l=Σ k_b.
Any choice of at most s−1 interior cut positions with
specified prefix sums is obtained by suitable k's and v's,
padding unused blocks. The indicated products are independent
polynomials in the N_b and τ_b. Evaluations therefore span
their coefficient rows: for all d≤P a finite certificate is
the tensor rational grid

    N_b∈{0,...,P},   τ_b∈{1,...,P+1},

where univariate Vandermonde in each variable separates
the polynomial degrees. Evaluate each history as the final
observation stage of its own actual branch. This proves
that the span of all s-block histories is **exactly** the
direct sum over d,l of functions depending on at most
s−1 selected interior prefix sums (finite linear sums
of such functions are allowed). If λ lies in that span,
a rational row basis and a linear solve give actual
b in Q(γ), not just formal parameters.

Set r=l−1 and L=d−l. The adjusted prefix coordinates
U_j=S_j−j are weakly increasing integers between 0 and L,
with endpoints U_0=0, U_l=L. Every function on this
simplex can be written using at most min(r,L) coordinates.
To see the bound L, view L extra units as ordered positions
P_a among the l parts. The indicator P_a=i is the
difference of the one-coordinate threshold tests
1_(U_i≥a)−1_(U_(i−1)≥a). Multiply these identities to
isolate any composition; each expanded term uses at most
L coordinates. The bound r is immediate.

Consequently all targets are attainable through d≤2s:
otherwise both r,L≥s would require d=r+L+1≥2s+1.
At d=2s+1 only r=L=s can fail. On a weakly increasing
simplex in r coordinates, the annihilator of all proper
coordinate marginals has a basis of alternating elementary
cubes with bases

    0≤a₁<...<a_r≤L−1,

i.e. sum over U=a+x with x∈{0,1}^r, signed by
(−1)^(r−sum x). These cubes lie in the simplex, and
every missing-coordinate marginal of one is zero.
Their lexicographically greatest vertices a+(1,...,1)
are distinct. To prove spanning, remove the mass at all
strictly increasing positive vertices of any zero-marginal
array in descending lexicographic order using these cubes.
If a boundary mass remains, take its lexicographically
greatest nonzero vertex. It has first coordinate 0 or
some coordinate equal to its predecessor. In that
coordinate, with all others fixed, no smaller value is
allowed and all greater values have zero mass. Its
marginal is therefore not zero, a contradiction.
For r=L=s there is exactly one such cube, not merely
one necessary relation among possibly more.

## 4. Exact evaluation of the critical relations

For r=s and l=s+1 write the compositions on a cube as

    α_i(x)=α_i^0+x_i−x_(i−1),
    x∈{0,1}^s,   x_0=x_(s+1)=0.

At d=2s+1 the unique cube has base (1,2,...,2) in the
part coordinates (equivalently U_j^0=j−1). Let Δ be its
signed alternating sum. For j<s, Δ e_j=0 by degree.
For e_s a monomial surviving Δ must choose each x once
from s of the s+1 adjacent factors. If factor i is
omitted, choices to its left are forced to have +x,
and to its right −x, giving sign (−1)^(s+1−i).
Thus Δ e_s is 1 for even s and 0 for odd s.

For the product e_(s+1), terms of total x-degree s
choose one constant α_i^0 and give the same signs.
Terms of degree s+1 must choose one variable twice,
from its two adjacent factors, and all others once.
Choosing x_j twice gives sign (−1)^(s+1−j); the other
choices are again forced from the ends. The sum of
these signs is 0 for even s and −1 for odd s.
The alternating sum of the baseline constants
(1,2,...,2) is 1 for either parity. Thus at d=2s+1,
Δ e_(s+1) is 1 for even s and 0 for odd s. In (3)
this gives

    Δ λ = 0                                           (s odd),
    Δ λ = γ^s(1−(s+2)γ)/(s+2)!                        (s even).

Combined with the complete marginal description this
proves both attainment and any obstruction at order
2s+2.

At d=2s+2 choose a different legal cube by adding 1 to
a baseline part. For odd s add it to the last part, so
Δ e_(s+1)=1 and Δ e_s=0. For even s add it to the
penultimate part, so Δ e_(s+1)=0 and Δ e_s=1. All parts
remain positive in the full cube, hence at most s-block
histories still annihilate it (each term of their
observation sees at most s−1 of the varying prefix
coordinates). The corresponding target values are,
respectively,

    γ^(s+1)/(s+2)!,      −γ^(s+2)/(s+1)!,

both nonzero for γ≠0. This rules out paying order
2s+3 for every such diagonal. Together with the previous
paragraph this gives exactly the stated maximum, with
no further real-root assumption. The attained maxima are
automatically exact because the next order is impossible
under the same block cap.

At γ=0 the argument gives no ceiling: (3) is zero unless
all parts are 1, so for each degree and length the target
is already constant. This is consistent with explicit
Euler extrapolation. It is not a strict nonzero-diagonal
case.

## 5. Two useful scope checks

**Natural versus independent output.** A single real branch
with its natural final output weights b_i=τ_i cannot attain
order four even with arbitrary signed increments. Its scalar
stability is

    R(z)=∏_i (1+(τ_i−γ)z)/(1−γz).

Order one through four of log R require
Στ=1, Στ²=2γ, Στ³=3γ², Στ⁴=4γ³. Real Cauchy–Schwarz then
would give 9γ⁴≤8γ⁴, impossible. If all increments are
nonnegative, even the cubic condition contradicts
Στ³≥(Στ²)^2=4γ² by Cauchy with Στ=1. These conclusions
do not hold for an independent signed b, which is exactly
the choice used in (4).

**A single ladder with independent readout is possible.**
Fix a jet cutoff p on stage slopes and choose the rational
increment alphabet {1,...,p}. Vandermonde in τ recovers all
W_j, j<p, as combinations of T_τ modulo h^p. Thus this
alphabet spans the full prefix module of dimension 2^(p−1).
From any already chosen history w, left multiplication
by T_w preserves this module and is invertible on it:
the pullbacks are filtered automorphisms, and an injective
self-map of this finite dimensional space is onto.
Future suffixes of length ≤p−1 suffice to span, by expanding
arbitrary products in T_τ−I and discarding p or more
positive-grade factors. Hence one can greedily append a
suffix of length at most p−1 whenever the observations
collected so far fail to span. At most
1+(p−1)(2^(p−1)−1) stages give a single universal ladder
with a rational prefix observation basis, chosen
independently of γ. Solve (4) for b; the solution can be
chosen polynomial in γ over Q using that same basis.
For exact order p at any γ, use the analogous span through
stage grade p and change just the first-unpaid moment for
α=(1,...,1) of length p by one. This is the strict tall
column; its change survives adding the diagonal because
all lower tall terms are unchanged. The single ladder
may need many blocks; it is not the sharp bounded-block
attainment proof above. None of these counts is close to
the verified unrestricted upper table at high order.

The [inverse-midpoint construction](INVERSE-MIDPOINT-PREFIX.md) gives a separate explicit polynomial-size family when no bound on the number of blocks is imposed.
