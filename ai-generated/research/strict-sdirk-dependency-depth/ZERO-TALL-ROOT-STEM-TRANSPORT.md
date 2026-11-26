# Leading rooted-tree span and exact stem transport of zero-tall corrections

Pure mathematical, common-diagonal SDIRK. Work over a characteristic-zero coefficient
field K (in particular a real algebraic field), with a fixed diagonal gamma in K.
The constructions preserve that field and diagonal. Stage clocks/signs, physical
depth and unrestricted near-table stage counts are not asserted. All statements
about finite jets are formal B-series statements; no numerical trials are used.

## 1. Actual stage model and an exact output invariant

Put H(Z) = h g_gamma(y+Z), where
    H(Z) = h f(y+Z+gamma H(Z)).
The prestate increment Z is O(h). Whenever Z is a constant-coefficient linear
combination of earlier H observations, H(Z) is one actual new strict lower-triangular
common-diagonal stage. The empty increment Z=0 is the prestate of the first stage
of any such base method. Using H from that stage again as a donor is not a new stage.

Use elementary trees F_bullet=f and
    F_[t_1,...,t_m] = D^m f[F_t_1,...,F_t_m],
with the symmetry factor already included in the coefficient of h^|t| F_t.
Let J act on these weighted series by h Df(y)[.]; it puts one unary root over
each tree and raises grade by one. Write pi_1 for the projection to unary-root
trees and pi_b for projection to trees with at least two root children.
The tall trees are the paths, including the single vertex. The root stem of
a nontall tree is the number of unary vertices above its first branching
vertex. In particular a branching-root tree has stem zero.

For any signed receiver combination C = sum_i w_i H(Z_i) define its net prestate
A_C = sum_i w_i Z_i. Taylor expansion at y gives exactly
    pi_1 C = J(A_C + gamma C),   coeff_leaf C = sum_i w_i.             (1)
Indeed the contribution of D^m f at this outer root has precisely m children.
The unary part only sees the aggregate physical increment Z_i+gamma H(Z_i).
This is in the independent formal rooted-tree basis, not an assertion derived
from testing on scalar f. If desired, the basis can be separated by a real
polynomial vector field for each target tree t: index coordinates by its
vertices, let f_v be the product of the coordinates of the distinct children of
v (constant 1 for a leaf), and evaluate at 0. A tree differential at coordinate
v is nonzero exactly when that tree is the subtree at v, by induction.

Let S=I-gamma J. If sum w_i=0, (1) is equivalently
    SC = pi_b C + J A_C.                                             (2)
In particular an affine-balanced receiver combination (A_C=0) has SC supported
on branching roots. On every branch-root tree B, its successive unary
coefficients are C_(J^l B)=gamma^l C_B. All its tall coefficients are zero.
This holds for arbitrary prestate dependency on earlier stages, different
anchors, arbitrary signed mixing, and lower-grade cancellations. As S does
not change the first nonzero homogeneous vector, no such mixing can expose
a unary-root leading tree. For a finite paid jet all the identities only
require the net prestate at one grade less.

A frozen finite difference uses the same computed increments V_j in every
stencil prestate, e.g.
    Delta_V^k H(Z) = sum_{a=0}^k (-1)^(k-a) binom(k,a) H(Z+a V).
Any iterated difference of total arity at least two has sum w_i=0 and A_C=0
exactly: it annihilates the constant and linear polynomials of the stencil
parameters. This applies even if the V_j are complicated nonlinear earlier
directions. The arity-one response U(V)=H(Z+V)-H(Z) instead has A_U=V. If V
is exactly zero on every affine vector field, so is U(V); for affine f the
implicit H is affine in Z. If V = h^r v + O(h^(r+1)), then
    U(V) = h^(r+1) Df(y)[v] + O(h^(r+2)).                            (3)
It uses one new stage when H(Z) is already known.

## 2. The exact natural-order mixed-forward palette

Let E_a(y)=y+aH(0) denote the map y -> y+a h g_gamma(y) (with H relative to
its input y), and let T_a act by composition with E_a. For any a in K not
zero, the actual r-stage forward donor
    V_r = a^(-r) (T_a-I)^r id
has V_r=h^r G_r+O(h^(r+1)), where G_r=D_f^r id and D_f psi=Dpsi[f].
This follows by expanding T_a-I=a h D_f+O(h^2) as a formal operator.
The practical construction evaluates only E_a^0 y through E_a^(r-1) y as
prestates. E_a^r y is already an affine combination of the observations,
and the coefficients of y cancel from the difference. One R-stage ladder
supplies every V_r for r<=R.

G_r has coefficient 1 on the tall r-tree and positive coefficient
    r! / (sigma(t) t!)
on every r-tree t. Here t! is the product of the subtree sizes and sigma(t)
the tree automorphism order. One proof uses the recurrence G_(r+1)=DG_r[f]:
differentiating amounts to attaching the next leaf at each vertex. The
result counts increasing vertex labels up to automorphisms. There are
r!/t! labelings on a fixed vertex set (multinomial interleaving at the root),
the automorphism action on labels is free, and the increasing order on a
path is unique. For the arguments below only the distinguished tall
coefficient and absence of other paths are needed.

For distinct available directions V_j=h^(r_j)v_j+O(h^(r_j+1)), with
multiplicities k_j>=1 and m=sum k_j, the mixed stencil
    (product_j Delta_(V_j)^(k_j)) H(Z)
has leading grade n=1+sum_j k_j r_j and leading vector
    D^m f(y)[v_1 repeated k_1 times, ..., v_s repeated k_s times].    (4)
Here "leading" means the indicated first possible grade even if the
displayed vector happens to be zero. In the Taylor expansion with formal
stencil parameters, every lower multidegree is killed. The first surviving
one is (k_1,...,k_s), and its factorial denominator is canceled by the
finite differences. Evaluating derivatives at the anchor Z=O(h) rather than
at y and using H/h instead of f only changes higher grades.

With only the single direction G_r per size, distinct unordered lists of
child sizes have disjoint root support. In the raw tree basis the line for
a size partition lambda is the graft of those G_r's (including the
multinomial factors for repeated sizes); its all-tall-child entry is 1.
If p_par(j) denotes the number of integer partitions of j:

* Same-direction order-m differences, m>=2, span dimension d_div(n-1)-1
  at grade n>=2 (one rectangle r^m for each divisor m>=2).
* All mixed forward-spine differences, m>=2, span dimension
  p_par(n-1)-1 at grade n>=2 (all partitions except the one-part partition).
* Adding only unary prolongations (3) above these first branching stencils,
  without refeeding a nonlinear direction into a later branch, yields
  sum_{l=0}^{n-3} (p_par(n-l-1)-1) at grade n>=3. Stem l and first
  branching partition distinguish the lines.

These are dimensions for the natural leading grade of each named recipe,
not dimensions of their full filtered span after arbitrary cancellations.
In contrast (1)-(2) are exact and do control such cancellations.

More generally if the available leading directions of size r span E_r of
dimension e_r in the free r-tree space, the natural-order branching span is
the direct sum, over lambda with at least two parts, of the embeddings
    tensor_r Sym^(multiplicity_r(lambda)) E_r
by grafting. The root partitions are independent. Inside each partition
the map is injective: symmetric products of the full r-tree bases correspond
to distinct multisets of child trees, and a subspace inclusion extends to
a basis. Grafts of available direction lists span that image by
multilinearity. In particular its dimension is
    [x^(n-1)] product_{r>=1} (1-x^r)^(-e_r) - e_(n-1),  n>=2.
One can use the partitionwise version as a residual test over the actual
coefficient field rather than treating all shapes from a given size as
separately available.

Grade 3 has exactly one nontall direction [bullet,bullet]. At grade 4, the
two branching-root directions [tall_2,bullet] and [bullet,bullet,bullet]
are available to mixed stencils; unpolarized stencils have only the latter.
The unary-over-fork t=[ [bullet,bullet] ] is unavailable to *any*
affine-balanced leading correction by (2), even after arbitrary cancellations.
Appending (3) to the fork supplies it with one further receiver.
This really can be the first defect at an actual method: from any order-four
common-diagonal base (at that same diagonal), append a nonzero multiple of
this unary-over-fork output. The resulting base retains order three and all
its scalar/tall coefficients, but its order-four residual has a nonzero
unary-over-fork coordinate. No affine-balanced correction can fix it while
retaining the paid grades. More generally at paid grade 4, if grade 3 is itself
being corrected, the balanced rule requires
    R_(unary-over-fork) = gamma R_fork
for the residual in these coordinates.

The first-fork palette with unary prolongations has its first separate
deficiency in grade 5: in the 3+1 root block the two child choices tall_3
and fork_3 occur with equal coefficient, because G_3=tall_3+fork_3.
There are 7 lines in the 8-dimensional nontall space. Feeding a fork donor
and a singleton into a second difference removes the deficiency. The
same-size line relation is not a universal invariant like (2); lower-order
stencil cancellations can themselves manufacture nonlinear feeders.

## 3. A universal leading basis with sparse actual stencils

Index the following recipes by nontall trees t and build all required child
directions first. A child that is a tall r-tree is replaced by V_r above
(or any available size-r direction with tall coefficient 1). A nontall child
uses its recursively constructed correction. At a branching root take
(4), grouping repeated equal children. At a unary root use (3) on the
nontall child. Call the physical output C_t.

Inductively C_t is exactly zero for affine f: branching receivers have
A_C=0 and zero sum of weights; unary receivers have a zero-affine net
prestate. It starts at grade |t|, has coefficient 1 on t, and all other
leading terms have strictly more leaves. Indeed a substitution of any other
tree for a tall child has more than one leaf, and substitutions in nontall
children strictly increase their leaves by induction. Child sizes, and the
stem at the root, are unchanged. Grafting simply adds child leaf counts
for a non-leaf root. Hence ordered by leaf count, the leading coefficient
matrix is unitriangular (also within each root-stem and first-branch
partition block). There is one recipe per nontall tree, which is exactly
the number of leading vectors needed for a fixed linear dictionary spanning
that homogeneous space. Restricting to branching roots gives all
branching-root vectors while exactly maintaining A_C=0.

If only a few of the basis recipes are used, build the closure F of their
indices under nontall subtrees, sharing each made direction. Let R be the
largest size of a needed tall child. The common baseline H(0) is shared.
With no donor in an existing base, the conservative total is
    max(1,R) + sum_{u in F} (product_v (k_(u,v)+1) - 1),               (5)
when there is at least one correction. k_(u,v) is the multiplicity of
the distinct child v of u. Each summand is the number of nonbaseline
receivers in that one local stencil. Unary responses cost one. An m-fold
identical-child stencil costs m, not 2^m. Actual coincidences and prior
available donors can only reduce (5). There is no construction here of a
global parameter grid to meet unrelated tree orders.

## 4. Sharp stem hierarchy, including delayed cancellations and finite jets

Define response budget zero to mean a zero-sum receiver combination with
net prestate zero. At budget d>=1 allow zero-sum receiver combinations whose
net prestate is in the linear span of already realizable budget-(d-1)
outputs. The budget counts the recursively exposed **net prestate at the
output**, not every internal stage or path. For example, a balanced stencil
can use arbitrarily elaborate earlier donors yet is budget zero. Linear
combinations can be made by taking the union of their acyclic stage lists.
All budget outputs are exactly zero on affine f.

If C has budget d, then
    S^(d+1) C is supported on nontall trees of root stem <= d.         (6)
For d=0 this is (2). For the induction, apply S^d to (2). The term
S^d pi_b C has stem at most d, since S is a polynomial of degree one in J.
The second term is J S^d A_C; S and J commute, and the induction hypothesis
gives stem at most d-1 before the extra J. This proof holds for full series
and after truncating to any paid order. In particular it permits arbitrary
cancellation of lower terms before looking at the first nonzero grade.

Conversely, every desired homogeneous nontall vector supported on stem
<=d is a leading vector of this class (or zero). The recipes C_t of
Section 3 have budget at most their root stem by (2)-(3), and their
unitriangular basis preserves stem. Therefore if T_n is the number of
rooted unlabeled n-trees, the sharp grade-n leading dimension, n>=3, is
    sum_{l=0}^{min(d,n-3)} (T_(n-l)-T_(n-l-1))
      = T_n - T_(max(2,n-d-1)).
The difference counts branching-root trees because attaching a unary root
bijects with all smaller trees. There is no grade below 3 in this class.
The first obstruction at fixed d is J^(d+1)[bullet,bullet], of grade d+4.
It is genuinely realizable as a residual on an already accurate base of
that grade, by perturbing the base with the corresponding d+1 responses.
Thus "one more outer response" has a sharp algebraic role, but not a general
lower bound on SDIRK stage counts, or even a new-stage lower bound if the
base already supplies a deep-stem donor.

For any finite desired output jet R through p there is an exact criterion:
    realizable through p at budget d
      iff  S^(d+1)R has no tall terms and no stems >d (through p).    (7)
Necessity is (6). For sufficiency take the first nonzero grade of the
remaining difference. S^(d+1), being triangular with diagonal 1 across
grades, has the same vector there. Match it by the leading basis of the
budget, subtract the full achieved jet, and continue. This uses finitely
many local recipes and keeps the constraint at each subtraction. Equivalently
choose the suitable dictionary by increasing grade, then leaf count. With
gamma nonzero, (7) says that along each nontall stem chain J^l B the
sequence gamma^(-l) R_(J^l B) has zero (d+1)-st difference in the paid
range. In coordinates, the equation for l>d is
    sum_{j=0}^{d+1} binom(d+1,j)(-gamma)^j R_(J^(l-j) B)=0.
There is no such count if one simply introduces unrestricted net prestate
sources and calls them budget-zero. With an actual freely supplied prestate
space U through grade p-1, the exact alternative is
    S R belongs to B_0 + J U through p,                              (8)
where B_0 is the branching-root jet space. This is necessary by (2), and
sufficient by taking one response on a donor in U realizing the required
net prestate, then using the budget-zero construction for the remaining
jet. The unique required net prestate is
    J^(-1) pi_1 R - gamma R, through p-1.
If these U donors are only zero-affine through the paid band, the result
preserves that band rather than asserting unchanged higher tall coefficients.

## 5. Pairing with an actual base; no added field extension

Let an s-stage base table (A,b) of the same diagonal have ordinary order
P, let c=A1, and let Phi_t be its normalized stage elementary weight:
    H_i = sum_t h^|t| Phi_t(i) F_t / sigma(t).
If P>=2r-1, base observations supply a tall-triangular V_r, in fact the
exact leading G_r, without a new stage. Choose a rational polynomial Q_r
of degree r-1 with
    integral_0^1 Q_r(x) x^j dx = 0 for j<r-1,
    integral_0^1 Q_r(x) x^(r-1) dx = (r-1)!.
The scaled monic orthogonal polynomial works (nonsingular rational moment
matrix, and its leading moment is its strictly positive square norm).
For q=r-1 an explicit choice is
    Q_r(x)=(-1)^q (2q+1)!/(q!)^2  *  (d/dx)^q [x^q(1-x)^q].
Repeated integration by parts and the elementary beta integral verify the
normalization, including q=0.

Use w_i=b_i Q_r(c_i) and V_r=sum_i w_i H_i. Attaching a new leaf a times
at the root of t multiplies Phi_t pointwise by c^a, and changes t! to
(|t|+a)t!/|t|. For |t|<=r and every 0<=a<=r-1 the enlarged condition
is paid. Therefore
    b^T Q_r(diag c) Phi_t
      = |t|/t! * integral_0^1 Q_r(x) x^(|t|-1) dx.
Thus all grades <r vanish and grade r is exactly G_r. This includes trees
with only one vertex (and no assumed stages beyond the original base).
If r0=floor((P+1)/2)>=1, larger tall-triangular directions can be obtained by
applying (3) to V_(r0) successively at the shared baseline. Their tall
coefficient is still one, and other terms are nontall: they need not be
the original G_r when r>r0. With an existing first-stage baseline and
order P>=1, the initial term in (5) can accordingly be replaced by
max(0,R-r0). The exact fixed-forward palette formulas use G_r, whereas the
universal unitriangular proof needs only tall-triangular directions.

Other donor reuse can be certified by linear algebra with actual stage
profiles. A readout w annihilating all Phi_t of grade <r has leading
r-profile (w^T Phi_t/sigma(t))_|t|=r. For a readout also to annihilate
every affine response it must annihilate the tall Krylov space
span{1,A1,...,A^(s-1)1}; with only paid p, powers through p-1 suffice.
Cayley-Hamilton proves the full assertion, and on affine f these are
precisely its tree coefficients. For example if all subdiagonal entries
of A-gamma I are nonzero, the Krylov space is already all K^s (successive
powers of the strictly lower part have their first nonzero entries one
position later), so there is then no nonzero exactly zero-affine readout
of base observations alone. This does not prevent a new balanced receiver,
and paid-only readouts may still exist. It prevents assuming ready-made
nonlinear donors for free.

Finally, for an actual base of order n-1 whose stability series matches
through p, the order-(n-1)-to-p residual has no tall terms. The general
dictionary can correct it through p without changing the base stages,
its common diagonal, coefficient field, or any tall coefficient (choose
d>=p-3). Weights and directions are constants over K; triangular solves
and local integer stencil nodes adjoin no roots. If the base scalar
stability series first fails at p+1, an exactly zero-affine correction
retains that failure and the resulting order is exactly p; otherwise only
at least p is automatic. Scarce-stage use requires a sparse actual
residual, or sufficient existing donor span, assessed with (4), (7),
(8) and the support count (5). The universal span is not a uniform
near-table stage bound and supplies no improvement to the unrestricted
published upper table by itself.

The depth counted here is the number of exposed net-prestate responses in the correction model, not the physical dependency depth or the total number of added stages. The natural palette counts refer to its specified leading stencils, not the larger span after arbitrary cancellations.
