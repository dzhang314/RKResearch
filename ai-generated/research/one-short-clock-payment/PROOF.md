# Same-clock payment one order short

Source-only mathematics and a first-flight Lean candidate against the reviewed local main
`7d5ba756fcf30d2e970ec5579bb185079b83384b`. No Lean build or axiom output is claimed.

## One genuine mixed test

Let the actual tableau over a characteristic-zero field satisfy the reviewed
`HasOrder p A b`. Write c=A1. On stage vectors define

    S(f,g)=sum_i b_i [f_i (A g)_i + g_i (A f)_i] - (sum_i b_i f_i)(sum_j b_j g_j).

This is literally the reviewed symmetric bilinear map `symplecticPair`, not an
assumption of full symplecticity. For polynomials F,G with deg F+deg G+2 ≤ p,
S(F(c),G(c))=0 by `symplecticPair_zero_on_paid_tree_spaces` and
`evalNodes_mem_treeSpace`. For a physical clock t write s_t=1_{c=t},
B_t=sum_{i:c_i=t} b_i, M_uv=sum_{i:c_i=u}sum_{j:c_j=v} b_i A_ij. Thus
D_uv=S(s_u,s_v)=M_uv+M_vu−B_u B_v, including both directions, the same-stage
diagonal, and strict same-clock edges. Grouping and linearity give

    sum_{u,v} D_uv H(u,v)=0                  (total degree H ≤ p−2).

Proof: expand H in monomials and apply the paid pair separately to each. No
rectangular bidegree payment is required; symmetric H suffice. The hypothesis
for an empty/nearly empty budget should be written monomial by monomial as
i+j+2 ≤ p, avoiding natural subtraction ambiguity.

## What one missing order leaves

Choose ANY finite set T of n≥2 distinct labels (not necessarily a physical or
output cover). For t in T set q_t=prod_{x∈T, x≠t}(X−x), k_t=q_t(t)≠0, and
h_t=q_t(c)−k_t s_t. This last vector is exactly the reviewed
`hiddenMask A T (visibleSelector T t)`. It can be nonzero even if all off-T
aggregate output weights vanish. Put

    J_t=2 k_t S(s_t,h_t)+S(h_t,h_t),
    W_t=k_t² D_tt+J_t=S(q_t(c),q_t(c)).

For a≠z in T the monic top terms cancel exactly:

    q_a−q_z=(a−z) prod_{x∈T, x≠a,z}(X−x).

At p≥2n−1 the pair (q_a−q_z,q_v) costs at most (n−2)+(n−1)+2=2n−1.
Thus S(q_a(c),q_v(c))=S(q_z(c),q_v(c)) for each v in T. Symmetry makes
this entire corrected matrix constant, say Lambda. In particular

    k_a² D_aa+J_a=k_z² D_zz+J_z;
    k_a² D_aa=k_z² D_zz  if and only if  J_a=J_z.

Neither correction must be zero. Equivalently one can use the single
symmetric test formed from (q_a−q_z)(X)(q_a+q_z)(Y). When T covers all
physical clocks, J=0 and D_uv=Lambda/(k_u k_v), at most rank one. At
p≥2n full double selection pays; the corrected matrix, not necessarily
the physical matrix, is zero. For a mixed selector support one may prove
physical equality with a *single* combined leakage, not two
independent vanishings.

## A physical multiplicity that actually follows

For a lower triangular A ordered by physical stages, put

    d_t=sum_{i:c_i=t} b_i A_ii,
    E_t=sum_{i<j, c_i=c_j=t} b_j A_ji,
    V_t=k_t²(B_t²−2d_t)−J_t.

The chronological hypothesis implies M_tt=d_t+E_t. The mixed identity gives
2(k_a² E_a−k_z² E_z)=V_a−V_z. Consequently V_a≠V_z forces some actual
i<j of equal clock, at a or z, with b_j A_ji≠0. The comparison includes
the exact correction difference. For strict ERK plus J_a=J_z, unequal
(k_a B_a)² and (k_z B_z)² suffice. On a common diagonal gamma, replace
B_t² by B_t(B_t−2 gamma). No condition on pairings of omitted stages is
hidden inside a cover hypothesis.

More generally all physical labels with no such edge belong to a single
level set of V. For n genuinely occupied labels the union of their fibres
therefore has at least 2n−max_v #{t∈T:V_t=v} stages. This is a conditional
distribution statement. At the fully paid order and J_t=0, each strict ERK
site with B_t≠0 must have a same-clock weighted strict edge separately;
the corresponding common-diagonal condition is B_t(B_t−2 gamma)≠0. None
of this is an unrestricted stage-bound change.

## Optimal isolation from known support

Let U be the finite set of unordered pairs which *may* carry nonzero D,
including the target (a,a). For symmetric polynomial tests of degree ≤d,
form evaluation rows at U. A universal deduction of D_aa=0 from these tests
and that support is possible exactly when the row of (a,a) is outside
the span of the other rows. This is exactly the existence of a polynomial
with value 1 there and 0 at the other pairs. If no such polynomial exists,
a nontrivial linear relation with coefficient 1 at the target supplies a
formal symmetric defect annihilating all tests (give each off-diagonal
orientation half its unordered atom). This converse does not assert that
arbitrary defects are realized by actual tableaux. One may use symmetric
monomials, or powers of x+y and xy with degrees 1 and 2 respectively.

If the only off-target possibilities are r different pairs {a,h}, the
symmetric mask prod_h (X+Y−a−h) has value prod_h(a−h)≠0 at (a,a) and kills
all other permitted pairs. Degree r is optimal by restriction to Y=a. On
an entire n-clock square, the necessary degree is 2n−2: the separate
selector achieves it, and w_u w_v with w_u=1/k_u annihilates every
monomial of degree ≤2n−3 while w_a²≠0. The annihilation follows by
leading-coefficient interpolation on T.

## Actual sharpness, not an extrapolation from that linear model

For n≥2 over the real algebraic field take the left Radau nodes T: zero and
the n−1 roots of the monic polynomial pi orthogonal for the weight X on
[0,1]. Positive definiteness and the sign-change argument give n−1 distinct
interior roots. Divide a polynomial of degree ≤2n−2 by X*pi and integrate;
orthogonality kills the quotient term. Thus the weights B_t=integral l_t
of the normalized Lagrange basis integrate that degree, and exactness on
l_t² gives B_t>0. The next degree fails on X*pi², strictly positive in
integral and zero at all nodes. Define the dense collocation matrix
G_uv=integral_0^u l_v.

The actual tree-order argument in the checked main's research note
`ai-generated/research/causal-profile-reduction/hidden-clock-moment-ladder.md`,
section 4, applies with p=2n−1: the stage profiles are pure through tree order
n+1; in a paid tree at most one child has order ≥n+1. Push that child's
matrix action through the tested integral by the Lagrange/primitive identity
there, reduce the child by induction, and return by formal integration by
parts. Every integrated degree is ≤p−1. More explicitly, if its order is j
and the other children's total order is m, the input test becomes P=F X^m,
deg P≤p−j−1. The adjoint identity needs deg P+n≤p−1; replacing the child
needs (deg P+1)+j≤p; the restored primitive product has degree ≤deg P+j≤p−1.
Small children use the literal product of pure stage actions. Setting F=1
therefore proves all rooted-tree conditions, not only bushy quadrature.

Use explicit causal banks: bank 0 has zero rows; bank k≥1 uses G from
bank k−1 only; weight only the final bank, at depth p. Induction on the
tree order shows that bank k agrees with the dense response on tree order
≤k+1. All physical clocks lie in T because 0∈T; all weighted pairs are
exactly those of B_u G_uv. But G_0v=0, so 2M_00=0≠B_0². This proves actual
failure of individual diagonal payment at p=2n−1 with *no* hidden clocks.
For n=1 use single-stage explicit Euler. The first unpaid monomial fails
because all lower degrees agree and X*pi² is monic. This is not a claim
about a stage-minimal realization or an interval/invariance obstruction.

## Independent small rational checks

`check.py` computes the actual strict matrices, grouped defects and hidden
terms with exact fractions; the rooted-tree conditions through orders 2
and 3 are enumerated explicitly (respectively the two and four conditions).
It also checks the next bush fails. Four cases discriminate:

* signed4: exact order 2; at the sole live clock the paid self defect is
  zero, while S(s,h)=1 and S(h,h)=−2 cancel only jointly.
* heun3: exact order 3; both live fibres singleton and their scaled defects
  differ; J=(0,2/9) restores corrected equality. Merely covering aggregate
  weights cannot replace J_a=J_z.
* joint5: exact order 3; J_a=J_z=−2/9, strictly weaker than two zero
  conditions even on an actual causal tableau.
* radau4: exact order 3; no hidden stages at all and neither physical
  diagonal paid. This is the smallest-order nontrivial full-grid case,
  not a minimum-stage assertion.

The first-flight Lean source and typed probes have not been elaborated.
The fraction checker validates these examples, not the general Lean source.
