# Fixed scalar coordinates throughout the equality-chart tail

**Actual tableau theorem.** Let m=7 or 8, and let A,b be any lower
triangular tableau of classical rooted-tree order at least 2m over
any characteristic-zero field with exactly 3m−3 physical stages.
Write E_j for the span of the stage elementary weights through grade
j, F_j for its genuine numerical zero-profile defects, and c for the
original tableau clocks. Then there is a clock-invariant core U of
dimension two or three, and a normalized physical vector w with
r=4−dim U (one or two), such that

* F_j=U plus the span of w,cw,…,c^(r+j−6)w at 5≤j≤m;
* E_q consists exactly of H(c)+u+w Q(c), where deg H≤m, u∈U,
  and deg Q<r+q−5, at m≤q≤2m−3. The parameters are unique.
* There are at least r+2m−8 distinct clock values on rows where w is
  nonzero, irrespective of repeated physical nodes. U is the largest
  clock-invariant subspace of F_m, and a single-site part of w cannot
  belong to U unless that part is zero.

This is an unconditional structure theorem *at the indicated equality
counts*, not by itself an exclusion of those counts. For m=9,10 the
tail machinery also applies if the corresponding low-grade chart is
given; the two-order flagship does not assume that chart at m=7,8.

## Why the scalar block stops at degree m

The previously verified quartic reductions are invoked on the actual
p14 and p16 arrays. They give dim F₅=4, dim F_m=m−1, and a largest
invariant core U with 2≤dim U≤3 already inside F₅. Strict defect growth
forces dim F_j=j−1 for 5≤j≤m; if F_j were invariant on an interval edge
its outgoing two-moment rank gain would contradict this unit increment.
The existing normalized one-escape theorem and flag staircase therefore
give the same U,w from grade five to m. Maximality at grades 5 and m
identifies the two potentially different cores.

The true, output-active terminal cardinal e_t is the sum of b_t G(c)
and f∈F_m, with b_t≠0, c_t=1 and G the signed Lobatto polynomial. Thus
f−Cf=b_t D(c), for D=(X−1)G. In particular D(c) lies in F_m+C F_m.
Since deg D=m+1, *every* polynomial of degree at most m+1 is a degree
at most m polynomial plus a scalar multiple of D. This is proved by
cancelling its leading coefficient, without a monic convention.
Consequently C acting on the fixed degree-m scalar block only needs
one increment of the genuine defect orbit, not a new scalar degree.

At the midpoint every actual elementary-weight column has a bounded
polynomial representative modulo its genuine defect. For m≤q<2m−3,
the complementary reverse-word space is the exact annihilator of E_q
and is not invariant under 1−C; the terminal reverse line is handled
by its already established nonlocality. If E_q were C-invariant, its
annihilator would be (1−C)-invariant by the transposed row pairing,
a contradiction. Since the actual rank is m+q, the only one-dimensional
increment is E_(q+1)=E_q+C E_q. Combine the scalar absorption just
proved with the unchanged core to extend the very same head by one
power at every step. This includes q=2m−3 with no exceptional extra
term and no high-grade separation assumption for F_q.

Finally map two finite coefficient vectors and one core vector to the
actual sum H(c)+u+wQ(c). Its range contains E_q by the stage-space
identity and the previously proved clock-polynomial representation
of a head orbit. The parameter count is exactly
(m+1)+dim U+(r+q−5)=m+q=dim E_q. Rank-nullity hence gives zero kernel
and exact range. If fewer head sites existed, their nonzero monic
nodal polynomial could be a head coefficient of allowed degree and
would evaluate to zero after multiplication by w; injectivity forbids
this. This counts numerical knots, not physical coordinates.

## Lean API

Namespace RKCert.Paired.Terminal. Start with fixed_forward_tree_head,
or midpoint_head_fixed followed by MidpointHead.tree_polynomial_iff
and MidpointHead.physical_relation_trivial. The parameter map is a
linear map with a separately exported injectivity/onto-E_q theorem,
MidpointHead.exact_tree_parameters. The exact effective-site count
is MidpointHead.physical_head_site_bound. The separate interface
no_shifted_lobatto_factor_mask applies the previously proved physical
head pivot without charging a grade for a clock multiple already paid
inside the genuine defect space.

The construction reuses Mathlib rank-nullity, dimension of finite
function spaces and products, submodule finite-rank equality, and
Lagrange nodal polynomials. All sample, count and closure equalities
relate to the actual original array. No finite-field reduction,
determinant enumeration, positivity order, or stage deletion is
introduced by this packet.
