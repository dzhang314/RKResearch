# Physical field descent and auditable split certificates for ancestor widths

**Separate mathematical track.** This keeps the same adjacent-level
strict SDIRK format, diagonal, widths and allowed-height all-tree
transport as the ancestor-hull constructions. It does not import a
field obstruction from discriminants or turn a real-split certificate
into a claim of splitting over a number field.

## 1. The local hull gate is necessary for actual adjacent tableaux

Let K have characteristic zero, fix order p≥2 and levels h=0,...,D
with 1≤D≤p−1, and prescribe a common diagonal γ. The strict part
B=A−γI only taps the preceding level, and output b is supported on
level D. At a level h put d=D−h, s=p−d, and let r be its allowed width.
For r<s put b_cut=s−1−r. Write c=A1, y=1−x, and let T=V−γ id with
V the zero-origin primitive in y. The local test space is

    C(d,b_cut) = span { M^(k_d) T M^(k_(d−1)) ... T M^(k_0) 1 :
                        k_i≥0, sum k_i≤b_cut },

where M multiplies by y. Its known descriptions are

    C(d,b_cut)=T^m K[y]_(≤ν),  m=(d−b_cut)_+,  ν=d+b_cut−m (γ≠0);
    C(d,b_cut)=y^d K[y]_(≤b_cut)                           (γ=0).

Suppose an actual tableau over K has order at least p and at
most r stages on this level. Take a monic degree-r split hull H
containing all the distinct clock labels 1−c_i of those stages.
One can instead keep only labels eligible for an actual strict
route to terminal output. If fewer than r are present, append
distinct arbitrary elements of K to reach r; K is infinite.
Then for every W in C(d,b_cut),

    ∫₀¹ H(y) W(y) dy = 0.                                  (A)

To prove this, let Y be actual coordinatewise multiplication by
1−c. The physical scalar
bᵀY^(k_0) B Y^(k_1) ... B Y^(k_d) H(Y)1 vanishes, since its
unexpanded row only reads the fixed level and H is zero on all
its eligible labels. Same-clock strict edges are not erased.
After expanding B as A−γI and powers of 1−c as c polynomials,
every term is a literal rooted output of order at most

    1+d+r+sum k_i ≤ p.

The last multiplier is on the same bottom receiving root as H;
each c factor adds a leaf and each A adds a new parent. Substituting
the paid exact-flow values c↦x, A↦I_x (zero-origin primitive),
bᵀ↦∫₀¹ dx and moving the d copies of I_x−γ id by adjointness
therefore produces (A). The bottom multiplier is included. This
argument uses actual physical stage clocks, not interpolation
profiles or one changed layer in isolation.

Conversely, prescribe a terminal q-node rule with q≤p, exact
through degree p−1, and assume the shifted exact-flow target is
zero on every paid tree taller than D. For every positive internal
level with r<s, choose an independently split monic H of degree r
satisfying (A); when r≥s any distinct sites suffice. The actual
cardinal rows (apply I_x−γ id to each preceding cardinal and
evaluate at the receiving site) realize order at least p over K.
The initial singleton needs only its constant profile and has
physical clock γ. The terminal rule has only its ordinary moment
requirement; e.g. reusing the terminal hull at unchanged internal
width q is safe by exact quadrature on H·W of degree ≤p−1.

Indeed the existing ancestor-first all-tree transport removes
each interpolation difference F−ρF=H·E. At distance d, the
degree budget of the quotient E plus all sibling factors is
≤b_cut; moving the d integrations to the test side makes the
scalar change a member of (A). This is the literal all-tree
telescoping argument, not merely the words used to prove
necessity. Restore γI by edge contractions. Taller paid trees
are zero on both sides by the stated height condition. Thus in
this format the independent split-hull conditions characterize
realizability at the width caps through order p, not just a
sufficient repetition of one interpolation recipe. Terminal
weights, height and exact-order witnesses are handled as stated,
not asserted for an arbitrary other topology. The D=0 order-two
exception is the separate midpoint singleton.

## 2. Use one hull per width: a genuine field saving

Fix p,γ and a physical width r which recurs on positive levels.
Where the gate is nonempty, the quantity d+b_cut=p−1−r is constant.
For γ≠0 write it as L. At an earlier level m is larger, so
T^m K[y]_(≤L−m) is contained in the later test space:
factor out the later power of T and use that each T raises
degree by at most one. At γ=0, y^d K[y]_(≤L−d) is similarly
contained in the later space just by factoring out its smaller
y power. Unconstrained earlier levels need no inclusion.

Hence choose the hull at the **latest level using a given
width** and reuse it at all earlier positive levels with that
width. If it is the terminal width, simply use the terminal
hull. The profile still has every physical stage on its own
level; equal clocks across levels cause no problem. This applies
to arbitrary attained profiles, including nonconsecutive
repetitions or a mix of old and newer cuts.

For the nonzero-diagonal higher-budget profile
r(s)=min(q,floor((2s+1)/3)), q=ceil(p/2), the nonterminal
uncapped cuts have r<s (apart from the initial convention).
In the early region where the higher-budget gate is used,
b_cut≤d and n=dim C=2b_cut+1. The repeating pattern is

| s | r before the cap | b_cut | n | free root count r−n |
|---|---:|---:|---:|---:|
| 3j | 2j | j−1 | 2j−1 | 1 |
| 3j+1 | 2j+1 | j−1 | 2j−1 | 2 |
| 3j+2 | 2j+1 | j | 2j+1 | 0 |

The same width occurs at 3j+1 and 3j+2, so the free-two layer
may use **the later saturated hull**, adding no field at all.
For every uncapped repeated odd width the later cut is present
unless the selected partial profile actually changes its width;
the general latest-width rule covers that partial case too.
The only remaining nonsaturated cuts in the full profile are
the even widths 2j, one parameter each. The one-moment cases
are already split over K by the rational imposed-root recipe
(or the nonzero singleton denominator when r=1). Thus after
reusing equal widths, only even widths ≥4 can require a new
nonsaturated field computation in the full nonzero profile.
For real-embedding ranges giving Haar, impose a rational
root there and adjoin only the degree-(2j−1) residual roots.
This provides an unconditional finite real-algebraic upper
extension throughout those ranges with unchanged widths.

At a saturated cut n=r whose degree-<r moment pairing is
invertible, (A) uniquely determines H. Its splitting field is
compulsory for **every** actual tableau of this width in the
adjacent terminal topology. Padding also shows all r effective
labels must be distinct: if fewer occur, two different choices
of extra roots would give different monic solutions. Consequently
the field generated by γ, the prescribed terminal clocks, and
all these saturated root sets is an unconditional necessary
subfield (provided the cut determinant is nonzero). This is
an inclusion argument, not a calculated degree lower bound.
Width-increasing alternatives and different topologies are
outside the claim.

## 3. Exact least field for the whole zero-diagonal matched profile

There is further unconditional sharing for γ=0 at exact depth
D=p−1 and widths r(s)=ceil(s/2). For s=2j the saturated gate has
r=j, b_cut=j−1, d=p−2j, so the unique monic hull P_j is the
degree-j Jacobi hull for the positive weight y^(p−2j) on [0,1].
All j roots are simple interior. At the following odd
s=2j+1 the weight exponent decreases by one and the width
increases by one; use the hull yP_j. The added root is the
rational endpoint y=0, disjoint from the other roots, and

    ∫₀¹ y^(d−1) (y P_j) Q dy = ∫₀¹ y^d P_j Q dy = 0
    for deg Q<j.

The initial layer stays the singleton leaf level. Thus all
unsaturated internal layers can be built with *no additional
extension beyond the compulsory saturated fields*. If the
terminal rule is prescribed Gaussian add its splitting field
to this compositum; cardinal weights already lie in that
actual terminal field.

If the terminal rule is free and p is even, the last saturated
hull is the ordinary Gaussian one and is compulsory. If p=2j+1
is odd, use yP_j as the terminal hull as well (the preceding
degree-j hull has weight y). Euclidean division gives quadrature
exact through degree 2j=p−1; the cardinal weights are positive
by exactness on their squares. This is a positive Radau rule
with one rational endpoint and no new splitting field.
Depth and exact order follow from the nonzero paid and
above-depth first-unpaid tall values. In either case the
compositum of all mandatory saturated fields (and prescribed
terminal field if applicable) is exactly the least coefficient
field by inclusion for this width profile. The result uses
the permitted rational endpoint at the designated levels; it
does not impose that all clocks lie strictly inside (0,1).
It holds uniformly over p, without estimating the degree of
that compositum.

## 4. A complete root-pin certificate and real-only alternative

The rational certificate statements in this section assume algebraic diagonal and terminal data. Let W have n independent moment constraints on degree <r,
so monic degree-r solutions form an affine space of dimension
a=r−n. If a split solution H with r distinct roots exists over
the target field F, there is a set of a of its roots that pins
it uniquely. To see this, evaluation on all r roots is
injective on the a-dimensional homogeneous space of allowable
degree-<r differences. Select a independent rows of that
evaluation map. Thus fixing those roots over F reduces
existence to an invertible degree-n moment solve: put G equal
to their monic product, solve the degree-n monic residual P
orthogonal to GW, and require exact split of P over F with no
old-pin collision. Invertibility is equivalently injectivity
of the degree-<n homogeneous system after multiplication by
G. Conversely such a residual and distinct pins give H=GP.
This is a complete positive certificate on finitely many
charts, not a finite search over pin values or an assumption that arbitrary pins work. For the
simple rank/Haar cases all constraints are independent; known
one-moment cases can also be handled directly by the original
rational-root recipe.

For the full nonzero profile after reuse, an even layer has
r=n+1. In the Haar ranges the certificate simplifies to a
single root parameter with no real branch search. Take
the monic degree-n solution P and any monic degree-(n+1)
solution Q; all latter solutions are Q+tP. P and Q are
coprime. Otherwise at a root of P one could choose t to make
Q+tP have a multiple interior root, impossible because a
degree-(n+1) polynomial orthogonal to Haar W must have at
least n interior sign changes. The latter fact follows by
bordering evaluation rows at the sign-change sites, adding
filler sites tending to 0 if needed, and taking a normalized
limit sign test. Therefore all real Q+tP have n simple
interior roots and one remaining distinct real root (which
may also be interior). For any a∈F with P(a)≠0 take
t=−Q(a)/P(a), and test the degree-n residual after dividing
by y−a for **exact split over F**. Every F-split hull arises
on this chart by choosing one of its roots a. Taking any
rational a off the poles always yields a simple real-split
hull, but need not yield all its roots in F.

More generally, for any attained cut whose W is Haar, one
can take any distinct rational pins outside [0,1], since
multiplication by their product preserves Haar. The residual
P then has n simple interior roots unconditionally. This
is a constructive field extension option even if the exact
old-field existence problem remains open. For a recomputed
candidate without a Haar proof, there is an exact rationally
auditable **real** split certificate as follows. For a monic
degree-n P over a real number field K, work in K[y]/(P).
For a weight g compute the symmetric trace matrix

    H_g(i,j) = Tr(multiplication by g(y)y^(i+j)),
                 0≤i,j<n.

H_1 is positive definite at the chosen embedding iff P has
n distinct real roots. To see this after extending to R,
a nonzero nilpotent lies in the trace-form radical. In the
reduced quotient each real factor contributes a positive
square, while each complex factor contributes
2 Re(z²), which has a negative direction. With simple real
roots established, H_y and H_(1−y) are both positive
definite iff all those roots lie in (0,1), by the real
coordinate decomposition. Equivalently the latter two
positive definite matrices already imply H_1 is positive
definite by addition. Other rational brackets or explicit
disjoint sign-changing intervals work too. Imposed-root
collisions are checked by nonvanishing evaluations.

All the matrices, moment solves and signs can be verified
by exact rational linear algebra and algebraic sign
certificates at the specified real embedding (e.g. an
isolating rational interval for a primitive element and
a signed polynomial-remainder calculation). If coefficients
depend rationally on γ, denominators and Sylvester minors
give finite rational sign inequalities and can certify
an entire γ interval by exact sign isolation. This does
not require forming the full compositum. Each new individual
clock is a root of a rational norm polynomial of degree
≤[K:Q]n, and can be supplied by an isolating bracket and
its K-residual predicate even when the joint field is much
larger. Exact descent **without** extension instead needs
literal root elements in F: one may give them in a rational
basis of a specified number field, verify the product
identity for P and distinctness there, and obtain the
cardinal rows by field arithmetic. An unspecified
real-splitting certificate or a p-adic splitting receipt
does not replace those field elements.

## 5. Keep the old Gaussian rule and still attain exact order p

In the generic-depth profile D=p−1, the first positive layer
has width one (s=2) whenever that profile is feasible. This
gives an exact order witness without changing the terminal
rule or assuming a nonzero next shifted tall value.

For p≥3 and γ≠0, if the tableau paid order p+1, applying
Section 1 at distance d=p−2 with width r=1 would give the
larger budget b_cut=1 and force its monic linear hull to
annihilate

    C(p−2,1)=T^(p−3) K[y]_(≤2).

This is impossible: the three tests T^m(y^j/j!), j=0,1,2,
paired with columns x^a/a!, a=0,1, have the rectangular
shifted beta-Hankel form

    H_(j,a)= Σ_(v=0)^m binom(m,v)(−γ)^(m−v)/(j+a+v+1)!,
    m=p−3.

Its rank is two by the published rectangular lemma, with
largest factorial index m+4=p+1. If m=0 the ordinary
pairing already has rank two. Hence there is a first-unpaid
tree discrepancy even when the Gaussian rule would pay the
next bush and the first-unpaid shifted tall value is zero.
This permits retaining the old terminal Gaussian field for
odd p as well. At p=2 the one-node Gaussian rule misses the
degree-two bush. For γ=0 and for the sharp shallow exceptional
profile, the already proved tall witnesses give exact order.
The nonzero paid tall value keeps the asserted physical depth
in each regime. For unlike profiles without these witnesses
Section 1 by itself gives order at least p, not exact order.

## 6. Practical priority

* **High tractability, unconditional within existing cut ranges:**
  one-hull-per-width reuse, zero-diagonal Jacobi/endpoint reuse,
  and real-split or interval receipts. These preserve all
  physical stage counts and actual rows can still be recovered
  by cardinals. No jointly huge field need be expanded merely
  to verify real splitting or the paid moments.
* **Exact old-field certificate, positive when supplied:**
  check the compulsory hulls and the remaining independent
  residual problems. For the full nonzero profile only the
  even-width single-parameter problems remain after testing
  mandatory fields and treating the one-constraint cuts.
* **Arithmetic limitation:** real openness and a one-dimensional
  parameter do not imply there is a value whose remaining roots
  lie in a prescribed number field. That is a separate splitting
  or rational-point question. None of these positive methods
  claims a universal small extension, or computes a lower
  degree for an unspecified forced compositum. In a topology
  where the physical word factorization fails, neither the
  necessity nor the resulting least-field statement is implied.
