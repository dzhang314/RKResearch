# Exact negative-diagonal width in the adjacent terminal-output format

**Scope.** Fix p≥2 and a prescribed negative real γ, and work first
in characteristic zero with γ in a real coefficient field. A
nonzero determinant below already lies in Q(γ), so the lower bound
also holds after any extension of that subfield. The physical
diagonal of A is γ, the actual strict part B=A−γI only connects a
level to the next level, and b is supported on the single terminal
level. No trimming of strict same-clock edges is used. This is not a
general SDIRK stage minimum, and this note makes no claim for an
arbitrary positive γ or other topologies.

For an order-at-least-p tableau in this format, put s=p−d at strict
distance d below the terminal level. For every 0≤d≤p−1, the level
at distance d must exist and must have at least

    r_d = min(ceil(p/2), floor((2(p−d)+1)/3))

**distinct contributing clock labels for these probes**: it suffices
to count indices on that level with any actual strict route to the
terminal b-support. In particular this many physical stages is
necessary per level. The word "contributing" here means eligible to
enter a strict-path row, not that the level has nonzero output b.
For every prescribed negative real-algebraic γ the [higher-budget construction](ANCESTOR-MOMENT-SPAN.md) attains these widths at exact order p and
depth p−1 over a finite real-algebraic coefficient extension.

## 1. Paid physical word; why the bottom multiplier is allowed

Let c=A1 and let Y be coordinatewise multiplication by 1−c. This is
a diagonal linear map on the actual physical stage vector, not a
new stage or contracted edge. For nonnegative k_0,...,k_d define

    L_k(v) = b · (Y^{k_0} B Y^{k_1} B ... B Y^{k_d} v).

There are exactly d B factors. The rightmost Y^{k_d} is a legitimate
multiplication at the receiving root of the test column in the
bottom level; it is not a new strict step or an extra edge.
Use columns v_a=Y^a 1 for 0≤a<r. Every pair L_k(v_a) is a linear
combination of literal RKOC values of order at most

    1 + d + a + Σ k_i.

Indeed c^a is a bush with a leaf children. Multiplication by a power
of c attaches that many leaf children to the same root, hence
increases grade by that power's exponent. Expand (1−c)^j by the
binomial formula. Acting by A adds a new unary parent; B=A−γI is a
sum of a one-edge increase and no increase. Finally the output inner product adds the
unit difference between grade and order. This argument applies to
each term, including identity choices in the expansion of B, so it
uses only the given all-tree order. In particular using Y^{k_d}
and Y^a on the same bottom polynomial costs just k_d+a, not a second
root. With Σk_i≤b_0, the entire matrix is paid when

    d + b_0 + r ≤ p.                                       (A)

The exact-flow substitution in these paid words is c↦x, A↦I_0
(the zero-origin primitive), B↦J=I_0−γ id, and the output readout ↦ℓ=∫_0^1.
This is not a simplifying-assumption substitution on unobserved
columns. For a literal tree the reference recursion gives
x^(order−1)/forestFactorial(tree), by multiplying at the root and
applying I_0 at each child edge. Integrating gives the inverse tree
factorial. Thus this substitution agrees on each paid scalar term.

In y=1−x, let M multiply by y and V integrate from 0 to y. Integration
by parts makes T=V−γ id the adjoint of J for the scalar integral.
Moving the d forward maps from the column to the test gives exactly

    L_k(v_a) = ℓ(y^a W_k),
    W_k = M^{k_d} T M^{k_(d−1)} ... T M^{k_0} 1.           (B)

In particular the bottom multiplier is what provides the full span
with its leftmost M^{k_d}. Restricting only to decorations strictly
above the bottom would in general lose a dimension.

## 2. Actual physical factorization and word span

Since multiplication by Y never changes a level and every actual B
step moves exactly one level, the row L_k reads only indices at
distance d below terminal b. This uses the unexpanded B, not its
paid algebraic expansion. If that level does not exist, all rows
are zero. Otherwise the matrix of (B) factors through its physical
indices by

    left_(k,i) = L_k(e_i),    right_(i,a) = (1−c_i)^a.

An index with no strict route to b-support has zero left column.
Equal clock labels give equal right rows and can be grouped. Thus
its rank lower bounds the number of distinct available labels at
that level. No assumptions on the signs of weights or edges, the
order of physical clocks, or their distinctness are needed.

For γ≠0 the already proved ancestor-word span is, with
m=(d−b_0)_+ and ν=b_0+min(d,b_0),

    span W_k = T^m K[y]_{≤ν}.                               (C)

For completeness, in the factorial coefficient bijection
`y^j/j! ↦ z^j`, T is multiplication by f=z−γ and M is
`D_+=z²∂_z+z`. Every word has degree ≤d+b_0 and keeps at least m
factors f. Conversely split the word span S(d,b_0) according to
its leftmost operation, giving
`f S(d−1,b_0) + D_+ S(d,b_0−1)` when both indices are positive.
At d>b_0 the first summand already gives the full filtered space
f^m K[z]_{≤ν}. At d≤b_0 it supplies all multiples of f in the
relevant degree range, a codimension-one subspace. For d=b_0,
`D_+ f` has the missing nonzero value γ² at z=γ; for d<b_0,
`D_+ 1` has the value γ. The d=0 and b_0=0 bases are respectively
all allowed monomials and f^d. This proves (C).

## 3. Why there is actual rank r at a negative diagonal

Write α=−γ>0. For each k, the first k test polynomials

    F_j(y)=T^m (y^j/j!),   j=0,...,k−1,

have strictly positive evaluation determinant on
0<y_1<...<y_k<1. In the factorial basis the coefficient matrix
of T is the lower bidiagonal matrix αI+S, S the subdiagonal shift.
An ordered minor can have a nonzero term only from the increasing
matching of row and column indices, since each row has nonzeros
only at its own or preceding column. Thus this finite matrix is
totally nonnegative, and so are its powers by Cauchy–Binet. The
monomial evaluation matrix has all ordered minors positive: a
nonzero combination of k distinct positive-domain monomials has
at most k−1 positive zeros by factoring the least power and using
Rolle inductively. Hence its ordered generalized Vandermonde sign
is constant; substituting y_i=ε^(k-i+1) for sufficiently small
positive ε makes the increasing matching the unique leading term
with positive sign. Factorial column scaling does not change this.
Cauchy–Binet now gives strict positivity of the test evaluation
determinant, with a positive term from exponents 0,...,k−1 and the
α^m diagonal of the coefficient matrix.

Consequently no nonzero polynomial P of degree <r can annihilate
F_0,...,F_(r−1) under ℓ. If there are a≤r−1 interior sign changes
of P, take the determinant of the first a+1 tests evaluated at these
points and at an additional variable y. It has no other interior
zeros and its sign alternates across the listed points, by the
ordered strict determinants. Multiplying it by P gives a nonzero
constant-sign integrand, so its integral is not zero. This gives
an invertible r-square moment pairing with 1,y,...,y^(r−1).
It is a determinant of already paid readout values after row
combinations in (C), not a claim of intermediate column equality.
The argument works already in the real subfield Q(γ) and survives
field extension by nonvanishing of that same determinant. It does
not require the physical nodes or weights to be positive.

Provided r≤ν+1, the rows in (B) generate those r test polynomials;
the matrix through the physical layer has rank r. Take b_0=s−r.
The condition r≤ν+1 is equivalent to both

    r≤2b_0+1 and r≤b_0+d+1,
    i.e.  3r≤2s+1 and 2r≤p+1.

The displayed r_d is the largest integer satisfying both, is at
least 1 for s≥1, and is at most s, so b_0≥0 and (A) holds.
The physical factorization therefore forces the asserted width.
At the terminal d=0, the words just give the ordinary moment pairing
and r_0=ceil(p/2). At the earliest paid layer d=p−1, s=1 and r=1:
the word is the pure tall test b^TB^(p−1)1, whose target
ℓ(J^(p−1)1)>0 because J=I_0+α id. Thus it forces the earliest
level to exist. These two endpoints do not presume nonempty levels
in advance.

## 4. Attainment and the 130 comparison

The published higher-budget construction for a prescribed negative
real-algebraic γ has exact depth D=p−1, positive q=ceil(p/2)
Gaussian output clocks/weights, zero output weights on earlier
layers, and widths

    min(q, ceil((2(h+1)−1)/3)),   0≤h≤D.

These follow from actual split hulls and simultaneous ancestor-first
cancellation for every paid tree, not from just the probes above.
Its exact depth and exact order witnesses are the nonzero paid tall
and first omitted tall target respectively. Here h+1=p−d, and
`ceil((2s−1)/3) = floor((2s+1)/3)`. Thus the upper exactly meets
all of the physical width lower bounds at once. The total adjacent
terminal-only minimum in this matched class is

    Σ_(s=1)^p min(ceil(p/2), floor((2s+1)/3)).

The upper may enlarge a prescribed coefficient field. The claim of
attainment is over the allowed real-algebraic extensions, not at a
minimal fixed coefficient field or with extra constraints on a
prescribed set of clocks. For p=20 the widths in increasing s are

    1,1,2,3,3,4,5,5,6,7,7,8,9,9,10,10,10,10,10,10.

The first fourteen sum to 70, the last six to 60. The full apparent
30-stage gap above the previous 100-stage staircase is structural
for a prescribed negative γ in this format. A further improved
negative-diagonal construction must break at least one exact
factorization premise, for example by permitting skip edges or
nonterminal output weights, not by adjusting only final quadrature
or independently retuning a same-level hull. None of this gives a
matched minimum at a positive exceptional depth.
