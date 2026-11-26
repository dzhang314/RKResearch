# DIRK stage lower bounds over arbitrary commutative rings

Over a field with \(p!\) a unit, ordinary rooted
order \(p\ge8\) gives \(f_6\ge f_3+4\). Over every nonzero commutative
unital ring, cleared ordinary order \(p\ge12\) for a lower triangular
tableau gives
\[
               s\ge p+\lfloor(p-1)/2\rfloor-2 .
\]
No assumptions on diagonal, signs, repeated clocks or individual
weights enter the proof. At 12 and 13 the counts are 15 and 17;
the general counts at 14 and 15 are 18 and 20. The non-C(2)
branch at 14 also pays 19. The proof does not certify either
stronger full characteristic-zero count at 14 or 15 over rings.

The [characteristic-zero precursor](../characteristic-zero/dirk_universal_grade_six_surplus_from_genuine_closed_bridges_and_origin_jets_20261123.md) supplies the stage geometry. The proof below accounts for the field and factorial assumptions at each step.

## Weighted Gram and triangular rank inputs

For the size-\(h\) matrix with entries
\(I(x^{a+i+j}(1-x)^b)\), the fixed Beta identities are valid through
\(N=a+b+2h-1\) paid factorials. At row \(i\ge1\) the replacement
\((a+b+i+1)\operatorname{row}_i-(a+i)\operatorname{row}_{i-1}\),
in descending row order, has zero first entry. For \(j\ge1\)
its entry is
\[
 j(a+i+j-1)!(b+1)!/(a+b+i+j+1)!,
\]
the shifted smaller-matrix entry times \(j\). All multipliers and
the first pivot are units; the induction does not increase \(N\).
This establishes invertibility without a positivity claim over
the field. If fewer than \(\lfloor p/2\rfloor\) nonzero clock labels
have nonzero aggregate weight, the monic node polynomial \(V\) of
those \(k\) labels would satisfy \(I(xVQ)=0\) for all \(\deg Q\le k\).
The scalar cost is \(2k+1\le p-1\) and the size-\((k+1)\) shifted
Gram costs \(2k+2\le p\), a contradiction. Pure indicator classes
contribute zero aggregate weight at their clocks.

For a simultaneous invariant subspace of a lower triangular \(N\)
and diagonal \(Y\), split the subspace by the finite clock spectral
projections. Echelon reduction with the earliest pivot sends
each eliminated coordinate into a combination of later nonpivot
coordinates at that same clock. Hence the induced operators are
lower triangular and diagonal respectively. At the first nonzero
entry of the quotient \(Yv\), the equations
\(NYv=Y^2v/2\) and \(NY^2v=Y^3v/3\) would give incompatible
diagonal values \(y/2\) and \(y/3\). This is valid whether the
original triangular diagonal has zeros. For a pure \(F\)-plateau
at \(j\ge2\), both primitive defects vanish in the quotient and
\(\mathbf b\cdot\mathbf c=1/2\) ensures survival. \(F_2\) is
exactly the span of \(g=Ac-c^{\odot2}/2\), so \(f_3\ge1+\epsilon\),
where \(\epsilon\) records \(g\ne0\). If \(g=0\), the first
coordinate gives \(c_1^2/2=0\) and the first stage is truly zero.

For outgoing inclusive Hermite from invariant \(U\subset F_j\),
take the first \(r=\lfloor j/2\rfloor\) nonzero clock detections
of the constant vector modulo \(U\). A clock of nonzero weighted
mass guarantees detection by pure moment annihilation. Normalize
local prefix detectors on the constant vector. The polynomial
\(H=x\prod_{\nu=1}^r(x-u_\nu)\) kills all detected blocks and
the origin; \(HT\) of degree at most \(2r\), with \(\deg T\le r-1\),
can be matched by a single vector in \(U\) through the last
detecting row. This uses a matching vector separately in each
clock block and no reality assumption on the clock order.
The lower-triangular operator reads equal prefixes through that
row. After subtracting the actual primitive defect, the output
detectors attain \(J(HT)(u_\nu)\) on \(F_{j+1}\) and kill \(U\).
If all these primitive values vanish, the degree-\(\le2r+1\)
primitive has double roots at 0 and all \(r\) nonzero sites,
so it vanishes and \(T=0\). In the incoming version \(U=F_j\)
and \(r=\lfloor(j-1)/2\rfloor\); the actual primitive discrepancy
belongs to \(U\), so the detectors composed with \(A\) attain
the same \(r\) values on \(U\) and kill \(F_{j-1}\). This proves
both gains with the stated rounded indices and only primitive
divisions at most \(j+1\).

## Paying the grade-six surplus

If \(f_6=f_3+3\), the three gains are all one. Outgoing Hermite
rules out clock invariance of \(F_4,F_5\); incoming Hermite
does so for \(F_6\). If \(F_3\) is invariant, the later spaces
are \(U+wP_{j-4}\), \(U=F_3\), with at least four effective
head clocks by noninvariance at degree six. Products of
a clock-local \(U\) member with any \(U\) member belong to
\(F_6\); their head polynomial of degree at most two vanishes
at at least three other effective clocks. Hence these products
lie in \(U\). Finite interpolation of individual vectors,
intersecting value classes and using \(e-ef\) to exclude a
class as needed, yields actual pure indicators. This does not
assume a generic vector over an infinite field or constant
values of \(w\) inside a mask.

The refunded four-debut proof works with those possibly varying
heads. A zero-headed nonzero debut among the first three is
explicit by the genuine commutator on the masked \(xV\), where
\(V\) is the product of earlier nonzero outside-clock factors.
The subsequent tests \(J(xVQ)\) at that row, for every
\(\deg Q\le\deg V\), would annihilate a rescaled size-\(\le3\)
\(x\)-Gram of \(V\), impossible. This replaces the original
oriented interval sign test. At the third and fourth debuts
the same commutator has already vanished on enough preceding
nonzero heads to force their zero diagonals. For the coupled
cut at debut \(t=3,4\), charge each earlier split clock once,
including a split inside a pure indicator class or a nonzero
outside head at zero. Choose a preceding head representative
in each mask and subtract its exact class constant. The
input multiplier of degree \(\le t-3\) and the output multiplier
of degree \(\le t-2\) must vanish on the same charged
set. If it has \(b\) labels, the input domain projected to
the scalar profile has dimension at least
\(2+\max(0,t-2-b)\) and the output rank at most
\(\max(0,t-1-b)\). Projection is injective since the
\(t-1\) earlier nonzero head values distinguish its multiplier.
Thus a kernel primitive is a nonzero scalar multiple of
\(x^2\prod_{\nu\le t}(x-z_\nu)\). Differentiating only at the
previous debuts and applying divided differences gives the
two equations for \(z_i^2/w_i\), hence
\(w_i=k z_i^2 V_3'(z_i)\) at the first three witnesses.
Comparing the third primitive forces the first two clocks,
after rescaling the third to one, to satisfy \(x^2-x+1/5=0\).
The fourth determinant is exactly
\(x^2(x-1)^3(5x^2-5x+1)/300\), so has no additional distinct
nonzero root. The constants in this elimination need only
primes 2, 3 and 5, besides proven nonzero field differences.
All actual primitives in the cut have degree at most six.
The requisite fourth nonzero outside site follows from the
paid quadrature argument for \(p\ge8\).

In the noninvariant \(F_3\) alternative, the chain is
\(F_j=U+wP_{r+j-4}\), with at least \(r+4\) effective
clocks. Clock-local products in \(F_6\) have head degree
\(\le r+2\) and at least \(r+3\) other zeros, hence are
core elements. This gives finite indicator masks and makes
it legitimate to remove \(w\)'s mask component. Dividing
the \(2r-1\) consecutive products from two true \(F_3\)
head powers shows \(w=P(c)\) on its support with
\(\deg P\le4-r\). If \(r\ge2\), the first \(x\)-contrast
is grade three since \(Cw\in F_3\); three primitive moments
at its explicit off-head pivot cost at most \(F_6\) and
the shifted Gram kills degree-\(\le2\) \(P\). For \(r=1\)
and \(P(0)=0\), the plain contrast and its two shifts kill
\(P/x\) by the same test. If \(\deg P\le1\), the grade-four
\(x\)-contrast and its single shift suffice. Whenever the
contrast is asserted nonzero, all appropriate scalar
moment tests give the same fixed Gram, not a square of
unknown coefficients with a presumed sign.

The remaining \(P(0)\ne0\), degree-two or -three case uses at least
five distinct dirty sites. A nonzero clean nonroot follows by
testing the original plain contrast with \(xQ\), \(\deg Q\le3\),
at total grade seven. This size-four \(x\)-Gram costs eight.
Keep the earliest row of each unmasked \((c,w)\) signature and
omit clean zero. A genuine grade-3 to grade-6 trace whose scalar
constant is zero already repeats each signature and is zero
at clean zero. Repetition and zero insertion therefore subtract
only genuine grade-three indicators. This applies again to
each intermediate image before a second \(A\), since both
scalar operators \(J,x\) preserve zero constant. The resulting
lower triangular projection has a genuinely pure commutator
on the stated traces at grades five and six, without asserting
it is an ordinary RK method.

At most three preceding dirty taps at the first clean nonzero
row are impossible by the head Vandermonde and the incompatible
diagonal primitives of \(x,x^2\). With five preceding dirty
rows, genuine commutator pivots make the fourth and fifth
explicit and remove the tap between them. With exactly four,
the first clean nonroot is explicit. Two separate clean visits
before that event would make \(J^2(xP)\), degree at most six,
have the triple origin root and two distinct double nonzero
roots. This proves the first clean row is that nonroot,
and the nonzero four-tap null row forces it to share the
fourth dirty clock. The three-dimensional head evaluation
map cancels all four preceding inputs whenever a scalar
\(f\) satisfies \(f(0)=f(u)=Jf(u)=0\) at degree at most five.
A second clean row before dirty five would demand dependence
of value and derivative on \(x^2(x-u)^2 P_2\) at its distinct
nonzero clock, impossible already using polynomials of degree
zero and one in that last factor. Thus the two dirty rows
and the clean one between them are consecutive. The actual
commutator then removes the fifth-row diagonal and both later
taps from the fourth dirty and first clean rows. Each of
the fourth and fifth dirty rows consequently uses the same
first three predecessors, in either chronology.

Finally the cuts with \(f\in xP_3\) and head multiplier in \(P_1\)
have dimension at least three and inject into \(f\).
Their primitive evaluations on five dirty clocks lie in the
three-dimensional \(PP_2\) evaluation space, hence fill it:
a degree-\(\le5\) primitive with a double origin root cannot
vanish at five distinct clocks even if one is zero. This
would allow both \(P\) and \(xP\) to have zero value and
derivative at zero after addition of a multiple of the
same degree-five nodal polynomial. The two jets are
independent by \(P(0)\ne0\), contradiction. All dimensions,
chronological pivot equalities and root multiplicities are
field algebra; the largest new factorial cutoff is the
size-four \(x\)-Gram at eight. The two branches therefore
prove \(f_6\ge f_3+4\) at the claimed paid scope.

## The ordinary stage floor and the exact terminal Gram

For polynomials of degree at most \(d\le j\), ordinary separation
from \(F_j\) uses all \(\deg Q\le d\) tests within \(j+d\le p-1\)
and a size-\((d+1)\) ordinary Gram. When the first row is truly
zero, the coincident scalar polynomial factors \(x\), so
\(d-1\) test degrees suffice and a size-\(d\) \(x\)-Gram
separates at \(j+d-1\le p-1\). These statements include
injectivity of polynomial evaluations, by treating the zero
vector as pure.

An \(E_j=E_{j+1}\) plateau for \(j\le p-4\) gives an invariant
annihilator in reversed chronology. There \(v\) is reversed
\(b\), \(Y=I-C\) is reflected, and the second and third
primitive defects annihilate \(E_j\) by the exact
integration-by-parts identity at cost \(j+3\le p-1\).
The sum functional kills the annihilator and sums \(Yv\)
to \(1/2\). The native triangular quotient therefore
contradicts the plateau. This proves every stated strict
increase, even with zero or signed weights.

At \(p=12\), \(f_6\ge5+\epsilon\). In the anchored case
use degree six, six \(x\)-weighted tests and cutoff 12,
obtaining dimension \(5+7\). In the unanchored case
use degree five, six ordinary tests and cutoff 11,
obtaining dimension \(6+6\). From \(E_6\) to \(E_9\)
there are three strict steps, giving 15 stages in both cases.

For \(p\ge13\), set \(m=\lfloor(p-1)/2\rfloor\ge6\).
Pure growth gives \(f_m\ge m-1+\epsilon\).
The degree-\(m\) ordinary scalar space adds \(m+1\)
using cutoff \(2m+1\le p\), and the \(p-3-m\)
strict steps give \(s\ge p+m-3+\epsilon\).
This is sufficient at \(\epsilon=1\).

If \(\epsilon=0\) and equality holds, trimming a trailing
zero output would violate the just-proved weaker bound,
so \(b_s\ne0\). The rank staircase from \(E_m\) to
\(E_{p-3}\) is exact, grows by one at each step, and
ends with the whole coordinate space. Therefore the first
two reverse identities \(D_1,D_2\) vanish. At the terminal,
with \(y_s=1-c_s\), they give
\(b_s(a_{ss}-y_s)=0\) and
\(b_s y_s(a_{ss}-y_s/2)=0\).
It follows over the field that \(y_s=0\) and \(a_{ss}=0\).
Hence \(Ae_s=0,\ Ce_s=e_s,\ D_3e_s=0\).

The span of rows \(D_3W(A,C)\) of word length at most
\(\ell\) annihilates \(E_{p-4-\ell}\) and kills \(e_s\).
It has dimension at least \(\ell+1\): \(D_3\ne0\) and
any proposed plateau would have genuine \(N,Y\)
invariance, contain \(D_3\) and the zero \(D_2\), and
kill the sum functional, an instance of the same no-stall
contradiction. The dimension cap is \(\ell+1\) by the
saturated staircase. At \(\ell=p-4-m\) it is the whole
annihilator of \(E_m\), giving \(e_s\in E_m\).

Thus \(e_s=H(c)+z\), \(\deg H\le m,\ z\in F_m\).
Here \(H(0)=0\) follows from the true zero first row.
For each \(\deg Q\le m-1\), test with
\(b(1-c)Q(c)\): the terminal vector contribution is zero,
the pure contribution is paid since \(m+1+(m-1)=2m\le p-1\),
and the scalar test is \(I(x(1-x)(H/x)Q)=0\).
The size-\(m\) \(x(1-x)\)-Gram cutoff is \(2m+1\le p\),
including the borderline odd orders. It forces \(H=0\),
so \(e_s\) is pure and \(b_s=0\), contradiction. This
excludes exactly the remaining equality and proves the
uniform formula. For the nonzero-\(g\) order-14 equality
candidate the same terminal staircase works with \(m=6\).
Without an origin use \(Q\in P_6\) and weight \(1-x\):
grade \(2m+1=13\), size-seven cutoff 14. This gives the
additional conditional 19-stage fact.

Finally, over a nonzero commutative unital ring the
cleared tall equation makes \(p!\) a unit. Reduction
at a maximal ideal preserves the physical rows, triangular
structure, and all cleared rooted equations, and yields
a field of the above type. This proves the ring result
without a rational base-change assumption on that ring.
The later fixed-arithmetic inventory was treated only as
scope information, not certified as additional all-ring work.
