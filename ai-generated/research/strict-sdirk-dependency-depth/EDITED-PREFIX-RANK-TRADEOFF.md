# Edit and shared-start tradeoffs for the physical carrier rank

Pure mathematics. Fix a real common diagonal gamma != 0. Coefficients of
the constructions can be rational. No assumption of positive readout or
that other stage clocks lie in (0,1). The lower bounds concern the stated
retained slots/phase, not arbitrary SDIRK. The outside stages need not
form an adjacent block, and all actual output weights may be changed.

## 1. The rank device, and a stronger mixed-degree carrier

Write M=diag(c), c=A1, and Pi=M A-A M-A^2. Its diagonal is -gamma^2;
in particular Pi is invertible. For a formal expression in stage tree
profiles Phi_t, its exact polynomial model sends Phi_t to
|t| x^(|t|-1)/t!; each normalized order condition pays the integral
of this polynomial. Multiplication by M attaches a leaf at the root
(X: multiplication by x), and A adds a unary root (I: integration
from 0 to x). The model of Pi is exactly zero, since XI-IX=I^2.
These are rules on the specified expressions, not on a quotient by
actual stage-vector relations. A grade bound is the maximum tree
order in the expression.

Here is the rank principle without a support assumption. For each
l pick an injective polynomial-profile lift V_l of a polynomial
subspace: every V_l(P) has grade at most p-2l and exact model
w(x)P(x), where one fixed w is nonzero and of one sign on [0,1].
Require deg P <= 2l. Then the vectors Pi^l V_l(P) for a basis in
each block are independent. In a relation divide from the left by
the lowest occupied power Pi^l0. Apply the actual left row b^T
P_l0(M). This is paid because the new grade of a term l is at most
(p-2l)+2(l-l0)+2l0=p. The terms still containing Pi have zero
target; the leading term is the nonzero integral of w P_l0^2.
Inversion was performed only on actual physical vectors before
computing these models; no paid model of an inverse is used.

For a single carrier D of grade r and nonzero exact model d of
one sign, take n=p-r, m_l=min(2l,n-2l),
V_l(P)=P(M) D and w=d. Its rank through block L is
    F(n,L) = sum_{l=0}^L (1+min(2l,n-2l)),
    0<=L<=floor(n/2).
The complete count is F(n)=floor(((n+2)^2+4)/8), as can be checked
by splitting the two progressions at floor(n/4). For d of changing sign
one basic alternative is the left test d(M)P(M), at cost deg d:
use n=p-r-deg d and the nonzero integral of d^2 P^2.

**Mixed-degree improvement.** Suppose d=x^u(lambda+zeta*x),
u>=0 an integer, lambda*zeta !=0. Its nonzero root is
alpha=-lambda/zeta. The model of A D, divided by x^u, is
x(lambda/(u+1)+zeta*x/(u+2)), whose value at alpha is the
nonzero constant -zeta*alpha^2/((u+1)(u+2)). Divide this
quadratic by lambda+zeta*x. Thus a combination of A D and
Q(M)D with deg Q<=1, rescaled by the nonzero remainder, is
a physical carrier E of grade at most r+1 and exact model x^u.
If D vanishes on a predecessor-closed retained set, E does too.
For any polynomial P, divide it by lambda+zeta*x and use
    V(P) = quotient(M) D + P(alpha) E.
Its exact model is x^u P, and its grade at most
max(r+deg P-1,r+1). (The quotient is zero if P is constant.)
For p>=r+1, set n=p-r+1. At l with n-2l>=2 use the full
polynomials of degree <= min(2l,n-2l). If n-2l=1 use just D,
whose factor lambda+zeta*x has degree 1<=2l. If n-2l=0 use
no block. Thus the independent count is exactly
    F(p-r+1)-1.                                                     (A)
The last block loses one column in either parity of n. This does
not claim optimal rank of all useful expressions. It is stronger
than merely retaining one sign-adjusted seed, and includes the
case of a sign-changing linear carrier.

Any such independent family gives an outside-stage rank bound:
if its projection onto s retained coordinates has dimension at
most b, at least rank-b stages are needed outside those coordinates.
This is rank-nullity, and does **not** require their complement to
be invariant. The same carrier proof therefore applies before
support is exactly closed.

## 2. A few edited rows at fixed old clocks

Take s labelled, chronologically increasing slots. The nominal chain
has A0=gamma I+a N, N the strictly lower all-ones matrix in those slots,
and M0=diag(gamma+ai), i=0,...,s-1, with a!=0. Allow arbitrary new
stages, even interleaved, and arbitrary changes in at most t old rows,
but the clocks of all retained slots remain nominal. An unedited row
keeps all its nominal coefficients and gets no input from outside the
slots. Let P be coordinate projection to these slots, and let R be the
row error P A-A0 P, with image in the edit-site coordinate span H.
Put mu=a-2gamma and nu=gamma(gamma-a).

The actual grade-three carrier is
    D = c^2 - 2Ac - mu c - nu 1,
with exact model d(x)=-mu*x-nu. Here the square is pointwise.
Since c_old is unchanged, P D lies in H: a nonedited row's
first clock moment is unchanged even if earlier states were edited.
The two useful exact projection identities are
    Pi0=M0 A0-A0 M0-A0^2=-gamma^2 I+a*mu*N,
    P Pi - Pi0 P = M0 R - R M - A0 R - R A.                       (B)
For the first, [diag(i),N]=N+N^2 entrywise. The second is just
expanding the products using P M=M0 P and P A=A0 P+R.
Its error image lies in H+NH.

Starting from P M^j D in H, (B) implies
    P Pi^l M^j D in span(N^q H : 0<=q<=l).
For midpoint a=2gamma the nominal Pi0 is scalar, so the bound is
H at l=0 and H+NH at every l>=1. This includes edits that read
interleaved new stages; it does not pretend old complement
invariance when those edges are present.

**Exact spline loss.** If the edit sites are i_1<...<i_t,
let g_i be the distance to the next edit, the final sentinel
being s. Then
    dim span(N^q H : 0<=q<=L) = sum_i min(L+1,g_i).                 (C)
For L=0 the vectors are the edit-site coordinate vectors. For q>=1,
(N^q e_i)_j is zero for j<=i and binom(j-i-1,q-1) for j>i.
The space consists of an arbitrary value at each knot i and
a discrete polynomial of degree <=L-1 on the rest of its gap,
zero before the first knot. Inclusion follows by restricting earlier
polynomial tails. For equality, work from the first gap to the last:
at the current edit use its spike and its polynomial tails to fit
that gap after subtracting earlier contributions. The new columns
vanish on all earlier gaps, and the binomial polynomials form the
full restricted polynomial space. This proves the claimed exact
dimension, including short and adjacent gaps.

For a one-sign d, n=p-3. For the basic sign-adjusted d, use n=p-4
when needed. At l<=L the bound is
    outside stages >= F(n,L) - sum_i min(L+1,g_i),                 (D)
clamped at zero and maximizable over L. In midpoint replace L by
min(L,1) in the spline loss. The formula is a lower bound on actual
outside stages, not an assertion of attained RK order.

When the edited prefix itself is predecessor-closed, one can compute
the exact projection loss for this family on its own rows: it is
the rank of the columns Pi_old^l M0^j P D. If P D has q nonzero
coordinates, the rank of each l-block is exactly min(q,m_l+1)
by the Vandermonde on distinct edited clocks and invertibility of
Pi_old. Their sum and (C) are both upper bounds on the projection
rank. Equivalently, multiplying each P polynomial by the product
of the q clock factors of these actual defects fits
sum_l max(0,m_l+1-q) independent vectors entirely off the prefix.
This costs no extra positivity degree, since the enclosing
independent family was already proved. If all first clock moments
are preserved, P D=0 and this closed-prefix rank loss is zero,
regardless of the number of coefficient edits.

For a closed midpoint prefix the earliest nonzero D site i_* also
improves the loss. The original vectors are supported from i_* on.
On vectors supported on that suffix a row error with site <=i_*
acts on earlier inputs all zero; this remains true after multiplying
by M0 or a lower-triangular A. Accordingly (B) cannot generate
N e_(i_*) from the first defect, and its later errors may create
only edit spikes and step tails at the strictly later edit sites.
The subspace is therefore spanned by e_(i_*) and
e_i,N e_i at later edits. In particular at most 2t-1 dimensions
are lost if there is any actual defect, or zero if none.
With interleaved edges use the general <=2t instead.

**Sharpness of early one-edit projection loss.** In any row i>=2
add epsilon to nominal predecessor 1 and subtract epsilon from
predecessor 0, with epsilon!=0. Clocks stay fixed, P D=-2epsilon*a e_i.
If this is the only edit of a closed prefix, on the suffix starting
at i the edited Pi acts exactly as nominal Pi0, since the
perturbation reads only earlier inputs. For mu!=0, the span of
Pi0^l e_i for 0<=l<=L equals span of N^q e_i, q<=L, and reaches
min(L+1,s-i). Thus the spline loss in (D) really can be attained
by equal-clock physical rows. This is a rank statement, not a
high-order feasibility example. In the midpoint the same one edit
costs only its single spike.

**Improved generic tradeoff.** For a neither gamma nor 2gamma,
d is linear with nonzero constant and linear coefficients. Use (A)
with r=3. In the Euclidean lift the initial old projection is
in H+NH, since P E is made from P A D and a linear polynomial
times P D. The polynomial part of each lift is always a polynomial
times D, not a high-degree polynomial times E; this is important
for the projection degree. In the full mixed blocks l<=L-1 for
L=floor((p-2)/2), the projection is in sum_{q<=l+1}N^q H.
If there is a terminal l=L block it contains only D, which
again projects after Pi to q<=L. Thus
    outside stages >= F(p-2)-1 - sum_i min(L+1,g_i),
                                     L=floor((p-2)/2), p>=4.       (E)
More generally this proof works for an available one-degree-higher
constant carrier with the indicated same projection bound.

For s=p and one edit, (E) gives lower total stages on p=4,...,20:
    4,5,7,9,11,14,17,20,23,27,31,35,39,44,49,54,59.
Every entry is at least the last verified unrestricted achieved
table (3,5,7,9,11,14,17,20,23,26,30,34,38,43,48,54,59).
Midpoint at p=20 has F(17)=45; s=20, at most 2t dimensions lost.
Thus three or fewer fixed-clock edits cannot strictly improve on
59, even interleaved. In a closed prefix the three-edit lower is 60.

Euler a=gamma is different: d=gamma*x. It has the one-sign bound,
but cannot gain a constant seed by (A). Indeed on the nominal
Euler chain every nonleaf stage polynomial vanishes at c=0:
if a polynomial q at the stage clock has discrete primitive G
with G(x+a)-G(x)=a q(x), the A0 action is
G(x+a)-G(a), identically zero at x=0. The tree recursion carries
this to all nonleaf profiles. Their degrees are <=|t|-1; any
carrier of grade <=s vanishing on all the nominal clocks therefore
has exact polynomial constant term zero. This is a property of
the nominal chain, not a general statement about edited profiles.

An actual early edited rational Euler base survives these tests:
take i>=3 fixed, alter the preceding columns 0 and 1 as above,
and use s=p. Its subdiagonal remains nonzero, so the strict
Krylov vectors (A-gamma I)^j 1 for 0<=j<p are triangular with
nonzero diagonal (the product along the only length-j path to
row j). Signed rational weights can still realize all scalar
moments through p. The one-edit projection loss is attained, but
at p=20 the lower from this particular proof is only 20+45-9=56
for an early enough edit. Counts 56--58 are unexcluded, not
constructed. The same-clock scalar-exact base is an actual
starting architecture; a high nonlinear order continuation is
not claimed.

## 3. A shared state handoff into an entire uniform phase

Allow s retained branch rows to start at one common earlier
prestate, not necessarily y. Their internal block is A0 as before;
they all use the same earlier donor row r^T, extended by zero
on slots of the branch. Thus P A=A0 P+1 r^T. Let
beta=r^T 1, lambda=r^T c, and lambda2=r^T c^2.
Their clocks are c_i=gamma+beta+ai. In this section P may read
these stages wherever they occur in a topological ordering.
The common incoming row can describe a genuinely different state
even if beta=0, hence the same clocks as the unbranched run.

Put kappa=nu+beta^2-mu*beta-2lambda. The grade-three carrier
    D3=c^2-2Ac-mu c-kappa 1
vanishes on the entire phase, with exact model -mu*x-kappa.
Indeed (A0(c0+beta 1))_i=(A0 c0)_i+beta*c0_i, where c0_i
is the unshifted clock. Expand c^2 and subtract 2lambda.

The commutator spill is even smaller than (B). Since the additive
offset cancels in [M0,A0], its nominal Pi0 is unchanged. Directly,
    P Pi - Pi0 P = 1 (beta r^T-r^T(M+A)).                           (F)
The correction came from M0 1-A0 1=beta 1. Thus the spill is
only constants on the branch. The cumulative N sends polynomial
sequences in i of degree k to degree at most k+1. Starting with
a carrier that vanishes on the branch, after l>=1 applications
of Pi its projection has degree <=l-1. For a=2gamma it stays
constant, even after arbitrarily many applications.

For reference a second actual carrier is always available.
Define P2(x)=x^3/3-(a/2)x^2+(a^2/6)x, satisfying
P2(x+a)-P2(x)=a x^2. Put xi=lambda2-P2(gamma+beta).
Then the grade-four carrier
    D4=A c^2-c^3/3-(gamma-a/2)c^2-(a^2/6)c-xi 1
vanishes on the branch by telescoping the sum of squares.
Its exact model is -(gamma-a/2)x^2-(a^2/6)x-xi.

These give the following physical bounds for a retained length s.

* **Midpoint shared start.** If kappa!=0, use the constant
  grade-three carrier and lose at most one rank in projection.
  If kappa=0, the nonzero linear grade-four carrier remains.
  With root at zero it is one sign; otherwise use (A). In the
  latter case E is built with A D4, whose projection is a constant,
  so the whole mixed family again loses at most one rank by (F).
  For p>=5 this yields in all cases
      total stages >= s+F(p-4)-1
  (the mixed count F(p-3)-1 is at least F(p-4)).
  For s>=p this is already at least all achieved entries p=5..20,
  and p=4 is immediate from s>=4. In particular a shared start
  into a length-20 midpoint branch still forces >=60 stages.
  This does not rely on keeping every donor row in the carrier
  support, or on the donor readout being zero.
* **Nonmidpoint shared start.** If kappa!=0, D3 has nonzero
  constant and linear terms and (A) applies. E has constant
  projection, whereas D3 projects to zero. For L=floor((p-2)/2)
  the full mixed blocks l<=L-1 project to degrees <=l, and
  the terminal D3, if present, to degree <=L-1. Hence the total
  is at least s+F(p-2)-1-L. With s>=p this rules out improvement
  through 20; it is one stronger than the one-edit estimate.
  If kappa=0, D3 has model -mu*x. If either xi!=0 or
  rho=r^T D3!=0, one still obtains a model-constant grade-four
  carrier that vanishes on the branch: use D4, or AD3-rho 1,
  respectively, and cancel its x and x^2 terms using D3 and
  M D3. Use this E in the same mixed construction (division by x)
  and same loss bound. Thus surviving low-grade gates require
  kappa=xi=rho=0. Then on the branch Ac and Ac^2 are polynomials
  of c without constant, and AD3=0 makes A^2 c another such
  polynomial. The other branch profiles through grade four
  are powers/products of these. On s>=4 distinct branch clocks
  any grade-four carrier vanishing there consequently has
  exact model constant term zero. Without another seed, the
  one-sign D3 bound and (F) give
      total stages >= s+F(p-3)-floor((p-3)/2).
  It is only 57 for s=p=20. This is an exact scope boundary
  of these branch-local tests, not a sufficiency condition.

There is a useful further exclusion with only two donor stages
in the *whole pre-feed list*. In the nonmidpoint, non-Euler
case with kappa=xi=rho=0, the three actual vectors
D3, M D3, A D3 all vanish on the branch. Their models span
x and x^2, with model kernel spanned by M D3-2 A D3. On the
first donor (first stage of the retained base) D3=nu!=0, and
this model-kernel expression equals -gamma*nu!=0 there.
With at most two donors some nonzero combination of the three
vectors vanishes on all donors, and that combination cannot be
in the model kernel. This gives a physical grade-four carrier
with exact model x(lambda0+zeta0*x) on the complement of the
whole retained closed base. If it is one sign use F(p-4); if it
changes sign use (A) with u=1, at least as strong for p>=5.
For s>=p and a retained donor list this lower rules out table
improvement through 20 as well. This last argument does not
apply to Euler, to a donor list with extra earlier ancestors
outside those two retained rows, or to uncontrolled rewiring.

## 4. Independent real rational check of the shared-start mathematics

There is an actual two-donor midpoint fed base of size p+2,
scalar-exact through arbitrary p>=5 and ordinary order exactly
four. This confirms the low-grade carrier shift is not vacuous,
but the preceding mixed rank proves that the full architecture
does not improve the current counts if retained.

Choose rational t sufficiently large and set
    H=t^3-6t^2+5t+6,    gamma=1/H,    beta=t gamma,    a=2gamma,
    S=(beta^2-2gamma beta-gamma^2)/2,
    delta=2gamma+gamma^2 beta/S,
    r1=S/delta,    r0=beta-r1.
The two donor rows have common diagonal gamma and single
strict coefficient delta in the second row, with clocks
gamma,gamma+delta. For rational t the quadratic denominators
t^2-2t-1 and t^2-t-1 do not vanish. For t>=max(8,p) all
physical clocks lie in (0,1): H>=t^3/4, all branch clocks
are (1+t+2i)/H, i<p, and 0<delta<3gamma.

Using S=delta r1 gives the first clock moment
r^T c=(beta^2-gamma^2)/2. Hence kappa=0. For U=c^2-2Ac,
the donor values are -gamma^2 and -gamma^2+delta(delta-2gamma).
Thus r^T U=-gamma^2 beta+(delta-2gamma)S=0, so AU also
vanishes on the fed phase. The second clock moment is
    lambda2=gamma^2 beta+(2gamma+delta)S
            =2gamma(beta^2-gamma beta-gamma^2).
Subtracting P2(gamma+beta)=(beta^3-beta gamma^2)/3 gives
    xi=-(gamma^3/3) H=-gamma^2/3.
The normalized grade-four carrier then has exact polynomial
(a^2/6)(1/2-x).

There are rational weights supported on the phase that pay all
scalar conditions through p: for the strict lower part B the
branch restriction of B^j1 equals (aN)^j1 plus a linear combination
of (aN)^k1 of strictly smaller k, from its fixed incoming row
and the preceding donor block. This follows by iterating the
two-block lower-triangular recurrence. Thus the first p Krylov
columns on the p phase nodes are binomial triangular and full rank.

On the paid readout, U=0 makes the order-three fork exact by
the paid tall moment. AU=0 makes b^T A c^2=2 b^T A^3 1=1/12,
the unary-over-fork at order four. The D4 relation, with
xi=-a^2/12 and b^T c=1/2, then gives b^T c^3=1/4.
Since Ac=c^2/2 on the phase, the mixed order-four tree is paid
as well. All ordinary order-four trees are now covered.
Order five fails: b^T M D4=0 on this support, whereas its
paid target would be (a^2/6) integral x(1/2-x)=-a^2/72.

Moreover this exact grade-four carrier can be arranged to
vanish on both donors as well as on the phase: U and AU
have exact model zero and vanish on the phase, and their
two donor restrictions are independent (U's first coordinate
is -gamma^2, and AU-gamma U has second coordinate
-delta*gamma^2, first coordinate zero). Cancel the two donor
coordinates of D4 using these. On the whole retained p+2
base the model is still (a^2/6)(1/2-x), so (A) forces at
least F(p-3)-1 stages beyond it. At p=20 this is 44 more,
66 total. In particular a small manufactured state can truly
remove every grade <=3 nonzero model carrier on the branch
(there the grade <=3 profiles are exactly polynomials at c),
without evading the physical rank bound after grade-four
closure. The unexcluded directions above require different
architecture, not just adding paid stages to this example.

The spline count is a bound on projected rank, not on the number of live outputs. Its fixed-clock hypothesis includes donor clocks. The two-donor whole-base bound assumes the actual donor ancestry is retained and predecessor-closed; two nonzero donor taps alone do not give that hypothesis.
