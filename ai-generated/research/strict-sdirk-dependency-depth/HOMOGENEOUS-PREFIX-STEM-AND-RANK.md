# A retained-prefix obstruction for rational common-diagonal extrapolation

Pure math, characteristic zero over a subfield of the reals. Fix one common
diagonal gamma != 0. This concerns an actual retained homogeneous prefix
or extrapolation forest, with arbitrary signed readout and arbitrary new
strict lower-triangular rows at that same diagonal. It is **not** a lower
bound on unrestricted SDIRK, or on a method permitted to replace those
old rows. All identities concern physical stage vectors and paid
rooted-tree conditions, without numerical search.

## 1. An actual rational scalar-exact family

Index s stages by i=0,...,s-1. Put A=gamma I+a N, a!=0, with
N_ij=1 for j<i and 0 otherwise. Thus c_i=gamma+ai. This is the signed
checkpoint readout of a constant-step one-stage theta chain: if z_i is
the prestate and k_i=f(z_i+gamma h k_i), then
    z_(i+1)=z_i+a h k_i.
The output y+h sum b_i k_i is a signed affine combination of the
checkpoints z_i, since a h k_i=z_(i+1)-z_i. In particular a=gamma
is repeated implicit Euler, and a=2gamma is repeated implicit midpoint.
Changing the number of steps or the readout does not change gamma.
This is not the usual extrapolation of separate scaled methods
with different diagonals.

The binomial-basis vectors e_j(i)=binom(i,j) satisfy N e_j=e_(j+1)
and e_0=1. Let p be the target scalar stability order. A base with
s=p exists over the field of a and gamma: solve
    a^j b^T e_j = sum_{k=0}^j binom(j,k)(-gamma)^(j-k)/(k+1)!,
    0<=j<p.
The binomial evaluation matrix is unit triangular, so this is a
unique rational b for rational a,gamma. Since A=gamma I+aN, the
equations are exactly b^T A^j1=1/(j+1)! for 0<=j<p. More stages
or different b cannot change the paid tall moments. A prefix of any
length s on the retained rows is enough for the later geometric bounds.

## 2. Exact stem calculation and first actual defect

Let M=diag(c). Use normalized stage weights Phi_t, so Phi_bullet=1,
Phi_[t]=A Phi_t, and b^T Phi_t=1/t! is the order condition, with
t! the tree factorial (product of subtree sizes). The coefficient in
the raw elementary differential convention is b^T Phi_t / sigma(t),
where sigma is the tree symmetry order. For the fork B=[bullet,bullet],
Phi_B=c^2 (pointwise square). Put mu=a-2gamma and nu=gamma(gamma-a).
The binomial basis gives the exact physical identity on the chain
    c^2 = 2 A^2 1 + mu A1 + nu 1.                                  (1)
Indeed c^2=gamma^2 e_0+(2gamma a+a^2)e_1+2a^2 e_2.
The pair (mu,nu) cannot vanish when gamma!=0.

For J denoting a unary root graft and l+3<=p, the normalized residual
in J^l B (target minus base) is
    e_l = -mu/(l+2)! - nu/(l+1)!.
Indeed (J^l B)!=(l+3)!/2 and the tall relation (1) propagates under
A^l. The raw residual is e_l/2 because sigma(J^l B)=2.                (2)
Every such scalar-exact base has ordinary order at least 2. For p>=4
it has order exactly 2 unless mu/2+nu=0. In the latter case it has
order exactly 3: the next unary-over-fork defect is nonzero (the
two residual equalities would force mu=nu=0). The tuning with a!=0
is available at nonzero gamma other than 1/2 and 1:
    a=2gamma(1-gamma)/(1-2gamma),    nu=-mu/2,    mu=2gamma^2/(1-2gamma).
In particular this gives actual rational bases whose first nonzero
defect is not correctable by any affine-balanced receiver combination.
The paid unary-over-fork coordinate already forces a response, even
allowing cancellations and reuse.

As a check, at this tuning the whole leading raw grade-four residual is
    (mu/24) (F_[[bullet,bullet]] + 4 F_[bullet,tall_2]
                                  + F_[bullet,bullet,bullet]).
For the star, the same binomial expansion gives
c^3=(6A^3+6mu A^2+(mu^2+5nu)A+mu nu I)1. For the mixed tree use
M Ac=(c^3-mu c^2-nu c)/2. Substituting the four scalar moments and
nu=-mu/2 gives the formula, with respective symmetries 2,1,6.
The main obstruction does not rely on this grade-four check.

## 3. Exact stem budget and a physical chain lower bound

Put, for l>=0 and integer alpha>=1,
    Q_(l,alpha)(gamma) =
      sum_{j=0}^l binom(l,j)(-gamma)^(l-j)/(j+alpha)!,
    X_l=mu Q_(l,2)(gamma)+nu Q_(l,1)(gamma).
By (2), the raw fork-chain coefficient at stem l in (I-gamma J)^l R
is -X_l/2 for the finite residual R of a scalar-exact base.
The rooted-stem criterion is that budget d permits exactly those R
whose (I-gamma J)^(d+1)R has no tall terms or stems >d. In the present
case tall terms are absent already. Write L=p-3, p>=4. There is just
one tree through the paid range with stem L, namely J^L B. Thus
    least response budget = L    if X_L!=0;
                             L-1 if X_L=0,                          (3)
using nonvanishing of X_(L-1) in the second case, proved below.
The upper budget L holds for any nontall residual through p. The
budget L-1 test has just the one remaining stem and is exactly X_L=0.

There is an analogous **actual row** consequence that does not assume
any response-budget architecture. In an arbitrary extended order-p
table retaining the chain, define
    D=c^2-2Ac-mu c-nu 1
using the extended physical A,c. Relation (1) holds on each retained
stage, so D is supported outside the chain. This holds even if those
stages are interleaved with other stages, as long as their predecessor
set remains unchanged. Let W be the coordinate space of vectors zero
on that closed subset. Both A and M preserve W. Write B_W for the
restriction of A-gamma I to W and b_W for the output restricted to W.
The paid tall and fork-stem conditions give
    b_W^T (A|_W)^j D=e_j,
    b_W^T B_W^l D = -X_l,                    l+3<=p.                 (4)
In particular nonzero X_l forces a directed path of l edges consisting
only of stages outside the old chain: B_W is strictly lower triangular,
and its lth power is a sum over such paths. Thus the continuation has
at least p-2 sequential stages outside the chain in the generic case
X_L!=0, or p-3 when X_L=0. This is independent of auxiliary output
sources, changes to old readout weights, and skip edges between new
stages. Section 4 gives a stronger width bound.

Here are exact nonvanishing controls, without a root survey.

* If gamma is rational with 1/gamma not an integer, each Q_(l,alpha)
  is nonzero: after setting x=1/gamma and clearing factors, Q=0 would
  say x is a rational root of the monic-up-to-sign integer polynomial
      sum_j binom(l,j)(-x)^j (l+alpha)!/(j+alpha)!.
  This is impossible. On Euler and midpoint chains X_L is a nonzero
  scalar times Q_(L,2) or Q_(L,1), respectively. At the order-three
  tuning it is -(mu L/2) Q_(L-1,3), by
  j binom(L,j)=L binom(L-1,j-1). Thus (3)-(4) take the maximal branch
  in all three rational families for these gamma, at every p>=4.
* For **every real gamma**, Q_(l,1) and Q_(l,2), l>=1, do not both
  vanish, and X_l and X_(l-1) do not both vanish when (mu,nu)!=0.
  To prove it, set Q=Q_(l,2) and P=Q_(l,1). Termwise,
      P=(l+2)Q-gamma Q',    Q'_(l,alpha)=-l Q_(l-1,alpha).
  Q has l positive simple roots: it is a nonzero constant times
  (-gamma)^l L_l^(2)(1/gamma), where
      L_l^(alpha)(x)=x^(-alpha) e^x/l! *
                           (d/dx)^l (e^(-x)x^(l+alpha)).
  Expansion by Leibniz gives the Q identity. Integrating the displayed
  derivative l times by parts proves orthogonality to degrees <l
  under the positive weight x^alpha e^(-x) on (0,infinity); all
  boundaries vanish. Multiplication by the product of its sign-change
  factors would contradict that orthogonality unless it has l
  different simple interior roots. Hence every root rho of Q is
  real, positive and simple. Away from those roots,
      (P/Q)' = sum_rho rho/(gamma-rho)^2 > 0.
  At a root rho the Wronskian P'Q-PQ' equals rho Q'(rho)^2>0.
  Therefore the adjacent rows
      (Q_(l,1),Q_(l,2)), (Q_(l-1,1),Q_(l-1,2))
  are independent for each real gamma, as required. For fixed nonzero
  gamma, X_L is affine in a and has at most one zero: if its coefficient
  Q_(L,2)-gamma Q_(L,1) vanishes, the constant is
  -gamma^2 Q_(L,1)!=0. No exceptional case undermines the width bound.

## 4. A support-local rank theorem using actual paid contexts

This argument also applies to a broader class than (1). On an arbitrary
real common-diagonal order-p table, take a predecessor-closed set of
retained stages and the corresponding W of vectors vanishing there.
Suppose one explicit stage expression D, a linear combination of tree
profiles of order <=r, vanishes on that set. For a formal tree profile
use the exact polynomial model
    Phi_t -> |t| x^(|t|-1)/t!.
This is a rule on the *expression* of stage profiles, not on their
quotient by actual vector identities. Its integral is the exact output
condition. Multiplying a profile by M attaches a new leaf at its root,
and corresponds to X: f(x)->x f(x). Multiplying by A adds a unary
root and corresponds to I: f(x)->integral_0^x f(u)du. Each increases
the paid order by 1. All claims follow directly from the tree factorial
recursion. Thus for any word in these operators applied to D, whenever
all its trees have order <=p, the actual b-readout equals the integral
of the corresponding polynomial expression. This does not assume
stage order or a continuous collocation tableau.

Let d(x) be the polynomial of the specified D expression. Suppose
d!=0 and select a real polynomial g of degree eta so that gd is
nonzero and of one sign on [0,1]. Always g=d works; if d is already
of one sign take g=1. Only this scalar degree of the sign test is paid.
Define
    Pi= M A-A M-A^2.
It has diagonal -gamma^2, so is invertible on W, since A,M preserve
W. Its polynomial model is exactly zero, as XI-IX=I^2 by single
integration. In particular it raises the symbolic grade budget by
two, yet any term with a positive Pi factor has zero paid target
(the Pi factor can sit anywhere in the word). This is where a
**nonzero common diagonal** is essential.

For n=p-r-eta>=0 consider the actual vectors
    Pi^l M^j D,  0<=l<=floor(n/2),  0<=j<=m_l=min(2l,n-2l).
They all lie in W and are independent. In any relation write the
j-block as P_l(M)D, and take l_0 the least l with P_l nonzero.
Factor out Pi^l_0 and invert it *on the actual relation*. The
result is a relation of nonnegative-power expressions. Left-test
by b^T g(M) P_(l_0)(M). This test is paid: for term l its largest
possible order is
    r + 2(l-l_0) + deg P_l + eta + deg P_(l_0)
       <= r + n + eta = p,
using 2l+deg P_l<=n and deg P_(l_0)<=2l_0. All terms at l>l_0
now have target zero by the Pi identity. The remaining target
    integral_0^1 g(x)d(x) P_(l_0)(x)^2 dx
is nonzero by sign and polynomial nonvanishing. Contradiction.
In particular at least
    F(n) = sum_l (1+min(2l,n-2l)) = floor(((n+2)^2+4)/8)            (5)
actual stages lie outside the retained set. For n=4q,4q+1,4q+2,4q+3,
the sum splits on either side of l=floor(n/4); the respective sums
are 2q^2+2q+1, 2q^2+3q+1, 2(q+1)^2, (q+1)(2q+3),
which verifies the floor formula.

For the actual D in Section 3 the grade is r=3, and
    d(x)=x^2-2(x^2/2)-mu x-nu=-mu x-nu,
nonzero for all a,gamma under consideration. If d changes sign use
g=d, eta=1; otherwise use g=1, eta=0. Thus if s stages of a
homogeneous chain are retained, an order-p table has total stages
    Ntot >= s+floor(((p-2)^2+4)/8)          for p>=4,
and when d is one sign,
    Ntot >= s+floor(((p-1)^2+4)/8)          for p>=3.                (6)
Euler (d=gamma x) and midpoint (d=gamma^2) obey the second bound.
These width bounds hold even if a particular X_l vanishes. Conversely
the depth bound (4) may be stronger for small p or answer a different
question (parallel width cannot replace its sequential path). Take
the maximum of the bounds, not their sum.

## 5. Forests, rational dimension control, and the actual table comparison

A fixed-gamma checkpoint forest can allow several different constant
increments, independent branches or literal shared prefix stages,
and any signed mixture of its checkpoints. Every preserved individual
branch is a predecessor-closed chain of the type above (not necessarily
consecutive in a topological sort). Accordingly (6) can be applied to
the longest such branch, regardless of what happens on the other rows.

If the forest by itself is scalar-exact through p, gamma is rational
and 1/gamma is not an integer, it must contain a chain of at least p
stages. Indeed if its longest branch has length r<p, its strictly
lower part B0 has B0^r=0; the tall conditions then give
    0=b^T B0^r 1=Q_(r,1)(gamma),
contradicting the integer-monic check in Section 3. This uses the
actual predecessor relation of a literal checkpoint forest, not
a nonlinear cancellation or counting readout points. The same
polynomial check shows that the s=p scalar-exact single-chain
construction first fails at scalar order p+1 for these gamma.

An additional fallback does not require any lower bound on branch
length or a reciprocal condition. If a whole (possibly heterogeneous)
forest is retained and W is taken outside it, set U=c^2-2Ac, and
form the grade-5 stage expression
    D5=(U+gamma^2 1) * (c^2+U)
                   -2(c-gamma 1) * (c*U-AU),
where * denotes componentwise multiplication. On a retained
branch U=mu(c-gamma 1)-gamma^2 1 by (1), and AU=mu Ac+nu c.
Consequently 2(c*U-AU)=mu(c^2+U); hence D5 vanishes at every
retained stage, for its individual constant increment. The
componentwise product of tree profiles is the profile whose
root has all the input root children combined; order minus
one adds and the exact polynomials multiply. This verifies the
grade 5 bound. The exact model of U is zero, so D5 has exact
polynomial gamma^2 x^2, of one sign. Thus (5) forces at least
    floor(((p-3)^2+4)/8)
stages outside the entire retained forest at p>=5. This can
be combined by maximum with (6) for any single branch, but the
sets counted by the two arguments need not be disjoint.

For a retained p-stage scalar-exact chain, the first lower bound in
(6), using just s>=p, gives the following total lower for p=4,...,20:
    5,6,8,10,13,15,18,21,25,28,32,36,41,45,50,55,61.
For comparison, the last independently verified unrestricted
achievable table on the same orders (free nonzero common diagonal,
real algebraic coefficients, no retained-prefix restriction) is
    3,5,7,9,11,14,17,20,23,26,30,34,38,43,48,54,59.
Each restricted lower is already strictly greater. At order 20
Euler/midpoint instead require at least 65 stages by the sign
version. These numbers are a barrier to improving that table by
retaining such a long homogeneous branch and tacking on arbitrary
late corrections. The result applies whether the base readout is
kept or freely changed, even if old rows receive zero weight. It
says nothing about a shorter retained branch, adapted increments
along a longest path, or changing the old rows and dependencies
so that D, or the predecessor-closed support, no longer survives.
