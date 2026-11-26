# Embedded-clock lanes: exact nonlinear lifts and a path-moment limit

Pure mathematics. Fix r >= 2 and a common positive rational diagonal gamma
small enough for the finitely many gates stated below. No numerical solution
of rooted-tree conditions is used. We distinguish ordinary rooted-tree order
from scalar stability order and from the pure clock moments B(k).

Two actual same-slot constructions are proved: one final fan gives ordinary
order >= r+1 with scalar order >= 2r-1, and two final fans, for r >= 3, give
ordinary order >= r+2 with scalar and pure clock orders >= 2r-1. A separate
exact path-rank theorem precludes turning the sparse versions into full-order
2r-1 in the high-order ranges below. These are not new unrestricted upper
bounds on ordinary SDIRK stage counts.

## 1. Input chart and the actual terminal lane

Use the cached Laguerre chart through r-1 with paid cap P=r, from
`LAGUERRE-CACHED-DENSE-KERNEL.md` (sealed SHA
`ad523310296387203bd96ed272a5ca3fcebe1885d1ffc4eff40b7499e6e447db`).
Put I P(x)=integral_0^x P(t)dt, T=I-gamma Id, ell P=integral_0^1 P(x)dx,
and W_k=k!T^k1. The incoming chart F is a polynomial of degree <r-1
taking values in constant row combinations of old observations H_i=h f(Y_i).
There are exactly floor((r+1)^2/4)-1 old physical rows. They are closed
under predecessors; their strict matrix has nilpotence exponent <=r-1.
The cap concerns the preceding chart's agreement with the full Laguerre
diagram, not ordinary order r. With F_*(x)=h f(Flow_(xh)(y)) and
e_n=D_f^n id/(n-1)!, its only needed nonlinear identities are
    F=F_* through grade r-1,
    (F_*-F)^[r]=W_(r-1)(x)e_r.
We use raw elementary-differential vectors for these identities. For
normalized stage order conditions, Phi_t has exact polynomial model
|t| x^(|t|-1)/t!, whose integral is 1/t!.

There is additionally an exact scalar identity beyond the paid nonlinear
cap. On f(y)=lambda*y write z=h lambda and u=z/(1-gamma z). The scalar
chart at each old layer k is
    F_k(x)/y = sum_(j=0)^(k-1) u^(j+1) T^j1(x).                    (1)
It holds in the full diagram by H(Z)=u(y+Z) and the layer recurrence:
T raises degree by one, so no scalar remainder aliases. The coefficient
in monic mode W_j is the same at every layer containing it. Reusing
exact low modes and reconstructing the high modes from the actual sampled
rows thus preserves (1) exactly in the cached diagram too. No nonlinear
profile beyond the cap has been inferred from this scalar property.

Choose r distinct terminal clocks x_1,...,x_r and a strictly lower
triangular matrix L on those r slots. In chronological order define
    H_i = H( (T F)(x_i) + sum_(j<i) L_ij Delta_j ),
    Delta_i = H_i-F(x_i),                                          (2)
where H(Z)=h f(Y) at the one physical row Y=y+Z+gamma h f(Y).
Only completed stages appear in each strict prestate. By induction all
Delta_i are O(h^r); their grade-r vectors are W_(r-1)(x_i)e_r.
Indeed the receiver's state is exact through r-1 at x_i; a prestate
perturbation starting at r changes the observed derivative only at r+1.
Consequently the clocks are exactly the x_i, and every terminal
observation agrees with F_*(x_i) through grade r. The restriction of the
strict RK matrix B=A-gamma Id to the terminal coordinates is exactly L.
The subtraction of F(x_j) in Delta_j only changes old-column entries.

Use b supported on the terminal rows, unless stated otherwise.
Write C=diag(x_i), m=(W_(r-1)(x_i))_i, and tau_j=ell T^j W_(r-1).
From (1) and (2) the scalar terminal residual is exactly
    Delta/y = [u^r/(r-1)!] (Id-u L)^(-1)m.                         (3)
The exact scalar derivative z exp(xz) has expansion sum_(j>=0)
u^(j+1) T^j 1(x): equivalently it solves (Id-uT)F_*/y=u.
Therefore if b has B(r) and
    b^T L^j m = tau_j,    0<=j<=r-1,                              (4)
the step has scalar order >=2r-1. Here B(k) means all pure
clock degrees through k-1. Converting from u back to z preserves
jet order since u=z+O(z^2). All formulas in (2)-(4) are constant
row arithmetic, not implicit nonlinear coupling between terminal rows.

## 2. One final fan: same slots, rational terminal clocks

There are r distinct rational clocks in (0,1) whose interpolatory
weights have B(r+1) and are positive. For existence, start with a
real r-node Gaussian quadrature for dx; it is obtained from the
monic orthogonal polynomial of degree r by positive moments and
the usual sign-change proof of simple interior roots. Remove one
root xi_r and let Q be the monic product of the other r-1 roots.
Gaussian exactness gives integral Q != 0 and
xi_r=(integral xQ)/(integral Q), by evaluating on the original
nodes. Replace the other roots by distinct nearby rational numbers
and use the same rational ratio for the last root. Distinctness,
interiority, and positivity of the interpolatory weights persist.
The new nodal product (x-x_r)Q is orthogonal to 1, so polynomial
division gives exactness through degree r. This is an exact
existence proof, not a search for good quadrature numbers.

Use these b weights. For gamma small, all m_i are nonzero since
W_(r-1)(x) tends to x^(r-1) and the rational clocks are fixed.
In the first r-1 terminal rows take L to be the one-predecessor
chain with nonzero coefficients (e.g. ones). Its Krylov vectors
for m'=(m_1,...,m_(r-1)) have first nonzero entry at successively
later rows, so form a basis. Let L' denote this block. Choose
one covector d with
    d^T (L')^j m' = tau_(j+1),  j=0,...,r-2.
The scalar equations in the final row are then solved by taking
its strict coefficients to be
    (d^T - (b_1,...,b_(r-1)) L')/b_r.
Indeed b^T L=(d^T,0), which yields (4) at all positive j;
j=0 follows from the clock moments. The scalar polynomial
basis is alternatively read as the first r-1 Delta_i/u^r
spanning degrees <=r-2. There is no appended scalar-only row.

This is already an **ordinary** order r+1 lift. Let
    delta = (T W_(r-1))(x_i)_i - L m.
The stage-state error at grade r is delta_i e_r, and thus the
whole derivative error at grade r+1 is delta_i Ue_r, where
Uv=Df(y)[v] is the unary-root graft on raw coefficients.
There is no other tree at that grade: all branches are exact
at the clocks (each child has size <r). The exact output of
the reference derivative profiles follows from B(r+1). The
grade-(r+1) scalar condition forces b^T delta=0, either by
(4) or by the nonzero tall entry of Ue_r. Hence every tree
through r+1 is paid, not only the tall/clock marginals.

Actual count is
    floor((r+1)^2/4)-1+r
with no additional field extension: all terminal clocks,
quadrature weights, and scalar-fit coefficients are rational
when gamma is rational. The retained field is generated by
gamma and the selected Laguerre clocks (which are actual row
sums). No Gaussian roots used to prove the rational-node
existence have to be adjoined.

## 3. Two final fans: shifted-Radau output, no higher incoming cap

Assume r >= 3. Let x_r=1-gamma and g(x)=1-gamma-x. Choose
x_1,...,x_(r-1) as all roots of the monic degree-(r-1)
polynomial Q orthogonal to degrees <=r-2 for the signed
density g(x) dx on [0,1]. This is well defined for small
positive gamma. At gamma=0 the moment matrix for the weight
1-x is positive definite; Q has simple interior roots by
the sign-change test. Its coefficients are rational functions
of gamma, and this moment-matrix and simple-real-root gate
persists for sufficiently small gamma. To avoid an unproved
positivity assertion about the signed density, choose disjoint
small sign-change intervals around those roots at gamma=0.
They still contain roots by continuity; they lie strictly
below x_r near 1. These are r-1 distinct real roots and
exhaust Q. In particular all terminal clocks are distinct
and interior, and m_1 and the other m_i are nonzero
since their limits are positive powers of nonzero clocks.

The degree-r terminal hull is (x-x_r)Q=-gQ, orthogonal to
degrees <=r-2 in dx. Its interpolatory weights b therefore
have B(2r-1) by polynomial division. In particular all
b_i are strictly positive, since the square of a degree-(r-1)
cardinal polynomial is an exactly paid test and has positive
integral. Define
    d_i=b_i g(x_i),  i<r;        d_r=0.
For all polynomials P of degree <=2r-3 we have
    sum_(i<r) d_i P(x_i) = ell(gP) = ell(TP).                     (5)
The first equality is B(2r-1) and g(x_r)=0; the second is
Fubini for I, or polynomial integration by parts. In particular
d_(r-1)>0 because x_(r-1)<x_r, irrespective of the ordering
of the other r-1 nodes.

We realize all scalar moments (4) while making
b^T L=(d_1,...,d_(r-1),0), as follows. This is exact constant
coefficient synthesis, with every observation physically
later than the ones whose Delta it uses.

* In the first r-2 terminal rows use the one-predecessor chain
  with nonzero links, say all ones. Let L_1 be this block and
  m_1vec the initial r-2 entries of m; its scalar Krylov
  vectors are a basis by the same leading-position argument.
* Choose a covector f on those r-2 entries with
      f^T L_1^j m_1vec = tau_(j+2), j=0,...,r-3.
  Complete row r-1 with predecessor row
      (f^T - (d_1,...,d_(r-2)) L_1)/d_(r-1).
  For the resulting prefix matrix L_0 this gives
  (d_1,...,d_(r-1)) L_0=(f^T,0).
* Complete row r with predecessor row
      ((d_1,...,d_(r-1)) - (b_1,...,b_(r-1)) L_0)/b_r.
  Now b^T L=(d^T,0). Equation (4) at j=0 is B(2r-1),
  at j=1 is (5) applied to W_(r-1), and thereafter reduces
  to the paid f^T L_1^(j-2) m_1vec.

The last two are the only fan rows; no older non-predecessor
link is needed. The positive small-gamma limit of tau_(r-1)
also ensures the top scalar degree is actually active. The
combined graph has scalar depth 2r-1 even though the retained
incoming chart is of depth r-1.

## 4. All ordinary trees through r+2 for the two-fan construction

This step does **not** demand that the incoming chart be paid
at cap r+1. Define S P=(P(x_i))_i for sampling, and define
    D P = S(TP)-L S P
for scalar or vector-valued polynomials. Write E=F_*-F
and E_term=S F_*-H. For the exact state error on the terminal
rows, using Delta=H-SF=S E-E_term gives
    state error = D E + (gamma Id+L) E_term.                       (6)
Here T acts on the continuous polynomial E and L on the
terminal row values. All statements are coefficientwise.

Set delta=D W_(r-1) as above. First
E_term^[r+1]=delta Ue_r. For the next grade,
    E_term^[r+2]
       = U(D E^[r+1])
         + ((gamma Id+L) delta) U^2 e_r
         + (C delta) D^2 f(y)[f(y),e_r].                          (7)
The error in the state begins at grade r. Up to output grade
r+2 Taylor expansion consequently uses only its linear term
and the first state term x_i f multiplying that error.
The squared state error has order >=2r+1>r+2 for r>=2.
Equation (6) gives all indicated sources in (7).
In particular the unknown F^[r+1] is allowed: it is simply
an actual polynomial row combination of degree <r-1.

Every term in (7) vanishes under the terminal output. First,
b^T D P=0 on all polynomials of degree <=2r-3, by (5) and
B(2r-1) applied to TP. The grade-(r+1) exact derivative
model has degree r and the old part degree <r-1; r<=2r-3
for r>=3, so the entire first term is killed for every
elementary vector, even outside the incoming cap. Also
b^T delta=0, and
    b^T L delta
      = d^T S(T W_(r-1)) - b^T L^2 m
      = ell T^2 W_(r-1) - tau_2
      = 0.
Here T W_(r-1) has degree r so (5) applies again. Finally
b^T C=x_r b^T-b^T L, exactly as row vectors by construction
of d. Hence b^T C delta=0 as well. Pure reference output
clock moments are exact at both grades by B(2r-1).
This proves **all ordinary order conditions through r+2**.

Stage count remains floor((r+1)^2/4)-1+r, exactly the
incoming cap-r chart and r terminal slots. The exact field
of the tableau is
    Q(gamma, selected Laguerre prep clocks, all roots of Q).
Necessity of these generators follows from the physical row
sums and diagonal; sufficiency follows from all preceding
polynomial operations and nondegenerate linear systems. The
last clock 1-gamma adds no root. The terminal Q can require
its splitting field; we do not assert a purely rational
version of this two-fan Radau construction.

For illustration, r=11 uses 46 stages and has ordinary
order >=13, scalar and clock orders >=21. This is a
genuine all-tree lift in the same wave, not ordinary order
20. For r=12 the corresponding numbers are 53, >=14 and
>=23. These are starting diagrams and do not change an
unrestricted ordinary-order upper table.

## 5. Exact mixed-path obstruction, independent of coefficient blowup

This applies to arbitrary signed output weights, including
old-row readout, and arbitrary real clocks and lower triangular
terminal L. It does not assume the scalar reweight formula.
It only uses the retained closed depth-(r-1) incoming block
and the physical terminal-to-terminal strict couplings L.

Use the actual supported stage vector
    D_0 = (A-gamma Id)^(r-1) 1.
It vanishes on the incoming rows by that block's strict
depth. Coordinate vectors zero on those rows are preserved
by B=A-gamma Id and M=diag(c) on the actual full table.
Their restrictions to the terminal support are respectively
L and C; all chart terms vanish there on such input vectors.
In particular this is not a gamma->0 approximation of
stage coefficients or a regularity assumption.

For s>=1 and nonnegative exponents j_0,...,j_s, consider
the actual stage word
    M^(j_0) B M^(j_1) B ... M^(j_(s-1)) B M^(j_s) D_0.           (8)
Its rooted size is at most r+s+sum j_i, since B is unary grafting
minus a scalar identity and M attaches a leaf at the root.
Order p pays its actual output against the following exact
polynomial moment, whenever that rooted size is <=p:
    Lambda_gamma(X_0^j_0 ... X_s^j_s)
      = ell[ x^j_0 T(x^j_1 T(... T(x^j_s T^(r-1)1)...)) ].       (9)
This follows directly from the tree model: M acts as x, and
B as T. It is legitimate even though D_0 is a sum of different
tree grades. The symbols X_i are independent coordinates for
the moment functional; the nested T on the right is univariate
and applied before taking the outer factor.

Physically (8) is exactly a signed atomic moment on ordered
terminal paths of length s:
    sum_(i_0>...>i_s)
      b_(i_0) L_(i_0,i_1)... L_(i_(s-1),i_s) (D_0)_(i_s)
                     x_(i_0)^j_0 ... x_(i_s)^j_s.                (10)
All indices here are terminal, and terms without actual
strict edges contribute zero. Thus the moment matrix on
polynomials in s+1 coordinates of total degree <=d has rank
at most the number N_s of nonzero s-edge paths, regardless
of signs, coincident nodes, or large coefficients.

Take d=floor((p-r-s)/2) when p>=r+s. Every square-moment
entry is paid. At gamma=0, (9) is literally
    (1/(r-1)!) integral_(0<X_s<...<X_0<1)
                      X_s^(r-1) prod X_i^j_i dX.
Its moment matrix on degrees <=d is positive definite:
a nonzero polynomial squared cannot vanish on this open
simplex. The entries of (9) are polynomials in gamma with
rational coefficients, so this positive definite gate
continues for sufficiently small gamma. Therefore the exact
necessary condition is
    N_s >= binom(d+s+1,s+1),  d=floor((p-r-s)/2).                 (11)
It is uniform in actual clocks, couplings and signed output.

There is also a finite-exception statement away from zero.
If N_s is smaller than the right-hand dimension, choose any
principal (N_s+1)-square submatrix of the paid model moment
matrix. Its determinant is a nonzero rational polynomial in
gamma (strictly positive at zero), whereas existence of that
table requires the determinant to vanish. Thus that graph's
obstruction holds at every gamma except a finite set of
algebraic numbers, independent of the clock/row parameters.
The theorem does not claim an exhaustive treatment of those
exceptional diagonals.

This is a genuinely mixed rooted-tree condition, not a clock
or scalar marginal. It sees the joint locations of each
successive high child and its parent's leaf clock, through
the multiplicative x factors at different unary grafts.
Projection to one clock or to all tall trees loses (11).

## 6. Counts and what they rule out through 20

For the original one-predecessor lane of r terminal slots,
N_s<=r-s. With a final dense fan and the first r-1 rows a
chain, N_s<=2r-2s-1 for 1<=s<=r-1. With the last two rows
fans and the first r-2 a chain, N_s<=4(r-s)-4 when s>=2 and
s<=r-2. The latter counts fan prefixes of length 0,1,2:
(r-2-s), 2(r-2-s+1), (r-2-s+2). At the ranges used below
no negative-part correction is needed.

More generally, with n chain slots followed by t fan slots,
the upper path count is
    sum_{f=0}^{min(t,s)} binom(t,f) max(0,n-s+f) + binom(t,s+1).
Fan vertices can only come first in a descending path; the
remaining chain edges are consecutive. This gives an exact
obstruction to merely lengthening a sparse one-hop lane.

For r=11 and target ordinary p=20, choose s=3: d=3, so (11)
requires 35 paths. The pure, one-fan and two-fan versions have
at most 8, 15 and 28, respectively. Even ordinary p=17 is
excluded for the original pure lane at r=11: s=2,d=2 gives
10 required compared with 9. At r=12 the single-fan version
still cannot be order 20: s=2,d=3 requires 20 versus 19.
These are arithmetic comparisons of (11), not searches
over tableaux or exceptional roots. The two-fan proof above
does not realize ordinary order 20; (11) at r=12 is only
a necessary path test, not a witness.

Already ordinary order 2r-1 of the pure lane is impossible
at small gamma for every r>=5. For r=5 choose s=2,d=1.
For r=6 choose s=1,d=2. For r>=7 choose s=2 and
d=floor((r-3)/2); then binom(d+3,3)>r-2. The last inequality
holds at d=2 and continues since r-2<=2d+2.
Thus the same-slot scalar span in the original lane is
not a full-order construction even with arbitrary reweighting.

A precise caution for attempting a further nested-adjoint
lift illustrates why just imposing *all* next adjoint moments
is too strong. In the shifted-Radau arrangement let z=x_r=1-gamma,
v=x_(r-1), and R be the hull of the first r-2 clocks. If the
terminal b paid B(r+3) and the supported covector b^T L^2 were to
represent ell T^2 on *every* polynomial through degree r, then
both of the following would hold for j=0,1:
    ell[x^j (x-z)(x-v) R]=0,      ell[x^j pi_2 R]=0,
where pi_2=(T^*)^2 1=(1-x)^2/2-2gamma(1-x)+gamma^2.
But pi_2(z)=-gamma^2/2 !=0. Modulo (x-z)(x-v), the linear
polynomial x-v equals pi_2(x)(x-v)/pi_2(z); the difference
has a quotient of degree <=1. The displayed zeros imply
ell[(x-v)R]=0, hence b_r=0 by its cardinal formula.
This would lose the active top scalar slot. It does not
rule out paying only the specific next rooted modes, or
adding a denser mixed lane, and should not be read as a
general order-(r+3) nonexistence result.

Use these statements as exact architecture results: the
ordinary r+1 and r+2 lifts are actual; the path count is a
limit; scalar order, full pure clock order, or enough paths
alone are not sufficient for a new unrestricted upper bound.
