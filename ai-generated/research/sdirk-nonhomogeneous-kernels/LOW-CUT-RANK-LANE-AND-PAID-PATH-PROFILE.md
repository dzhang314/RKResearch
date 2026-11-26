# Paid path profile and a same-count low-cut-rank terminal lift

Pure mathematics. Terminal reorganizations only; no experimental search or
new unrestricted stage-table entry. We distinguish (i) a paid mixed path-count
profile, (ii) actual all-rooted order gained at the same number of stages,
and (iii) a different rank obstruction that remains even for a full terminal
DAG. The proved extra ordinary order in Section 5 is for the unit-time
readout, not a new dense output theorem at that higher order.

## 1. Setting and exact path resource

Use the actual incoming Laguerre chart F through layer r-1 at cap r, from the
cached dense-kernel seal ad523310296387203bd96ed272a5ca3fcebe1885d1ffc4eff40b7499e6e447db.
It is predecessor-closed with strict depth <=r-1 and has
    floor((r+1)^2/4)-1
physical rows. In Section 4 we use only the Laguerre error band and the
sample/cache identities from that seal, not the more specialized two/three
slot error expansions. The terminal-lane and shifted-Radau foothold is
`EMBEDDED-LANE-SHIFTED-RADAU-AND-PATH-RANK.md`, SHA
b76b3189c0e5fb86e9a1d794c663023c40485a47ca8cfa6c3047be322d8a1d8e.

Let I P(x)=integral_0^x P, T=I-gamma Id, ell P=integral_0^1 P, and
W_j=j!T^j1. All A diagonals are gamma. Labelling the r terminal rows
chronologically, put C=diag(x_i), L their strictly lower actual coupling
matrix, and B=A-gamma Id, M=diag(c) for the full tableau. The row model is
    H_i=H((T F)(x_i)+sum_(j<i) L_ij Delta_j),
    Delta_i=H_i-F(x_i),
where H(Z)=h f(Y) at the single new physical row Y=y+Z+gamma h f(Y).
The old chart terms cannot create an unrecorded strict edge among lane
rows. Every Delta starts at grade r, since F is exact through r-1,
so the physical time of H_i really is x_i. We use actual fixed row
combinations only.

The raw path-profile lower is strengthened by a support shift. For each
a>=0 put
    D_a=B^(r-1+a)1.
This vanishes on the whole incoming block, and also on the first a
terminal rows: on vectors vanishing in the old block, B is exactly L,
and the first a rows of L^a are zero. Its exact tree polynomial is
T^(r-1+a)1 and grade is at most r+a. For s>=1 and j_i>=0 use the actual
expression
    M^j_0 B M^j_1 B ... B M^j_s D_a.
M attaches a leaf at the root, B adds a unary root minus gamma times
the original profile. Hence ordinary order p pays this word when
r+a+s+sum j_i<=p, against the exact polynomial-model moment
    Lambda_gamma,a,s(X_0^j_0 ... X_s^j_s)
      = ell[x^j_0 T(x^j_1 ... T(x^j_s T^(r-1+a)1)...)].
No scalar moment by itself gives this claim: the M operations record
the leaf clock of a different root along the high-child path.

Physically this is a signed atomic moment over all strictly descending
terminal paths i_0>...>i_s>a, at their clock tuple, with weight
    b_(i_0) L_(i_0,i_1) ... L_(i_(s-1),i_s) (D_a)_(i_s).
This holds with arbitrary old/terminal readout, even singularly large
coefficients. The old coordinates stay zero. At gamma=0 the model moment
is exactly
    1/(r-1+a)! integral_(0<X_s<...<X_0<1)
                            X_s^(r-1+a) prod X_i^j_i dX.
On any finite total-degree polynomial space its square moment matrix is
positive definite, by positivity on the open simplex. Its entries are
polynomials in gamma, so this holds for all sufficiently small positive
gamma independently of the actual clock values or weights.

In particular for
    d=floor((p-r-a-s)/2) >=0
the required rank, and hence the minimum number of terminal s-edge
path atoms ending beyond row a, is at least
    binom(d+s+1,s+1).                                              (1)
These are the minimum counts imposed by the indicated paid moment blocks,
not sufficient conditions for order, or an optimization of the total edge
count. There is a further exact fiber quota: multiply the polynomial
test space of degree <=d-e by any nonzero polynomial R(X_0,...,X_s)
of degree e<=d. Positive definiteness of the full degree-d model matrix
requires at least binom(d-e+s+1,s+1) paths surviving R. Choosing R as
a product of clock differences or of factors X_j-x_i can eliminate
particular path fibers. This is valid uniformly at small gamma even
when R depends on the actual clocks. The unfiltered rank obstruction
also holds except at finitely many algebraic diagonal values: a
necessary over-rank principal minor is a nonzero polynomial in gamma
as seen at zero. We do not assert generic positive definiteness of
the filtered test beyond the small-gamma interval.

## 2. A graph can meet (1) while missing ordinary order

A purely distributed two-band support has edges i->i-1 and i->i-2
when available, with cut rank <=2. On a contiguous tail of R slots
its s-edge count is
    sum_(j=0)^s binom(s,j) max(0,R-s-j).
The raw and shifted-tail profiles (1) all fit in this graph for
p<=min(20,2r-1). Here is a short general comparison, not a point
search. Put R=r-a, k=p-r-a; then k<=R-1 and k<=9, and for
d=floor((k-s)/2) one has R-s>=2d+1. If d=0 the consecutive
path suffices. If d=1 the j=0,1 terms give >=3+2s >=s+2.
If d=2 the j<=2 terms give
5+4s+3 binom(s,2) >=binom(s+3,2).
If d=3, k<=9 leaves s<=3, and the respective bounds from all
binary gaps are 13,24,44, versus 10,20,35.
If d=4 then s=1, giving 17>=15. Larger d is out of the paid
range. A bandwidth-one chain fails at the high targets of the
preceding seal, so two bands are the smallest bandwidth to
meet those raw profiles at those targets. This is a statement
about maximum path *capacity* of the support, not that arbitrary
nonzero coefficients there can realize the moments.

Two bands with equally spaced clocks also give an example of why
(1) alone is too weak: X_0-X_1 takes only two path values, so a
nonzero quadratic vanishes on every edge. If d>=2 at s=1,
positive definiteness rules this out even though the raw count
can pass. More generally the same argument applies to any
fixed set of <=d clock differences on those edges. No claim
about generic unisolvence of all the path tuples is inferred
from the count comparison.

Below we give a different lower-cut-rank graph with actual all-rooted
accuracy higher than the two-fan foothold and enough raw paths. It
does not assume that the two-band coefficient-fit problem is soluble.

## 3. A starting low-rank terminal matrix and its field

Choose the shifted-Radau terminal rule from the lane seal. Its last
clock is x_r=1-gamma, g(x)=1-gamma-x. The first r-1 clocks are the
simple real roots of the monic degree-(r-1) polynomial orthogonal
for g(x) dx. At gamma=0 this is the positive (1-x) weight, so all
roots are distinct interior and remain below x_r for small gamma.
The full terminal hull is -g times that orthogonal polynomial.
Its interpolatory b weights are positive and pay B(2r-1), as seen
also by the cardinal squares. In particular
    d^T=b^T g(C)=(b_i(1-gamma-x_i))_i,   d_r=0,
represents ell T on every polynomial through degree 2r-3:
ell TP=ell(gP). The material gate is b^T L=d^T (not an assumed
uniform shift of all rooted conditions).

Put m=(W_(r-1)(x_i))_i and tau_j=ell T^j W_(r-1). On scalar f let
u=h lambda/(1-gamma h lambda). The incoming scalar chart is exact
as a polynomial in u:
F_k(x)/y=sum_(j=0)^(k-1) u^(j+1) T^j1(x).
This persists in the cached version because each low mode is
literally unchanged at all scalar grades; the high modes are
recovered from the nodal values. Thus scalar Delta/y on the lane
is u^r (Id-uL)^(-1)m/(r-1)!, and scalar order 2r-1 follows
from b^T L^j m=tau_j for 0<=j<=r-1 and the clock moments.

Use *one shared cumulative response channel* on the first r-2
terminal rows: in this block put L_ij=a_i whenever j<i, with
nonzero row scalars a_i. This is a running sum of Delta_j,
not independently chosen fan coefficients. Its crossing cut
rank is one; its scalar Krylov columns from m form a basis
because every subdiagonal is nonzero and m_1!=0. As in the
two-fan synthesis, first choose the covector f on those r-2
rows by f^T L_1^j m'=tau_(j+2) for j=0,...,r-3. Then
choose row r-1 so d^T L_0=(f^T,0) on the prefix of length
r-1, and row r so b^T L=d^T on the terminal block. The
denominators d_(r-1) and b_r are nonzero. Denote the starting
matrix by L and the full covector b^T L² also by f^T,
understanding its zero extension. This gives the exact scalar
targets and all trees through r+2, independent of the row
scalars chosen. Its crossing cut ranks are <=3 (one shared
prefix channel and two independently fitted rows).

All operations are over the field generated by gamma, the actual
selected Laguerre prep clocks, and the real split terminal Radau
factor. This is the exact coefficient field as the clocks and gamma
are physical row sums and the diagonal. We choose gamma positive
rational sufficiently small and the a_i rational; none of the
following fits will adjoin another root.

## 4. A cap-r chart still has a small, exact off-cap mode space

The actual chart F_(r-1) need not agree with the full Laguerre chart
in grade r+1. Nevertheless the required mode space for its next
error is explicitly available without building the cap-(r+1)
kernel. Fix the selections of dimensionless Laguerre roots and
use their gamma multiples. Let `hat F_k` denote the cap-r cached
chart and `F_k^full` the full chart. Only in this section, write
D_k(x) for their grade-(r+1) polynomial difference.

At every selected layer-k node the two actual samples at grade
r+1 agree: the recursive stage observation at that grade depends
only on earlier-chart profiles and same-row child profiles of
orders <=r, which are paid by the cap and lower grade recursion.
Thus D_k vanishes at the selected nodes. Let
    L_k=max(0,2k-1-r)
be the number of reused low modes, and let low_k denote projection
to W_j with j<L_k. For L_k>0 the low part of D_k is
    low_k D_(k-1) + W_(L_k-1) times one raw vector.
Indeed the full charts k-1 and k have the same exact
low coefficients at grade r+1 except possibly that last reused
index: for j<=L_k-2 their paid band has r+1+j<=2k-2.
When L_k=0, D_k=0. The low-degree part just specified has a
unique polynomial completion of degree <k vanishing on all
selected nodes, by the same high-mode rank argument as for
the cached kernel. Call this linear completion J_k.

It follows constructively that D_(r-1) is a sum of at most
    b0 = r-1-floor((r+1)/2)
raw vectors times known polynomials P_i(x). Form these
polynomials recursively: at every compressed layer apply
J_k low_k to the previous polynomials, and add J_k W_(L_k-1).
No raw coefficient vector has to be computed. Combining with
the full-chart error band at grade r+1, all polynomial
coefficients of E^[r+1]= (F_*-F)^[r+1] thus lie in
    Ucal = span{ W_(r-2), W_(r-1), W_r, all P_i }.                  (2)
The full-chart modes just used are exactly those in its band
2(r-1)+1-(r+1)=r-2 through r. This argument neither assumes
paid equality outside the cap nor uses any previously proposed
explicit formula for the next defect vector.

Evaluation of Ucal is injective on any t distinct positive
terminal clocks for all small gamma, where t=dim Ucal and
the clocks have distinct positive limits. To prove it, the
operators defining the P_i commute with the substitution
x=gamma X, since W_j(x)=gamma^j W_j|_(gamma=1)(X) and the
selected sites scale in the same way. The mode span is the
dilation of a fixed finite-dimensional polynomial space
(individual nonzero scalar factors do not change its span).
Choose a degree-echelon basis with distinct leading degrees
d_1<...<d_t in that undilated space. The corresponding scaled
basis, multiplied by gamma^d_i, tends coefficientwise to
distinct monomials x^d_i. Their generalized Vandermonde is
nonzero on any t distinct positive points: a nonzero combination
of t such powers has at most t-1 positive zeros, by division
by the lowest power and Rolle induction. Hence this is a
nonzero exact small-gamma gate, not a numerical conditioning
assumption.

## 5. One triangular shear pays all rooted trees through r+3

This construction works for r>=11. Put K=t+1, so by Section 4
    K <= b0+4 <= r-3.
The first K terminal rows are inside the shared-channel
prefix. Choose its row scalars so Lm on those first K
coordinates is not in the evaluation span of Ucal. This
does not disturb any previous fit: on row i in the prefix
(Lm)_i=a_i sum_(j<i)m_j. The sum is nonzero for small
gamma, since the x_i have positive limits. Fix earlier
nonzero a_i and vary a_K; the determinant with last column
Lm is affine nonconstant in a_K, by the injective evaluation
on the first K-1=t points. A nonzero rational choice avoids
the one bad value, keeping scalar controllability.

Construct a vector u supported on the last three terminal
indices r-2,r-1,r, satisfying b^T u=d^T u=0 and u!=0.
There is a one-dimensional nullspace, and all three entries
of u are nonzero: d=b*g, b_i>0 and the clocks are distinct.
For example b_i u_i on these three indices can be the cyclic
clock differences. Also
    d^T C u=-b^T C² u !=0,
by the Vandermonde on {1,x,x²}. And f^T u !=0: f=b^TL²
vanishes on the last two columns, and its coordinate r-2
is nonzero since f^T L^(r-3)m=tau_(r-1) is nonzero at
small gamma and only that coordinate can see this power.

Now choose v supported on the first K terminal indices with
    v^T S P = (ell T² P - f^T S P)/(f^T u)    for P in Ucal,
    v^T Lm = (d^T C Lm - ell T(x T W_(r-1)))/(d^T C u),
where S P means sampling P at all terminal clocks. These
are an exact linear system of rank K by the preceding
evaluation and independence checks. In particular v^T m=0
since W_(r-1) is in Ucal and the scalar tau_2 is already paid.
Set
    R=Id-u v^T,  R^-1=Id+u v^T,   L_new=R L R^-1.
Disjoint ordered supports make these unit lower triangular
and keep L_new strictly lower, so its rows are physically
realizable in (2), with no extra stage or nonlinear virtual
evaluation. The fixed clocks do not change: every Delta in
(2) still begins at grade r for arbitrary strict L_new.

Using v^T m=0, b^T u=d^T u=0 gives, exactly,
    b^T L_new=d^T;
    b^T L_new^j m=tau_j for all the previous scalar j;
    f_new^T=b^T L_new²=f^T+(f^T u)v^T;
    d^T C L_new m=d^T C Lm-(d^T C u)(v^T Lm).
So the newly paid mixed gates are
    f_new^T S P = ell T² P   (P in Ucal),
    d^T C L_new m = ell T(x T W_(r-1)).                           (3)
All node values, linear systems and shears are in the old
Laguerre/terminal Radau root field; the actual row sums are
unchanged. No new field root or output reweight is hidden here.

Here is a verification that the gates pay **all** rooted
conditions through r+3. In the following write L for L_new
and f for f_new; retain d=b^TL. Use
    D P=S(TP)-L S P,   delta=D W_(r-1),   A_t=gamma Id+L.
The terminal exact derivative error F_* at the nodes minus
the actual H has grade >=r+1, and the exact state error is
D E + A_t [terminal derivative error], with E=F_*-F. The old
e_r input error is W_(r-1)e_r as previously. The first
terminal grade errors are
    err^[r+1]=delta U e_r,
    err^[r+2]=U D E^[r+1]+(A_t delta) U² e_r+(C delta) K_1(e_r),
where Uv=Df(y)[v] and K_1(v)=D²f(y)[f(y),v]. At grade r+3,
Taylor expansion of h f about the exact state gives exactly
    U D E^[r+2]+U A_t err^[r+2]
       + C K_1(D E^[r+1]+A_t err^[r+1])
       + (C² delta) K_2(e_r),
where K_2(v)=(D²f(y)[G_2,v]+D³f(y)[f(y),f(y),v])/2 and
G_2=Df(y)[f(y)]. This follows from the first two grades
of the exact state along each x_i. Terms quadratic in the
state error first occur at 2r+1>r+3 here.

All the displayed coefficients vanish in the weighted
error, for the following exact reasons.

* b^T D E^[r+2]=0 with no hidden incoming cap: that
  polynomial has degree <=r+1, and b^T L=d^T
  represents ell T through 2r-3 while b pays TP.
* Because E^[r+1] has all polynomial modes in Ucal,
  b^T D E^[r+1]=0 and d^T D E^[r+1]=0, the latter
  by (3) and d representing ell T on the T-applied
  modes. Since b^T C=x_r b^T-d^T, this kills both
  b^T A_t D E^[r+1] and b^T C D E^[r+1].
* Already b^T delta=d^T delta=b^T C delta=0 by the
  order-r+2 gates. Also f^T delta=0: T W_(r-1)=W_r/r
  belongs to Ucal and b^T L³m=tau_3 is scalar-paid.
  Hence b^T A_t² delta=0, and b^T C A_t delta=0
  by b^T C=x_r b^T-d^T.
* Finally
      b^T C² Lm=x_r b^T C Lm-d^T C Lm
                  =x_r ell(x T W_(r-1))-ell T(x T W_(r-1))
                  =ell(x² T W_(r-1)).
  The prior b^T C delta=0 justifies the first mixed
  equality, and the new gate in (3) the second.
  Quadrature therefore gives b^T C² delta=0, and
  b^T A_t C delta=-b^T C² delta=0 as required.

Quadrature pays every exact reference profile through r+3,
since r+3<=2r-1 in this range. The actual rooted-tree
error is zero through that grade by the proof above.
Thus ordinary >=r+3 and scalar and pure-clock orders
>=2r-1 hold at the same actual count
    floor((r+1)^2/4)-1+r.
For example r=11 means 46 stages, ordinary >=14, scalar
and clock orders >=21; r=12 means 53 stages, ordinary
>=15, scalar and clock orders >=23. These are not
ordinary order-20 tableaux or new unrestricted upper bounds.

This is low rank in the meaningful sense of crossing
chronological cuts. The full scalar depth requires L to
have rank r-1, so total matrix rank cannot be the desired
notion. The new cut rank is <=5: the old <=3 plus
    L_new-L = L u v^T - u v^T L,
two rank-one updates. The potential quadratic shear term
is zero since v^T L u=0 by separated supports.
There is no third independent fitted fan row.

## 6. Raw profile passed; actual full-order wall not passed

The actual shear leaves all edges in the initial complete
prefix of length n=r-3 and every subdiagonal edge. For
the latter, the earliest modified row is r-2, where
Lu is zero; also v^T L has zero in column r-3 because v
is supported in rows <=r-3 and L is strict. All later
subdiagonal columns lie outside the supports of v and
v^T L. The fitted fans had nonzero subdiagonals by the
top paid scalar moment. Thus even the conservative
subgraph (complete prefix n, followed by three consecutive
edges) has at least
    binom(n,s+1)+sum_(j=1)^min(3,s) binom(n-1,s-j)
                                     +max(0,3-s)
paths of length s. The appended term counts the paths
starting in those last three slots, which must follow
their consecutive edges until entering the prefix.
For n>=5 this passes raw (1) at a=0 for all p<=2r-1.
Indeed if n-s>=3 the first binomial alone suffices;
if s=n-2 the demand is at most binom(n+1,2) and the
additional terms binom(n-1,3)+binom(n-1,4) cover the
remaining n-1 after the first two terms. At s=n-1 and
s=n the demand is at most n+1 and n+2 respectively
and the tails give these. Larger s requires one path.
The proof for a shifted tail is identical until its
width R=r-a drops below 8; for r>=11,p<=20 one has
p-r-a<=R-2. At widths R=7,6,5 the only nontrivial
counts beyond one are met by the same formula
(respectively s<=3, s<=2, and s=1), and R<=4 has
only one-path demands. These observations concern raw
counts (not every fiber quota or exact moment).

There is nevertheless a robust all-tree obstruction to
ordinary 2r-1 at the unchanged count with this retained
incoming block, even if the entire terminal graph is
fully dense. It is the supported transport-rank staircase,
which is stronger here than the mere path count. Recall
the proof to distinguish it from scalar saturation.
Put q=r-1. The vector q!B^q1 vanishes on the incoming
block and has exact model W_q. From a supported W_j
carrier, B raises a mode; the operator
    M-(j+1)B-beta_j Id
gives the nonzero multiple alpha_j W_(j-1) by the
three-term recurrence. Thus at grade G>=q+1 the
supported model has all consecutive modes
    max(0,2q+1-G) <= j <= G-1.
Let Pi=[M,A]-A², whose model is zero and whose actual
diagonal -gamma² makes it invertible on the supported
coordinate space. At level l with G=p-2l, take as many
as min(2l+1, G, 2(G-q)-1) consecutive available modes.
Left tests 1,x,... up to one less than this number have
an invertible model moment matrix on those modes at
gamma=0, by positivity of weight x^(first index), and
hence for small gamma. In any dependence of the
Pi^l times carriers, invert its first left Pi power on
actual vectors, then use those paid tests: the greater
l terms have zero model, and degrees fit p. This proves
the exact necessary terminal row count
    sum_(l: p-2l>=q+1) min(2l+1,p-2l,2(p-2l-q)-1).               (4)
It does not matter how many extra paths L contains.

For p=2r-1, q=r-1, (4) exceeds r for r>=6. At r=6 it is
7; as r increases by one the corresponding earlier
blocks never decrease and the last 3-to-5 or 1-to-3
increase (with a new 1-block on even-to-odd transitions)
makes the strict gap persist. For the table comparison
at ordinary p=20, r=11 would need 19 terminal rows and
r=12 would need 15, versus their available 11 or 12.
At r<=10 the scalar depth 2r-1 is already too short
for ordinary 20 at small gamma; at r>=13 the physical
count of this retained-kernel architecture is already
>=61. Thus no rearrangement only of the terminal L
here proves a smaller ordinary p=20 upper. These
statements are small-gamma retained-block obstructions,
not unrestricted lower bounds. They apply a fortiori to
any claimed dense order p readout, since it includes the
unit-time ordinary output. The positive construction of
Section 5 pays ordinary order r+3 only; its low-order
dense chart still has the previous meaning.

Independent audit should separately check the cap-r
off-cap recurrence (2), the three all-rooted gates (3)
and their chronology under the shear, and the difference
between raw path capacities and the transport rank (4).
No feasibility of an ordinary order beyond the proved
lift is certified by showing enough paths or scalar poles.
