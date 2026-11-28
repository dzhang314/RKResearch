# Grouped fourth-head cuts on the invisible one-clock DIRK11/13 face

**Results.** Work in the normalized DIRK11/13 boundary with one numerical
forward cubic-dirty clock and all its physical rows of weight zero
(\(r=0,d=1\)). Put \(h=(A-\xi/2)g\), with \(g=Ac^2-c^3/3\).
If the weighted fourth head \(\beta h\) has zero aggregate at every
numerical clock but the grouped square \(\beta h^2\) is nonzero, there
must be **exactly one physical cubic-dirty row**. In that remaining
one-row case a multi-label genuine reverse cubic forces either five
ordinary marked pairs or four such pairs and one invisible nondirty
slack row. Independently, on the entire grouped-zero fourth-head face,
two repeated physical signature contrasts are impossible. The argument
uses no order or positivity on the tableau's coefficient field once
the normalized characteristic-zero hypotheses hold. It does not exclude
all invisible one-clock candidates or change real DIRK11 **13–14**.

## 1. The remaining grouped invisible ingress

Use the actual rooted order and rank hypotheses in the
[signed cubic census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md):
thirteen literal lower triangular stages, \(C(2)\), genuine reflected
\(D(1),D(2)\), grade-six surplus, actual origin \(O\) and terminal
\(T\) at \(0,1\), and the terminal column and live terminal weight
there. The exact ranks include \(f_4=2,f_5=3,f_6=5\),
\(e_5=9,e_6=11,e_7=12\), and \(e_T\in E_6\setminus E_5\).
Here \(E_j,F_j\) are the true rooted and zero-profile spaces, and
\(e_T\) is the literal terminal cardinal.

The existing [grouped reverse debit](../causal-profile-reduction/dirk-order11-thirteen-zero-one-low-dirty.md)
rules out \(d=4\), gives the only possible counts \(d=z=5,6\)
for \(d\ge5\), and discards \(d=5,z=6\) before any assumption of
distinct physical clean weights. The [five](../dirk11-thirteen-invisible-five/README.md)
and [six](../dirk11-thirteen-invisible-six-no-late-completion/README.md)
cases have separate closures, and the normalized Hermite growth
rules out \(d=2,3\). This leaves the single physical **numerical**
dirty clock \(\xi\), not necessarily one physical row. In this
packet \(z\) counts physical nonzero-\(g\) rows; all have output
weight zero, and \(z\ge1\).

The forward part of the [one-local rank argument](../dirk11-thirteen-local-active/README.md#1-one-physical-cubic-clock-and-the-next-true-head)
does not need an active cubic. In a literal prefix with clocks just
\(0,\xi\), the first nonzero stage pays diagonal \(\xi/2\), so
\(\xi\ne0\) and \(g=\xi^3/6\) at every \(\xi\) in that prefix.
On the first stage of clock \(a\notin\{0,\xi\}\), \(g_a=0\) and
the actual first two scalar stage moments give the aggregate \(\xi\)
tap \(a^3/[6\xi(a-\xi)]\). Hence \(h_a=\xi^2 a^3/[36(a-\xi)]\ne0\)
and \(F_4=\langle g,h\rangle\). Such an \(a\) exists by the ordinary
moment support bound. Since \(Cg=\xi g\), the two native inclusive
Hermite bounds, **outgoing from \(F_4\)** and **incoming to
\(F_5\)**, exclude clock invariance of each: the gain would be two,
not the actual one. Thus \(F_5=\langle g,h,Ch\rangle\) and
\(U_4=\langle g,h,Ch,C^2h\rangle\) has dimension four in \(F_6\).
Both actual endpoints are \(g=h=0\): at the origin this is literal,
and at the terminal use \(e_T\in E_6\), the paid \(h\) test and
live terminal output weight.

For a numerical clock \(s\), put
\[
 \mu_s=\sum_{c_i=s}b_i,\qquad
 \alpha_s=\sum_{c_i=s}b_i h_i,\qquad
 \nu_s=\sum_{c_i=s}b_i h_i^2 .
\]
These are ordinary, fourth-head and square aggregates. Individual
rows may still have nonzero weights even when any aggregate is zero.
The main result assumes \(\alpha_s=0\) for every \(s\), and treats
\(\nu\not\equiv0\); later sections record conclusions independent
of the latter assumption.

## 2. Terminal separation and the exact square slot budget

The genuine terminal residual is
\(e_T-H_T(c)\in F_6\) with \(H_T(X)=30b_T XJ_4(X)\).
If it lay in \(U_4\), at every weighted nonterminal clock outside
\(0,1,\{J_4=0\}\) its nonzero value would force every active
physical row there to have the same live \(h\); all such rows
have \(g=0\) by invisibility. If its \(h\)-multiplier vanished,
no active row could be present. The grouped \(\alpha_s=0\)
therefore removes all ordinary mass at those clocks. But then the
true ordinary degree-ten test \(X(1-X)J_4^2\) has zero reading,
contrary to its rational integral \(1/330\).
Thus the terminal residual is independent, and the actual decomposition
is
\[
 E_6=\mathcal P_5(c)+\langle g,h,Ch,C^2h\rangle+K e_T .
\]
Separation of the pure degree-five part is the origin read and the
fixed rational \(X\,dX\) Gram on degree at most four.

The actual \(c^6\) column now gives a monic sextic \(M\) with
\[
 M(c)=a_0 g+L_2(c)h+\kappa e_T,\qquad\deg L_2\le2 .
\]
Group the weighted reading, using \(b_i g_i=0\) individually and
\(\alpha_s=0\). For \(s\ne1\) a live \(\mu_s\) forces \(M(s)=0\).
There are at least five live nonendpoint ordinary mass labels: if
there were at most four their nodal polynomial would vanish in
all the fixed rational \(X(1-X)dX\) Gram tests of degree at most
ten. These tests are nonsingular over every characteristic-zero
field. The actual origin gives another root \(0\), so these are
exactly the six roots of \(M\), \(M(1)=\kappa\ne0\), and
\(\mu_1=b_T\). This gives seven mandatory nondirty physical slots,
one at each live nonendpoint ordinary clock and the real origin
and terminal, independently of the physical origin weight.
If any nonterminal weighted row has clock 1, its \(h\) is a common
nonzero value forced by \(M(1)=L_2(1)h_i\). Since \(\alpha_1=0\)
and \(h_T=0\), it follows that \(\nu_1=0\).

The true three square moments \(\sum_s \nu_s s^j=0\),
\(j=0,1,2\), are paid by degrees \(8+j\). Hence nonzero
\(\nu\) has at least four labels. At a pair of physical weighted
\(h\)-rows with \(b_0h_0+b_1h_1=0\), the identities
\[
 \nu= -h_0h_1(b_0+b_1)=b_0h_0(h_0-h_1)
\]
show that a nonzero square requires a live ordinary mass and
distinct nonzero \(h\) values. Thus a \(\nu\)-live nonendpoint
label of zero ordinary mass requires at least three physical
nondirty rows; two weighted contributors alone would not suffice.
At a \(\nu\)-live ordinary interior label at least two physical
rows are needed (one extra beyond the seven mandatory slots);
at a \(\nu\)-live origin label at least two rows are needed
**besides** the actual origin. These three categories are disjoint
from the \(z\) physical dirty rows even when they share a clock.

If \(q\) is the number of nonzero square labels, \(o\in\{0,1\}\)
its origin count and \(x\) its nonendpoint zero-mass count, the
exact budget is
\[
 7+z+q+2x+o\le13,\qquad z\ge1,\quad q\ge4 .
\]
It forces \(z\le2,\ x=0\) and at least three live nonendpoint
square labels. Each such label is a root of \(M\) with some
nondirty row having live \(h\), hence is a root of \(L_2\).
Therefore \(L_2=0\). All \(g=0\) rows now have one of the
seven ordinary labels, and only the literal terminal can be
a \(g=0\) row at its terminal label 1. Nothing prevents
\(\xi\) from sharing an ordinary label.

## 3. Two invisible cubic rows are impossible in this square branch

Suppose \(z=2\). Equality in the budget gives **exactly four**
marked ordinary nonendpoint pairs, one unmarked ordinary interior
singleton, and the two actual endpoints. At a marked pair both
ordinary physical weights and both \(h\) values are live; the
two \(h\) values differ. All nondirty singleton \(h\) values are
zero by \(\alpha=0\) and their live weight or actual endpoint.
The only additional two physical rows are the unweighted cubic
dirties at \(\xi\); they may have arbitrary, unequal cubic values,
and may share one of the other numerical clocks.

Let \(Y=1-c,\ N=A^{\mathsf T}\) in literal reverse order,
\(G=NW(Y^2)-W(Y^3/3)\) the genuine weighted reverse cubic
and \(W(P)=b_{\rm wt}P(Y)\). Put \(U_0=E_6^\perp\) (dimension
two). The actual orders give \(G\in E_7^\perp\), \(YG\in U_0\),
and \(\beta h\in U_0\). The row \(G\) is nonzero on some
weighted nondirty coordinate: take the first active reverse
nonzero clock. Earlier active rows have zero reflected clock;
the genuine first moment gives \(d=y/2\) and the cubic
is \(b_i y_i^3/6\ne0\).

The two cubic carriers have zero **dirty** \(G\) and \(Gh\)
aggregate. In fact the actual reads of \(g,g^2,gh\) by \(G\)
are zero (grades \(3,6,7\)); they involve only these two
physical rows. If the two \(g\)'s differ, the first two reads
kill each \(G\) coordinate by a \(2\times 2\) Vandermonde.
If equal to a live value, \(Gg\) and \(Ggh\) give the two
asserted zero aggregates directly. This argument stays valid
when the dirty clock equals a clean pair clock.

* **If \(G\) uses multiple numerical labels**, then \(G,YG\)
  are independent, so \(\beta h=\ell(Y)G\) for an affine
  \(\ell\ne0\). At each of the four marked pairs \(\ell\)
  is live by the actual nonzero \(\beta h\) coordinates.
  Grouping gives \(Gh\) mass \(\nu_s/\ell(1-s)\ne0\) at
  each marker. Contributions at other labels vanish: all
  nondirty \(h\) values there are zero, and the dirty \(Gh\)
  mass was just killed. But \(G\) annihilates \(hY^j\) for
  \(0\le j\le3\), all in \(E_7\). Four distinct nonzero
  \(Gh\) masses cannot satisfy these four exact moments.
* **If \(G\) uses only one numerical label**, its \(1,h\)
  reads vanish at that label. Remove the already zero
  dirty aggregates. At a nondirty singleton the \(1\)
  read kills \(G\); at a marked pair the two unequal
  \(h\) values make the \(1,h\) reads injective. Hence
  every weighted coordinate of \(G\) is zero, contradicting
  the genuine reverse pivot.

Thus \(z=2\) is impossible, leaving **\(z=1\)** within this
grouped square branch.

## 4. Exact one-row envelope and independent signature cut

With \(z=1\) the \(Gg\) read kills the unique dirty \(G\)
entry. If \(G\) has multiple labels, \(\beta h=\ell(Y)G\)
as above. The grouped sums of \(G\) all vanish: all away
from the possible unique affine root vanish by \(\alpha=0\),
and at the root the total \(G1=0\) kills any remaining sum.
If \(q=5\), the budget consists of five marked live
interior pairs and the two endpoints, plus the single
dirty. If \(q=4\), the four nonzero \(Gh\) masses again
need at least one other \(Gh\)-live label by the four paid
moments. The extra label must be a root of \(\ell\), so
all weighted \(h\) at it is zero. Since the unique dirty
contributes no \(Gh\), a **separate unweighted nondirty**
row with nonzero \(h\) and \(G\) is necessary there.
An origin marker would consume the only spare slot and is
therefore impossible. So there are four marked interior
pairs and one unweighted nondirty slack row, sharing an
unmarked ordinary label \(\ne1\); it has opposite \(G\)
to that label's ordinary representative. Numerical overlap
with \(\xi\) is not excluded. If \(G\) is one-label,
the \(1,h\) reads instead require at its live weighted
support label at least three nondirty rows, or two
nondirty rows with the same \(h\); a singleton or a pair
of different \(h\)'s is impossible. These are not
existence claims or exclusions of all one-row cases.

Independently, on the entire grouped-zero \(\alpha\) face
(including \(\nu=0\)), two repeated physical signatures
cannot supply two independent contrasts. Use the exact
signature \((c_i,g_i,h_i,e_T(i))\), not a numerical
clock alone. Every \(E_6\) vector is constant on each
signature by the paid decomposition. The space of
covectors with zero sum on each class lies in \(U_0\);
two independent contrasts would exhaust its dimension
two. In that case put each signature's whole output
weight on its **last chronological member in reverse**
and subtract the old-to-new weight difference as a mask.
At every scalar polynomial \(P\) this mask annihilates
\(E_6\) because the polynomial is constant within each
signature. The \(\beta\)-weighted ordinary quadrature
sums are unchanged, even if some classes have zero
aggregate.

There are at least two distinct live nonzero reflected
clocks among these representatives. Sample the complete
signature classes of the first two such numerical debuts
\(u,v\), not a presumed single physical receiver. The
weighted input \(Y(Y-u)(Y-v)Q(Y)\), \(\deg Q\le1\), on
the concentrated weights is zero throughout the
inclusive slice; all members of each sampled signature
are within that slice by choice of representative.
Their true corrected primitive errors in
\(Z=E_5^\perp\cap\{T=0\}\) have full signature sums
\(-\mu_\sigma I P(u)\) and \(-\mu_{\sigma'} I P(v)\).
These two reads annihilate \(U_0\) and are independent
on the affine \(Q\) by the nodal determinant
\(u^3v^3(u-v)^3/120\). But \(\dim Z/U_0=1\).
This is precisely a
[native grouped reverse cut](../../lean/RKCert/ReviewedNative/DIRKOrderElevenThirteenGroupedReverse.lean)
with a refined physical partition. It rules out two
repeated signature pairs or one repeated triple, not just
opposite-weight pairs. A single repeated signature
contrast is not ruled out by this argument.

## 5. Neighboring fourth-head cases

If both \(\alpha\) and \(\nu\) group to zero, each nonzero
local restriction of \(\beta h\) to one numerical label
annihilates the entire \(E_6\) decomposition, by those
two grouped identities and \(b_i g_i=0\). At most two
such disjoint local rows can be nonzero. Each physically
weighted \(h\)-label costs at least two extra nondirty
slots beyond the seven ordinary slots: two \(h\)-live
weights with \(\alpha=\nu=0\) would have common \(h\)
and cancel their ordinary mass, so a live ordinary
nonendpoint of that kind needs an additional row.
Thus there are at most \(\min(2,\lfloor(6-z)/2\rfloor)\)
physically weighted \(h\)-labels in this branch. It
remains open, including the pointwise zero \(\beta h\).

If grouped \(\alpha\ne0\), its seven scalar moments
through degree six require at least eight numerical
labels. There are at most \(11-z\) physical nondirty
nonendpoint slots (excluding the actual endpoints, where
\(h=0\)). For \(z\ge3\) only the exact \(z=3\),
eight-head singleton allocation can satisfy this count.
Let \(S\) be those eight labels and \(L\) their monic hull.
The ordinary barycentric identity gives
\(\alpha_s=\lambda/L'(s)\), \(\lambda\ne0\).
The three square moments imply the interpolant of
\(\nu_s/\alpha_s=h_s\) on those eight singleton heads
has degree at most four: applying the leading-coefficient
barycentric read to \(1,X,X^2\) kills its top three
coefficients successively. Call it \(F\).
Every weighted nonendpoint physical row is one of the
heads in this tight count. For each \(P\in\mathcal P_4\),
\(\beta[X(1-X)FP]\) therefore equals
\(\beta[X(1-X)hP]=0\), including any numerical endpoint
contacts (both vanish there). The ordinary degree-ten
Gram for \(X(1-X)dX\) forces \(F=0\), contradicting
the live singleton heads. Thus **grouped \(\alpha\ne0\)
requires \(z\le2\)**, distinct from the grouped-zero
square closure and not a full \(z\le2\) claim for all
invisible one-clock arrays.

## Replay and Lean scope

**python3 verify.py** independently checks the exact
rational Gram and terminal integral, first off-core
literal two-moment identity, pair and dirty read
identities, the four-label selector and every integer
slot possibility. The four marked algebra lemmas passed
Lean/Mathlib 4.36.0. The two core slot lemmas, without
Mathlib, passed Lean 4.34.1, 4.35.0, 4.36.0 and
4.37.0-rc1. All reported axioms are standard. The true
graded ingress, grouped mask and nonexistence scope
above are not a single Lean HasOrder endpoint theorem.
