# Signed dirty-clock inventory for DIRK order 10 at eleven stages

Let $\boldsymbol{g}=A\boldsymbol{c}^{\odot2}-\boldsymbol{c}^{\odot3}/3$, where powers of the stage node vector $\boldsymbol{c}$ are componentwise. Write $r=\#\{c_i:b_i g_i\ne0\}$ for the
number of distinct labels of individually active dirty stages,
and $z=\#\{i:b_i=0,\ g_i\ne0\}$ for the number of ghost dirty
physical rows. No ordering or positivity is used. The
unrestricted stage interval is still 11–12.

The native Lean theorem **dirty_labels_small_or_high** proves
$r\le2$ or $r\ge8$. The stronger low-branch bound is $6+2r+z\le11$.
Section 2 mathematically eliminates $r=2$ over every paid field.
With the separate high-support census and eight-label obstruction,
this leaves only $r=0,1$ in characteristic zero and the other paid
fields outside characteristics 137, 62969, and 112249. These are
surviving branches, not constructions.

## 1. Signed inventory on actual clock fibers (native Lean)

The first paid defect moments are $\sum b_i g_i c_i^k=0$,
$0\le k\le6$. For $r\le7$, a degree-$r-1$ Lagrange nodal
polynomial isolates the total signed mass $\sum b_i g_i$
on each distinct dirty label. A single active dirty member
cannot cancel, so each label needs at least two. The two
physical endpoints are clean, giving $2r\le9$ and immediately
excluding $r=5,6,7$. Ghost dirty rows cannot change a signed
mass or supply an active member, and repeated clocks have
already been grouped.

For $r\le4$, the second moments $\sum b_i g_i^2 c_i^k=0$,
$0\le k\le3$, likewise isolate each label. An exactly-two
fiber then has equal $g$ and opposite $b$, from
$w_1+w_2=w_1g_1+w_2g_2=0$ and $w_i=b_i g_i\ne0$.
Remove any two chosen physical rows per dirty fiber, and all
ghost dirty rows. Let $T$ be the distinct clocks of the
remaining stages. A clock absent from $T$ has no clean active
row, and either no dirty active row or exactly the two chosen
members, whose ordinary mass cancels. Thus $T$ contains all
nonzero aggregate quadrature masses, and $1\in T$ from the
actual clean terminal, even if its aggregate mass vanishes.

An order-ten quadrature with possible support $T$ and $1\in T$
requires $|T|\ge6$. If $|T|\le5$, let $P$ be the monic nodal
polynomial of $T\setminus\{1\}$ (degree at most four). The six
paid tests of $P$ against $x^k$, $0\le k\le5$, equal the same
scalar, since only clock 1 can contribute. The reviewed
unanchored constant-Cauchy lemma forces that scalar to zero.
The first five tests then force $P=0$ by the ordinary square
Cauchy matrix, a contradiction. Hence $11-2r-z\ge |T|\ge6$.
In particular $r=3,4$ are impossible.

The native terminal-clean input is not assumed. The saturated
reverse space at index three has dimension two, annihilates
the rank-nine $E_5$, and vanishes at the terminal coordinate.
Its annihilator is therefore exactly $E_5$ and contains the
terminal indicator. The paid product of this indicator and
$g$, together with the individually nonzero terminal weight,
gives zero terminal defect.

## 2. Two active dirty clocks are impossible (mathematical)

Let $D$ be all physical dirty clock labels, including
unweighted ones. If $r=2$, the inventory gives at most one
ghost dirty row, so $|D|=2$ or 3. The preceding proof gives at
least six distinct physical clocks, hence at least two
distinct nonzero clocks outside $D$.

The native ranks $\dim F_4=2,\dim F_5=3$ give
$U=F_4=g\mathcal P_1(c)$ if $|D|=2$, or
$U=F_5=g\mathcal P_2(c)$ if $|D|=3$. In either case this is
exactly the space of columns $g_i\varphi(c_i)$ for free values
of $\varphi$ on $D$, by interpolation. Here is the bounded-degree
inclusive Hermite proof; it works with paid inverses 1 through
5, rather than imposing the CharZero interface of the general
native Hermite theorem.

A nonzero clock has **failed** in a physical prefix if no
column in $U$ is identically 1 at that clock throughout the
prefix. A failure persists; every nonzero clock outside $D$
fails at its first appearance. Select the first two distinct
nonzero failures $a,b$ and truncate the prefix *including*
the row where $b$ fails. Every other nonzero clock is still
maskable on that prefix, so has a common nonzero $g$ there.
Put $H(x)=x(x-a)(x-b)$. Choose $m$ on $D$ by setting it to
zero at the roots of $H$ and dividing $H$ by the common
$g$ at the other prefix clocks; use zero on unused clocks.
Thus $g_i m(c_i)=H(c_i)$ on the inclusive prefix.

For each polynomial $q$ of degree at most one set
$L(q)_i=g_i m(c_i)q(c_i)$ and let
$$
 D(q)=I(Hq)(c)-A(Hq)(c)+A L(q),\qquad I(P)(x)=\int_0^x P .
$$
The first two terms are defects of grade at most five from
the native monomial identities and paid inverses. If
$L(q)\in F_4$, also $D(q)\in F_5$. Triangularity including
the diagonal ensures that $D(q)$ agrees with $I(Hq)(c)$
throughout the prefix. If $D(q)\in U$, the primitive
cannot be nonzero at either failed clock, since rescaling
$D(q)$ would give the forbidden prefix mask. It vanishes
at $0,a,b$, and so does its derivative $Hq$. Three
distinct double roots cannot fit degree at most five,
hence $q=0$.

If $U=F_4$, this injects the two-dimensional $q$ space into
$F_5/F_4$ via $D$. If $U=F_5$, it injects into the same
quotient via $L$, since $L(q)\in F_4$ implies $D(q)\in U$.
Each contradicts $\dim F_5/F_4=1$. This bounded-degree
adapter is mathematical, not yet a Lean theorem.

## 3. A remaining one-live-label skeleton (mathematical)

The same bounded Hermite argument forbids $|D|=2,3$ for
$r=1$. If $|D|>1$, there are consequently at least three
ghost dirties. Inventory forces exactly three, all with
different labels outside the live dirty clock. Exactly two
active dirty rows have equal $g$ and opposite weights.
Indeed, with three dirty active rows, the three paid moments
in $g,g^2,g^3$ kill their ordinary aggregate by interpolation
on at most three nonzero $g$ values. Then at most five
clean active clocks can remain. With four or more active
dirty rows, allowing their single clock as a contributor
still leaves at most five possible clocks. Both violate the
terminal-containing six-clock test.

Exactly six distinct active clean clocks therefore carry
all quadrature; they are 0, 1, and the four roots of the
shifted $J_4$ from the eight-label note. This follows by
multiplying their interior nodal product by $x(x-1)$ and
using its four paid unit moments. A dirty label may coincide
with a clean label.

There is a further chronology in this branch. The six
clock powers through degree five are independent on the
six clean rows; $g\mathcal P_3(c)$ adds four independent
columns supported on the four dirty labels. Thus $E_6$
has rank ten: the active dirty pair contrast $\ell$
annihilates $E_6$ by the cubic payment and is its entire
annihilator. The genuine reflected cubic defect is nonzero
and proportional to $\ell$. Its last nonzero component is
at the last active row with clock other than 1 by $D(2)$
and triangularity. The later pair row is therefore after
all nonterminal clean rows, and its clock is not 1.

No ghost dirty row can follow that later pair row. Otherwise
$\ell A$ vanishes at that ghost and annihilates $E_5$.
Its four dirty-label masses after multiplication by $g$
kill powers 0, 1, 2, so zero at one label kills all four
masses. The row $\ell A$ is then zero at every ghost and
proportional to $\ell$ on the pair. Annihilating the clock
powers through degree five forces its entries on the six
distinct clean rows to be zero as well. If $\ell A$ were
proportional to $\ell$, the equality subspace of the pair
would be invariant under $A$ and componentwise products:
all rooted tree columns would agree at the pair. Folding
the later column and weight into the earlier stage and
deleting the later row would preserve triangularity and
order while removing one stage, contrary to the native
11-stage floor. Hence the later pair row is physical
stage 10 (one-based).

The first clean row with nonzero clock must also follow at
least three distinct dirty labels. The grade-five defect
space is $g\mathcal P_2(c)$, so both $Ag$ and $A(Cg)$
vanish at that clean row. With at most two preceding dirty
labels those two tests kill the sums of incoming taps from
each, since $g$ is constant and nonzero within each dirty
group. Only its own nonzero clock and clock zero remain,
so its $C(2)$ and $C(3)$ equations would force its diagonal
to equal both $c/2$ and $c/3$. Thus the first noninitial
clean stage is physical stage 5 or 6; at most one dirty
row lies between it and stage 10. This is not an exclusion.
The one-physical-dirty-clock case is separate.
