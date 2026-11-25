# Zero-output donors can vary the weighted suffix at a fixed clock

The [donor realization](../quadrature-donor-realization/realization.md)
fixes the visible weighted rule. The
[stopped-clock selector](selector-paid-stopped-atoms.md) separates the
mixed source test from the signed atom comparison. Together they give
a stronger conclusion: marked weighted columns can be prescribed freely
with the *entire physical clock vector* and all paid tree responses
unchanged, and a visible-clock test retains one exact hidden contribution.
These are mathematical statements about the actual tableau, not a
Lean result or a stage bound.

## Freely prescribed marked columns

Let $p\ge2$, and fix a scalar quadrature exact through degree $p-1$
over an ordered field $K$. Coalesce its contributing physical sites, retaining
one nonzero weight at each. In a tableau write $c=A\mathbf1$ for the
physical clocks, $x_i=1-c_i$ for the reflected clocks, $B(u)$ for the
grouped output weight at $u$, and $L$ for its support. Let $S$ be any
finite set of marked reflected clocks, possibly meeting $L$.

**Claim.** For any array $\Lambda:S\times L\to K$, a lower-triangular
tableau of actual reviewed [`HasOrder p A b`](../../../RKResearch/OrderConditions.lean)
can have the given quadrature and satisfy, simultaneously for every
$F\in K[X]$ and $a\in S$,
$$
 \sum_{x_i=a}\ \sum_{j>i} b_j A_{ji}\,F(x_j)
       =\sum_{u\in L}\Lambda(a,u)F(u). \tag{1}
$$
The full grouped suffix $N_F(a)$ includes the additional term
$D(a)F(a)$, where $D(a)=\sum_{x_i=a}b_i A_{ii}$. The row diagonals, the
full vector of physical clocks, the output weights, and all paid tree
responses at the outputs can be fixed as $\Lambda$ varies. The same
claim holds with **exact** order $p$. In particular it applies to strict
ERK and to SDIRK with any chosen positive common diagonal.

**Proof.** Use the donor induction through tree grade $p-1$.
In the last zero-output bank put a marked donor of physical clock
$1-a$ for each $a\in S$, and $p-1$ repair donors at distinct clocks
$z\in E$ disjoint from the marked and contributing clocks. For
$p\ge3$ the immediately preceding pure bank of size $p-2$ builds
every one of these rows by the original donor system. For $p=2$ each
leaf response is $1$, and the first row suffices to set each donor's row
sum while keeping its prescribed diagonal. The field is infinite, so
the disjoint repair clocks exist. Earlier helpers may repeat clocks:
the output rows do not take input directly from them.

Append one active row of weight $B(u)$ at physical clock $c=1-u$.
Its strict coefficient multiplying the marked donor at $1-a$ is
$\Lambda(a,u)/B(u)$. Do not connect two active rows. With prescribed
diagonal $d_u$, the remaining coefficients $w_{u,z}$ solve
$$
 \sum_{z\in E} w_{u,z} z^k=
 \frac{c^{k+1}}{k+1}-d_u c^k-
 \sum_{a\in S}\frac{\Lambda(a,u)}{B(u)}(1-a)^k,
 \qquad 0\le k\le p-2. \tag{2}
$$
This is an invertible Vandermonde system. Its first equation fixes
the clock. For a child $T$ of order $r\le p-1$, its donor responses
are $z^{r-1}/\operatorname{ff}(T)$, with $\operatorname{ff}$ the
forest factorial. The diagonal uses the already proved response for
this smaller child at the current output row. Equation (2) at $k=r-1$
then gives the pure child action $c^r/T!$, because
$T!=r\operatorname{ff}(T)$. Multiplying over the children proves
the actual pure row response through order
$p$. Output quadrature gives every required tree condition. Only
the active rows carry output, so their prescribed marked edges give
(1); a same-clock active row adds only its diagonal. No positivity
of the strict matrix entries is imposed.

For exact order, use $p$ repair donors and additionally prescribe
$k=p-1$ in (2) with an offset $\xi_u$ on the right. No paid tree
or marked entry changes. For the next tree with a single child
equal to the order-$p$ bush, that child's value at every stage is
its clock to the power $p-1$. The output parent value at $u$ is
$c^p/p+\xi_u$. Changing $\xi_u$ by one in any one nonzero-weight row
changes the factorial-scaled next condition by $p(p+1)B(u)\ne0$.
At least one of the two choices fails it, even if the next pure
bush passes. This leaves the marked block and all clocks fixed.

Consequently if $F(u)\ne0$ at some visible receiver, $N_F(a)$ can
take any value at each mark. Even a true stop root $F(a)=0$ leaves
this freedom when another visible receiver has nonzero profile
value. The complete pure weighted rule, not merely its support
size, therefore does not determine the suffix cancellation.

## The exact leftover term of a visible selector

Write $I_{u,v}$ for the difference of normalized formal primitives.
For any actual order-$p$ tableau, let $L=\{u:B(u)\ne0\}$ in the
reflected coordinate. An individually live group with zero
aggregate weight is outside $L$. At $a\in L$ set
$$
 Q_a(X)=\prod_{u\in L\setminus\{a\}}(X-u),\qquad
 h_i=Q_a(x_i)\mathbf1_{\{x_i\notin L\}},\qquad
 \mathcal L_a(F)=\sum_j b_j F(x_j)(Ah)_j .
$$
If $|L|+\deg F+1\le p$, the
[paid actual mixed identity](selector-paid-stopped-atoms.md#1-the-actual-grouped-sources)
applied to $Q_a$ gives
$$
 B(a)I_{0,a}F=N_F(a)+\frac{\mathcal L_a(F)}{Q_a(a)}. \tag{3}
$$
Indeed $Q_a$ kills the other live groups, while the unisolated sum
is $\sum_{x\notin L} Q_a(x)N_F(x)=\mathcal L_a(F)$. There is no
division by an individual output weight or a diagonal.

With $N_F(a)=0$, the true local zero is equivalent to
$\mathcal L_a(F)=0$. One sufficient restriction is that $(Ah)_j$
vanish at every receiver with $b_jF(x_j)\ne0$, but a single weighted
cancellation suffices; requiring all hidden columns to vanish is
unnecessary. Even nonzero source and leakage may cancel in (3).
The marked-donor construction shows that this is an actual
unidentified term: with the pure weighted rule fixed, a change
$\Delta N_F(a)$ is compensated by
$\Delta\mathcal L_a(F)=-Q_a(a)\Delta N_F(a)$ whenever the
degree guard holds. In the prefix direction only rows with
individual output weight contribute, so that clock cover suffices
for the mixed selector at its paid degree; an aggregate cover
additionally requires accounting for any signed canceled groups.

## The atom comparison remains separate

The literal pure tilt $\widehat\mu_x=B(x)F(x)H(x)$ is unchanged by
every donor variant. Suppose a different signed law $\mu$ represents
$I_{0,1}(F H Q)$ through test degree $q$ and has $r$ off-stop sites.
Let $k$ count the nonzero off-stop sites of $\widehat\mu$. The
[independent comparison](selector-paid-stopped-atoms.md#2-independent-degree-budgets-for-source-and-atom)
identifies the laws under
$r+k\le q$ and $\deg(FH)+r+k+1\le p$: one can select each site in
their coalesced union, which contains at most $r+k+1$ sites.
Matched weights may reduce the charge. The usual bracket cost
already pays $2r$, so $k\le r$ covers the analytic charge, but
not the pure RK charge. If comparison is paid, a true stop root
erases $\mu_a$; (3) does not assert that comparison.

For a true-stop-root control over the real algebraic field, take
$p\ge7$ and $m=\lceil p/2\rceil$ interior Gaussian sites. Positive
definiteness of the rational interval moments gives the monic
orthogonal polynomial of degree $m$. If it had fewer than $m$
interior sign-changing roots, multiplying by the product of those
roots would give a nonzero fixed-sign integral, contrary to
orthogonality. Thus the roots are simple, interior and algebraic.
Lagrange integration pays degree $2m-1$ by polynomial division,
and the weights are positive by exactness on the squared basis.
Use any reflected visible stop $a$
and the exact-order construction with zero strict block there.
Set $F=P=(X-a)^2$, $W=1$, and $H=1-X$. The full source vanishes
and $m+3\le p$, but the local primitive is $a^3/3>0$; (3) gives
the nonzero hidden term. The one-atom analytic rule supported
just at $a$ has exact tests through $q=0$ with mass
$$
 I_{0,1}((1-X)(X-a)^2)=\tfrac12(a-\tfrac13)^2+\tfrac1{36}>0,
$$
although the literal pure tilt is zero there. This satisfies
the sign, mesh, pole and degree guards of the
[scalar stopped setup](../../lean/RKCert/ReviewedNative/FiniteStoppedBracket.lean)
with sign $\tau=1$, empty off-stop and cut lists, test cost $0$ and grid degree $3$,
but **not** the true local-zero premise. It demonstrates two unpaid
steps of the shortcut, not a counterexample to the stopped bracket.

## Exact replay

Run `python3 check-donor-suffix-leakage.py` from this directory.
The [stdlib checker](check-donor-suffix-leakage.py) verifies actual
rational rooted-tree conditions for ERK and SDIRK at exact orders
three and four. Two different marked column assignments keep the same
clocks and weights. At order three the next pure bush still passes,
but the unary-bush condition fails. At order four the grouped source
moves from $0$ to $25/63$ and the leakage from $-1/12$ to $1/63$
while the weighted local value remains $1/3$.
The [receipt](donor-suffix-leakage.receipt) is exact stdout; the proof
above, not a search or extrapolation from these examples, gives the
uniform result.
