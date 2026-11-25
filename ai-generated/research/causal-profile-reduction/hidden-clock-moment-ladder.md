# When hidden weighted clock columns cost no selector degree

This is an exact finite criterion for the actual tableau, not for its
quadrature support alone. The [mixed source identity](selector-paid-stopped-atoms.md#1-the-actual-grouped-sources)
and [visible selector with hidden leakage](donor-suffix-leakage.md#the-exact-leftover-term-of-a-visible-selector)
are the starting point. We use the reviewed
[`HasOrder p A b`](../../../RKResearch/OrderConditions.lean) throughout.
The new conclusions are a simultaneous paid-moment test, a support and
sign threshold for the weighted residual, and sharpness of that threshold
on actual explicit and common-diagonal methods at every even order.
This is a mathematical proof, not a Lean result or a stage bound.
No signs are assumed on the strict matrix entries.

## 1. Group the actual columns before testing them

Work over an ordered field of characteristic zero. Set $c=A\mathbf1$;
write $\mathcal C$ for the distinct physical clocks, $B(u)=\sum_{c_j=u}b_j$,
$L=\{u:B(u)\ne0\}$, $n=|L|>0$, and $H=\mathcal C\setminus L$.
Define the weighted clock matrix
$$
 M_{u,x}=\sum_{j:c_j=u}b_j\sum_{i:c_i=x}A_{ji}.
$$
Thus $M$ maps a clock-constant input to the actually weighted, grouped
receiver rows. In particular $\sum_x M_{u,x}=uB(u)$, whether or not the
individual $b_j$ at $u$ cancel. The full weighted column at $x$, tested
by a receiver profile $F$, is
$$
 N_F(x)=\sum_u M_{u,x}F(u),\qquad \rho_F=N_F|_H.
$$
The diagonal and same-clock strict edges are included. There is no
hidden weighted column exactly when $M_{\mathcal C,H}=0$. This does
not require each hidden stage to be disconnected, nor does the absence
of its own output weight imply it. For a finite check let $U$ cover
receiver clocks with individually nonzero $b_j$; then $M_{u,x}=0$
outside $U$. Testing $N_F(h)$ for all $h\in H$ and
$F=1,X,\ldots,X^{|U|-1}$ is equivalent to $M_{\mathcal C,H}=0$:
the evaluation matrix on the distinct receiver clocks is invertible.
One can instead use Lagrange profiles on $U$ to read the individual
matrix entries. In particular $U$ must not be silently replaced by $L$
when signed outputs cancel at a clock.

Use $I_{a,b}F$ for the endpoint difference of formal primitives.
For the suffix define $D_a(F)=B(a)I_{a,1}F-N_F(a)$ at $a\in L$.
For all $Q,F$ with $\deg Q+\deg F+2\le p$, actual order gives
$$
 \sum_{h\in H}\rho_F(h)Q(h)=\sum_{a\in L}D_a(F)Q(a). \tag{1}
$$
Indeed the [reviewed mixed bushy moment](../../lean/RKCert/ReviewedNative/BushyMoments.lean)
first gives $\sum_{u,x}M_{u,x}F(u)Q(x)=\sum_uB(u)F(u)I_{0,u}Q$.
The reviewed pure bushy moment integrates this last polynomial and
$Q(X)I_{X,1}F$, both of degree at most $\deg Q+\deg F+1$.
Their formal integrals agree by the primitive product rule. This gives
(1), without any order predicate on a transposed tableau. The prefix
version uses $N_F(x)=\sum_u M_{x,u}F(u)$, $I_{0,a}F$, and the first
mixed equality directly. The entire finite test below applies with
that change; its hidden slice then belongs to rows of $M$, not columns,
and the profile sees the clock coordinates of the input columns.
For a reflected suffix substitute $F(1-X)$ in the physical test and
$a_{\rm refl}=1-a$; all degrees and counts are unchanged.

## 2. The exact simultaneous moment ladder

Fix a receiver degree limit $d\ge0$ and suppose the visible selectors
are paid: $n+d+1\le p$. Put
$$
 D=p-d-2,\qquad r=D-n+1=p-d-n-1\ge0.
$$
For a clock set $E$ let $P_E=\prod_{x\in E}(X-x)$. At $a\in L$, the
normalized visible selector is
$\ell_a=P_{L\setminus\{a\}}/P_{L\setminus\{a\}}(a)$.
Equation (1) gives $D_a(F)=\sum_h\rho_F(h)\ell_a(h)$ whenever
$\deg F\le d$. Call the charge at $a$ **zero for $F$** if this exact
scalar is zero: the degree-$n-1$ selector already gives
$N_F(a)=B(a)I_{a,1}F$, with no extra hidden-clock degree.

**Simultaneous test.** Given any $S\subseteq L$, with $s=|S|$, the
charge is zero at every $a\in S$ for a fixed $F$ of degree at most $d$
if and only if
$$
 \sum_{h\in H}\rho_F(h)P_{L\setminus S}(h) h^k=0,
 \qquad 0\le k<r+s. \tag{2}
$$
If $S$ is empty, these $r$ equations are automatic from actual order.
To see necessity in general, use $Q=P_{L\setminus S}X^k$ in (1); its
degree is at most $(n-s)+(r+s-1)=D$, and each right-hand term vanishes.
For sufficiency, each $\ell_a$ with $a\in S$ is divisible by
$P_{L\setminus S}$ with quotient of degree $s-1\le r+s-1$. Apply (2)
by linearity and then (1). With $r=s=0$ the condition is empty.
The same equivalence holds simultaneously for all profiles of degree
at most $d$ by taking exactly $F=X^j$, $0\le j\le d$, in (2).
This is a finite matrix test: multiply $M_{U,H}$ on the left by
$(u^j)_{0\le j\le d,u\in U}$, and on the right by
$(P_{L\setminus S}(h)h^k)_{h\in H,0\le k<r+s}$, and test the zero matrix.
For $S=L$ the tilt is $1$ and the test uses all paid source degrees
$0$ through $D$, not just the $n$ original visible selectors.

**Support and sign.** Assume the charge is zero at the specified $S$
(for $S=\varnothing$ no extra premise is needed). If $\rho_F$ is supported
on at most $r+s$ hidden clocks, then it is identically zero. Indeed the
first that many monomial tests form a Vandermonde matrix on its support,
and the tilt has no root on $H$. More generally a nonzero tilted
residual in (2) must have at least $r+s$ sign changes on its sorted
nonzero support. If it had fewer, a polynomial with one root strictly
between every sign change and the appropriate overall sign would
make every tested nonzero product strictly positive, contrary to (2).
These statements constrain the **coalesced residual**, not the number
of stages or raw edges. They hold profile by profile. For example if
$d\ge |U|-1$ and the $S$ condition is known uniformly, one may take
receiver Lagrange profiles: if each hidden part of a receiver row has
at most $r+s$ nonzero entries (or fewer than $r+s$ tilted sign changes
when it is nonzero), then *all* hidden weighted columns vanish. A
bound on the total union of these row supports is not needed. Thus
under the stated receiver degree and rowwise support hypotheses,
structural absence of hidden columns is equivalent to zero charge
on $S$ for every profile of degree at most $d$.

**No hidden correction within an already paid selector guard.** For a
single stop $a$, every normalized polynomial having the same required
visible zeros is $\ell_a R$ with $R(a)=1$. To ask for zero leakage for
all receiver degrees at most $d$, define the finite vectors
$$
 v_j=\left(\sum_h \rho_{X^k}(h)\ell_a(h)(h-a)^j\right)_{0\le k\le d}.
$$
A multiplier of degree at most $e$ exists exactly when
$v_0\in\operatorname{span}(v_1,\ldots,v_e)$: write
$R=1+\sum_{j=1}^e\alpha_j(X-a)^j$ and solve $v_0+\sum_j\alpha_jv_j=0$.
This gives the minimum extra degree on any concrete finite data. It is
at most the number of effective hidden clock sites across the tested
profiles, by a normalized product of their root factors. For actual
order, (1) forces $v_1=\cdots=v_r=0$, since these test polynomials
vanish at every visible site and are paid. Therefore a *paid* multiplier
($e\le r$) can remove the leakage if and only if $v_0=0$, in which case
$R=1$ already works. This does not forbid a different selector with
fewer required visible zeros when their defects have been verified
zero; that information is exactly accounted for by $S$ in (2).

## 3. Physical consequences, with their hypotheses

If the grouped suffix column at a live clock $a$ has no entries at
receiver clocks other than $a$, take $F=X-a$. Its full source is zero,
including the diagonal. If $n+2\le p$ and the affine profile has zero
selector charge at $a$, then (1) gives $B(a)(1-a)^2/2=0$, hence $a=1$.
A prefix row supported on its own clock gives $-B(a)a^2/2=0$ and hence
$a=0$ under the prefix version. The support can come directly from
chronology: for the suffix, all stages at $a$ may lie strictly after
all individually weighted stages at other clocks; for the prefix, all
weighted stages at $a$ may lie before all stages at other clocks.
A lower triangle supplies the off-clock zero in either case. Same-clock
strict contributions require no special treatment because $F(a)=0$.
There is no need to divide by a diagonal or assume it is nonzero.

If both hidden slices vanish, so $M$ is supported on $L\times L$, and
$p\ge2n$, selecting two visible clocks with $\ell_u,\ell_x$ pays exactly
$2n$. The two mixed identities give
$$
 M_{u,x}=B(u)I_{0,u}\ell_x=B(x)I_{x,1}\ell_u.
$$
Thus the normalized quotient $M_{u,x}/B(u)$ is exactly the clock
collocation row. This is a statement about the linear weighted clock
matrix, not a full rooted-tree order assertion on an arbitrary quotient.
A causal physical tableau need not yield a lower triangle after clock
coalescence because repeated clock groups may interleave.

## 4. Sharpness on actual ERK and positive-common-diagonal SDIRK

The bound in (2) is sharp even for actual tableaux, not merely for a
signed Vandermonde vector. For every $n\ge1$, take $p=2n$, any
$0\le d<n$, and any subset $S$ of the $n$ visible nodes below. There is
an actual exact-order-$p$ strict ERK tableau, and one with any fixed
positive common diagonal over the real algebraic field, for which:

- the charge is zero on $S$ for all receiver degrees at most $d$;
- for $F=X^d$ it is nonzero at each visible clock outside $S$;
- the hidden residual of $F=X^d$ has exactly $r+s+1$ nonzero sites,
  with exactly $r+s$ sign changes after the tilt in (2).

### A seed with no hidden weighted rows or columns

Use the $n$ Gaussian clocks on $[0,1]$, with weights $B(u)>0$.
For existence, rational interval moments give a monic rational
orthogonal polynomial $\pi_n$ by positive definiteness of the Gram
matrix over the reals. Multiplying by the product of its interior
sign-changing roots would give a nonzero fixed-sign integrand unless
there were $n$ such roots. Thus they are distinct, interior and real
algebraic. Integration of the Lagrange basis is exact through degree
$2n-1$ by division by $\pi_n$. In particular on each squared basis
function it proves $B(u)>0$. The rule fails degree $2n$, as seen on
$\pi_n^2$, hence fails the degree-$2n$ monomial as well.

For clarity, the full tree order of the collocation seed can be
verified directly instead of assuming it from these quadrature moments.
Let $G_{u,x}=I_{0,u}\ell_x$. Write $|T|$, $T!$ and $\operatorname{ff}(T)$
for the reviewed order, factorial and forest factorial, and
$f_T(X)=X^{|T|-1}/\operatorname{ff}(T)$ for the pure stage profile.
The reviewed stage recursion multiplies the child actions, and
$I_{0,X}f_T=X^{|T|}/T!$. By interpolation and induction, the collocation
stage response $\Phi_G(T)_u$ equals $f_T(u)$ when $|T|\le n+1$.
For any polynomial $P$ with $\deg P+n+1\le p$ and any input vector $v$,
$$
 \sum_u B(u)P(u)(Gv)_u=\sum_x B(x)v_x I_{x,1}P. \tag{3}
$$
This follows by integrating $P(X)I_{0,X}\ell_x$ and
$\ell_x(X)I_{X,1}P$ using their equal integrals and the Gaussian rule;
both degrees are at most $\deg P+n$.

Now induct on $|T|$ to prove the tested identity
$\sum_u B(u)F(u)\Phi_G(T)_u=\sum_u B(u)F(u) f_T(u)$ whenever
$\deg F+|T|\le p$. If all children have order at most $n$, their actions
are pure and equality holds in each row. Otherwise there is a unique
child $\tau$ of size $j\ge n+1$, since $|T|\le2n$. The other child
actions give $u^m$ times their fixed reciprocal factorials, where
$m=|T|-1-j$. Apply (3) with $P=FX^m$; its guard holds since
$\deg P\le p-j-1$. The new test of $\tau$ is $I_{X,1}P$, of degree
at most $\deg P+1$, so the induction hypothesis still pays:
$\deg(I_{X,1}P)+j\le\deg F+|T|\le p$. Replace that response by $f_\tau$;
quadrature and the primitive product rule change its weighted test
back to $P(X)I_{0,X}f_\tau$. Both integrands have degree at most
$\deg P+j\le p-1$. Including the small-child factorials yields the
claimed pure profile. Taking $F=1$ proves all actual tree conditions
through $p$, with the reviewed normalization $T!$.

Convert this seed to a lower-triangular tableau by causal repeated
banks, not by asserting that a dense collocation matrix is triangular.
Fix the common diagonal $\gamma\ge0$. Bank $0$ has diagonal $\gamma I$
and no strict entries. Each bank $k\ge1$ has diagonal $\gamma I$ and
strict inputs $G-\gamma I$ only from bank $k-1$. The clocks in every
bank $k\ge1$ are the original Gaussian clocks; bank $0$ has clocks
$\gamma$. A simultaneous induction on tree order shows that bank $k$
agrees with the dense seed on every tree of order at most $k+1$:
for a child in such a tree, both the current and preceding banks
already agree at its smaller order, so the two contributions add to
$G\Phi_G(\text{child})$. Put output weights $B$ only in bank $p$.
This pays order $p$, and the next pure bush fails by the unchanged
Gaussian rule. The only direct inputs of weighted rows are in banks
$p$ and $p-1$, both at visible clocks. Thus the weighted matrix is
supported on $L\times L$ even if the tableau has other internal clocks;
its visible entries are exactly $B(u)[\gamma I+(G-\gamma I)]_{u,x}$,
so the clock quotient really is the original collocation matrix.
The copies may repeat and interleave clocks; they are only a proof
construction, not a stage claim.

### Two independent interpolation vectors for the perturbation

Put $\nu=p-d$ and select a set $H_*$ of $r+s+1$ new distinct hidden
clocks, disjoint from $L$ and, if necessary, from $\gamma$. Let
$Z=(L\setminus S)\cup H_*$, so $|Z|=\nu$. Take the barycentric weights
$$
 w_x=1/\prod_{y\in Z\setminus\{x\}}(x-y),\quad x\in Z.
$$
They annihilate polynomials through degree $\nu-2$. Independently choose
$d+1$ distinct **receiver** clocks from $L$. On them use their barycentric
weights $\beta_u$ and extend by zero to $L$. Thus $\sum_u\beta_u P(u)$
extracts the degree-$d$ coefficient of polynomials of degree at most
$d$, and $\alpha_u=\beta_u/B(u)$ is well defined. Both identities are
simply the leading-coefficient formula for Lagrange interpolation.

Prepend zero-output donor rows at every clock in $Z$ whose actual
stage responses are pure through order $p-1$, using the
[reviewed-tree donor induction](../quadrature-donor-realization/realization.md#1-the-donor-step-on-the-actual-tree-columns)
with the same diagonal $\gamma$. Such rows at finitely many prescribed
clocks use the already constructed pure bank of $p-2$ distinct nodes;
for $p=2$ only leaf purity is needed and a preceding row sets each
chosen clock. Do not change any old edge. Add an edge of coefficient
$\lambda\alpha_u w_x$ from the donor at $x$ to the final weighted row
of clock $u$, with fixed $\lambda\ne0$. All new edges are strictly
causal, all diagonals are preserved (strict ERK if $\gamma=0$, strict
SDIRK if $\gamma>0$), and the actual clocks stay fixed
since $\sum_x w_x=0$ ($\nu\ge2$). The earlier banks and donor stages
receive no input from the perturbed last bank.

Here the full tree conditions do **not** follow from pure quadrature
alone. We verify the actual graded output cancellation. Let
$\Delta\Phi(T)_u$ be the variation at a weighted row. For $|T|\le\nu$
it is zero. For $\nu<|T|\le p$, it has the form
$$
 \Delta\Phi(T)_u=\lambda\alpha_u R_T(u),\qquad
 \deg R_T\le |T|-\nu-1. \tag{4}
$$
For each child $\tau$, subtract its two actual last-row actions:
$$
 \Delta(A\Phi(\tau))_u
 =\gamma\Delta\Phi(\tau)_u+\lambda\alpha_u\kappa_\tau,\qquad
 \kappa_\tau=\sum_x w_x x^{|\tau|-1}/\operatorname{ff}(\tau).
$$
The unchanged preceding bank cancels. The diagonal multiplies the
change at the **same row for the smaller tree** $\tau$, so induction
on tree order applies without any inversion. The direct term vanishes
for $|\tau|<\nu$. At most one child can have size $j\ge\nu$ in a paid
tree, as two would force $|T|\ge1+2\nu>p$. If there is no such child,
all actions are unchanged. Otherwise the other children have total
order $m=|T|-1-j\le d-1<n$, so their unchanged actions are pure. In the
child product the difference is therefore exactly the one varying
action times those unchanged factors. In (4) we may take
$R_T=C X^m(\kappa_\tau+\gamma R_\tau)$, setting $R_\tau=0$ for
$|\tau|\le\nu$, with $C$ the product of the other reciprocal tree
factorials. Its degree is at most $m+\max(0,j-\nu-1)\le |T|-\nu-1$.
This proves (4), also for $\gamma=0$. For $d=0$ no paid tree has an
affected child.

Every changed paid tree therefore has weighted output variation
$\lambda\sum_u\beta_uR_T(u)=0$, since $\deg R_T\le p-\nu-1=d-1$.
The actual `HasOrder p A b` is preserved, not just the mixed or pure
conditions. The exact order is still $p$ because the weight and clock
vectors, hence the failing next bush, are unchanged.

### Reading the sharp hidden law

Only the indicated direct edges of weighted rows varied, so for any
profile the change of the grouped column at $x\in Z$ is
$$
 \Delta N_F(x)=\lambda w_x\sum_u\beta_uF(u),
$$
and it is zero elsewhere. The seed had no hidden weighted columns and
zero charge at every visible site for all paid profiles. Thus for
$F=X^d$ the hidden residual is exactly $\lambda w_x$ on $H_*$, and the
visible defect is $-\lambda w_a$ on $L\setminus S$, zero on $S$. In fact the grouped column at a clock
in $S$ has no variation for any profile, since its source clock is
not in $Z$. All profiles of degree below $d$ have no variation anywhere. Multiplying the
hidden residual by $P_{L\setminus S}(x)$ leaves
$\lambda/\prod_{y\in H_*\setminus\{x\}}(x-y)$, which alternates sign.
This verifies the three sharpness claims, including their actual tree
and chronology hypotheses. Taking $S=L$ gives a nonzero rank-one
hidden column block that is invisible to **every** paid profile of
degree at most $d$ at all visible stops. Thus neither zero charge in
that range nor low matrix rank alone implies structural zero columns.
The result concerns only mixed source charges; it never erases an
atom of an independently specified signed law.

## Exact arithmetic replay

The [standalone checker](check-hidden-clock-moment-ladder.py) verifies
18 variants over $\mathbb Q(\sqrt{15})$, including all 37 paid rooted
shapes and a genuinely nonzero same-row diagonal child change. It
also checks the next bush failure and the exact hidden support and
sign pattern. Run `python3 -B check-hidden-clock-moment-ladder.py` and
compare with the [receipt](hidden-clock-moment-ladder.receipt). This
regression checks the construction in one setting; the all-order
statement is proved above, not inferred from the sample.
