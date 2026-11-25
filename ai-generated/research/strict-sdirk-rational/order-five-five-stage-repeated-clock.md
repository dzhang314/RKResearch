# Five rational strict SDIRK stages attain exact order five

The known five-stage lower bound is attained over \(\mathbb Q\),
both for order at least five and for exact order five. This improves
the rational upper bound of six. The construction uses one genuine
repeated clock, in the third and fourth rows, with two different
stage vectors there. It comes from an exact rational parameterization,
not a search or numerical fit.

## Literal tableau

The common diagonal is \(1\). The entries above the lower triangle
are zero.

| Row | Entries |
|---:|---|
| 1 | \(1\) |
| 2 | \(-6/11,\,1\) |
| 3 | \(14907/2900,\,-13167/2900,\,1\) |
| 4 | \(-15818893/310500,\,190522673/6520500,\,7279319/326025,\,1\) |
| 5 | \(173/92,\,-6655/2484,\,-28271375/155877831,\,-5000/251011,\,1\) |

The weights and clocks are
\[
\begin{aligned}
\mathbf b&\coloneqq
 (47/216,\ 14641/22680,\ -4940875/569292948,\ 14375/8032352,\ 23/160),\\
\mathbf c&\coloneqq(1,\ 5/11,\ 8/5,\ 8/5,\ 0).
\end{aligned}
\]
The two vectors of first quadratic defects are not independently
fitted; they satisfy the exact shared-line identity from the
[tableau normal form](order-five-five-stage-normal-form.md):
\[
\mathbf q\coloneqq
 (1/2,\,-47/242,\,197/58,\,-5593/3450,\,47/138),
\qquad \overline{\mathbf q}=(69/47)\mathbf q.
\]
The [exact checker](check-five-stage-repeated-clock.py) derives the
rows and then independently evaluates the literal displayed tableau
on all rooted trees. It checks all 17 tree conditions through order
five; all 20 order-six conditions fail. The tall weight at order six
is \(-5/24\), not \(1/720\). The method has one negative weight and
indeed \(-15\prod_i b_i=(474153625/218608492032)^2\), as required
by the [five-row determinant condition](order-five-five-stage-necessary.md).
No stability claim is made.

## Derivation of the repeated-clock family

Use centered coordinates \(t=2x-1\) and write the five physical clocks
in that variable as \((a,u,v,v,-a)\). In particular
\(\gamma\coloneqq(1+a)/2=c_1=1-c_5\).
Assume the four sites are distinct and that the displayed divisions
are defined. Let \(\mu\) be uniform probability integration on
\([-1,1]\) and let the monic four-site polynomial be
\[
P(t)\coloneqq(t^2-a^2)(t-u)(t-v).
\]
The four-site degree-four rule must satisfy \(\mu(P)=0\), or
\[
uv=\frac{5a^2-3}{5(1-3a^2)}.
\]
Conversely this relation makes the degree-three Lagrange weights
exact at degree four as well, by subtracting a multiple of \(P\).
For \(z\in\{a,u,v,-a\}\) define
\[
H_z\coloneqq\mu(P(t)/(t-z)),\qquad
\omega_z\coloneqq H_z/P'(z).
\]
These are the aggregate quadrature weights \(\omega_z\). The deleted
cubic means are explicit:
\[
H_a=(a-u-v)/3+a u v,\quad
H_{-a}=(-a-u-v)/3-a u v,\quad
H_u=v(a^2-1/3),\quad H_v=u(a^2-1/3).
\]

For the forward defect, aggregate the products \(b_i q_i\) at each
of the four clocks. The products are orthogonal to all polynomials
through degree two exactly when they are proportional to the
four-site barycentric vector \((1/P'(z))_z\). Indeed, the cubic
coefficient in the Lagrange interpolant of a quadratic is zero: \(\sum_z z^k/P'(z)=0\) for \(k=0,1,2\).
The moment map on four distinct sites has a one-dimensional kernel.
Thus for some \(\alpha\) the singleton defect value at \(z\) is
\(\alpha/H_z\), and at the duplicate it is the weighted mean of
the two defects that equals \(\alpha/H_v\).

### Pay the two initial rows

Here the first two physical sites are singletons. Their defects are
forced by triangularity and the common diagonal:
\[
q_1=\gamma^2/2,\qquad
q_2=2\gamma\,\frac{1+u}{2}-\gamma^2-\frac{(1+u)^2}{8}.
\]
They require \(q_2H_u=q_1H_a=\alpha\).
For transparency, put \(R\coloneqq1-3a^2\), \(D\coloneqq5a^2-3\);
after using \(uv=D/(5R)\) and clearing denominators this equation is
\[
 (1+2u+4au-2a^2-u^2)DR-(1+a)^2(4au+5Ru^2+D)=0.
\]
Its exact factorization is
\[
2(u-a)\left[
 (3a^2-1)(5a^2+5a+1)u-(5a^2-3)(3a^3-3a-1)
 \right]=0.
\]
The first factor is the prohibited coincident initial pair. The
other gives the rational family
\[
u=\frac{(5a^2-3)(3a^3-3a-1)}
          {(3a^2-1)(5a^2+5a+1)},\qquad
v=-\frac{5a^2+5a+1}{5(3a^3-3a-1)}.
\]

### Split the repeated site to pay isotropy

Use \(\alpha=H_aq_1\), \(q_5=\alpha/H_{-a}\), and
\(\lambda=\gamma^2/(2q_5)\). The reflected second-row condition sets
\[
q_4=\big(2\gamma y_4-\gamma^2-y_4^2/2\big)/\lambda,
\qquad y_4=(1-v)/2.
\]
Let \(\omega\coloneqq\omega_v\),
\(m\coloneqq\alpha/H_v\), and \(\Delta\coloneqq q_4-m\).
Write the two weights at the repeated clock as
\(b_4=s,\ b_3=\omega-s\), and
\(q_3=(\omega m-s q_4)/(\omega-s)\) to preserve the correct
aggregate linear defect. Let
\[
E\coloneqq\sum_{z\in\{a,u,v,-a\}}\omega_z(\alpha/H_z)^2.
\]
The actual five-row squared output is
\[
E+\frac{s\omega}{\omega-s}\Delta^2 .
\]
Therefore the only weight split needed for isotropy is the rational
value
\[
s=-\frac{E\omega}{\,\omega\Delta^2-E\,}.
\]
When \(E,\omega,\Delta,\omega\Delta^2-E\) are nonzero this yields
two nonzero weights and all three required orthogonalities without
any other fitting equation. The four boundary defect values now
hold by construction, so the unique row/column solve from the
normal form supplies the full tableau.

### Exact specialization

Choose \(a=1\). Then \(u=-1/11,\ v=11/5\) and
\[
(\omega_a,\omega_u,\omega_v,\omega_{-a})
  =(47/216,\ 14641/22680,\ -125/18144,\ 23/160).
\]
Here \(\alpha=-47/165,\ E=-47/828,\ m=47/10\), and
\(\Delta=-10904/1725\); the scalar split exists and is
\(s=14375/8032352\). Every required denominator and physical
weight is nonzero. Applying the unique normal-form solve gives the
five rows at the top. In particular stages 3 and 4 at the same
clock cannot be literally merged, since their \(q_i\) values differ.

## Replay and exact minimum

Run `python3 check-five-stage-repeated-clock.py`. Its derivation and
separate literal-tree replay use only the Python standard library.
The accompanying `five-stage-repeated-clock-numerators.json` uses
integer numerators for the reviewed scaled-tree checker. This packet
is a mathematical/source certificate and was not compiled in Lean.

The [already established rational common-diagonal lower
bound](order-five.md) gives at least five stages at order five.
Together with this exact witness it proves that both rational
strict SDIRK minima equal five.

## Lean replay

The exact five-stage witness and both least-stage statements have Lean
proofs using the reviewed HasOrder predicate. The two modules,
RationalStrictSDIRKFiveStageFiveUpper and RationalStrictSDIRKOrderFiveMinimum,
compiled and passed independent kernel replay on Lean 4.36.0; the typed
audits show only standard Lean axioms.
