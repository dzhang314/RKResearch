# Moving terminal clocks: an ordinary nullity certificate and a core-feed test

## Scope

Source-only: no compiler, solver, numerical gate, replay, repository change, or held work. This extends dirk_ordinary_prefix_observer_certificate_20261126.md without assuming that the actual last clock is \(1\), that its diagonal is zero, or that a terminal column is already represented as an ordinary pure direction. All polynomial moment assertions are for actual order conditions and genuine profile lifts. No stage floor changes.

Let \(s\) be the last physical row of a lower triangular tableau, put \(t=c_s\), and let \(e_s\) be its indicator. Work over a field with the needed small integers invertible; a nonexistence result over the corresponding residue fields transfers to nonzero commutative rings by the cleared tall tree. Let \(J\) denote formal integration from zero. A genuine lift \((\Theta,f)\) at grade \(j\) is a rooted combination giving the numerical column \(\Theta\) and scalar profile \(f\). The true primitive operation gives \((A\Theta,Jf)\) at the next grade. Multiplication by \(C=\operatorname{diag}(c)\) corresponds to multiplying the profile by \(x\). Let \(U\) be a numerically \(C\)-invariant subspace with \(\mathbf b\cdot U=0\). It may be genuinely pure at a high grade; the hypotheses below state whenever that grade matters. Invariance gives \(\mathbf b\cdot H(C)U=0\) for every polynomial \(H\).

## 1. Keep the moving terminal evaluation instead of masking it

Suppose a genuine lift is zero after terminal deletion modulo \(U\). On the actual tableau write
\[
 \Theta=u+\xi e_s,\qquad u\in U,\qquad r_0=\xi b_s,\qquad m=p-1-j.
\]
The genuine scalar pairing gives exactly
\[
 \int_0^1 f(x)H(x)\,dx=r_0H(t)\qquad(\deg H\le m).
\]
This is stronger than starting with the test \(H(t)=0\): retain the possible terminal coefficient as one measured evaluation line. If a chosen decomposition is not unique, \(r_0\) still equals \(\int_0^1 f\).

For a common profile factor \(B\) and a family \(f=B F\), \(F\in\mathbb P_{L-1}\), define the exact ordinary moment matrix and evaluation vector by
\[
 M_{ab}=\int_0^1 x^{a+b}B(x)\,dx
   \quad(0\le a\le m,\ 0\le b<L),\qquad
 v_t=(1,t,\ldots,t^m)^\top .
\]
The actual terminal-deleted nullity is at most \(L+1-\operatorname{rank}[M\,|\,v_t]\), by the dimension of the inverse image of the one-dimensional evaluation line. If \(b_s=0\), use \(L-\operatorname{rank}M\). These are necessary scalar certificates, not assertions that every scalar null has a physical lift. Writing \(B=x^e B_0\), \(\deg B_0=\ell\), fixed paid \(x^e\)-Hankel gives
\[
 \operatorname{rank}M\ \ge\ \min\{L,\max(0,m-\ell+1)\}.
\]
For the rank proof restrict to \(B_0F\) of degree at most \(d=\min(m,\ell+L-1)\) and use the size-\((d+1)\) fixed Gram matrix. Its cutoff \(e+2d+1\) is paid because \(j\ge e+d\) and \(p\ge j+m+1\). No positivity of squares of unknown polynomials is used.

### Fixed anchors give an endpoint-free weighted reproducer

More precisely suppose all the profiles have a **known common Beta factor** \(W=x^e(1-x)^f\) and the quotient degree is at most \(n\), so \(\Theta\) has scalar profile \(W h\), \(\deg h\le n\). Use the moment equation against all \(H\) rather than introducing the moving weight \(x-t\). If \(m\ge n\), paid \(W\)-Gram determines \(h\) as \(r_0\) times the degree-\(n\) reproducing kernel at \(t\); if \(r_0=0\) then \(h=0\). For example, with the monic \(W\)-orthogonal polynomials \(P_k\) of norms \(d_k\), that kernel is \(\sum_{k=0}^n P_k(x)P_k(t)/d_k\).

If \(m\ge n+1\), testing \(P_{n+1}\) makes \(P_{n+1}(t)=0\). The reproducer is then a nonzero scalar multiple of \(P_{n+1}(x)/(x-t)\), by the paid Christoffel–Darboux identity. If \(m\ge n+2\), the [paid degree-\((n+2)\) test](PAID-BETA-TEST.md) rules out \(t\) using only the adjacent polynomials through \(P_{n+1}\). A fully orthogonal \(P_{n+2}\) need not be available at the tight paid cutoff. The argument is for the fixed Beta weight; a different factor requires its own Gram certificate.

In particular, at \(p=2q,j=q-1\) one known anchor factor already gives zero deletion nullity independent of the terminal clock. At \(p=2q+1,j=q\) any two known anchor factors, counting multiplicity (\(x^2\), \(x(1-x)\), or \((1-x)^2\)), suffice. A smaller true profile cap also gives extra tests. This does not need even the lower triangularity of \(A\).

### Odd midpoint with one origin factor: exact residual line

At \(p=2q+1,j=q\), with \(\deg f\le q\), the ordinary unweighted reproducer forces
\[
 f(x)=r_0 K_q(x,t),\qquad K_q(x,t)=\sum_{k=0}^q(2k+1)L_k(x)L_k(t),
\]
where \(L_k\) is shifted Legendre normalized to one at 1. For a simple origin factor \(f(0)=0\) and \(f\ne0\), this requires \(K_q(0,t)=0\). Since \(K_q(0,0)=(q+1)^2\ne0\), \(t\ne0\). Christoffel–Darboux at the origin gives \(L_{q+1}(t)=-L_q(t)\), and consecutive coprimality gives \(L_q(t)\ne0\). Thus \(t\) is a genuine nonzero root of the fixed left-Radau polynomial \((L_{q+1}+L_q)/x\), and
\[
 K_q(x,t)=\frac{q+1}{2} L_q(t)\frac{L_{q+1}(x)+L_q(x)}{x-t}.
\]
It follows that the common profile factor \(B\) must divide this explicit quotient. The fixed left-Radau roots are simple in paid fields (by the reflected right-Radau Legendre lowering identity); the origin root of \(L_{q+1}+L_q\) is simple by its endpoint derivative, and \(x=1\) is not a root. In particular one can reject a repeated common factor, a second actual endpoint factor, or any factor incompatible with the quotient without testing core transport. If \(t=1\), \(K_q(0,1)=(-1)^q(q+1)\) is paid and nonzero. The moving-clock problem left here is a possible real terminal evaluation at a fixed left-Radau site, not a full scalar rank collapse.

## 2. Lower triangularity gives an intrinsic terminal core-feed obstruction

The lower triangular last column is always \(A e_s=a_{ss}e_s\), without imposing \(a_{ss}=0\). Use any polynomials \(P,H\) and integer \(k\ge1\) such that
\[
 \deg P+\deg H+k\le p-1-j.
\]
Apply \(A^k\) to the genuine lift \(P(C)\Theta\) and take the genuine \(H\) moment. Polynomial Fubini, or repeated formal integration by parts, yields
\[
 \mathbf b\cdot H(C)A^kP(C)u
 =
 r_0 P(t)\left[
 \frac{1}{(k-1)!}\int_t^1(x-t)^{k-1}H(x)\,dx-a_{ss}^kH(t)
 \right].
\]
Indeed the left side before subtracting the terminal column is \(\int_0^1 H J^k(P f)\). Its adjoint polynomial in the original \(f\) has degree at most \(\deg P+\deg H+k\), so the actual initial terminal-evaluation identity applies at \(t\). No order assumption is assigned to a deleted array.

The first useful case is \(k=1\), \(H=x-t\), if \(j\le p-3\):
\[
 \mathbf b\cdot (C-tI)A P(C)u
   =\tfrac12 r_0(1-t)^2 P(t)
       \qquad(\deg P\le p-j-3).
\]
If \(r_0\ne0\) and the actual core feed \(\mathbf b\cdot (C-tI)A U\) vanishes, this forces \(t=1\). This holds in particular when \(U\subset F_{p-3}\), since \(A\) and \(CA\) then land in genuine grades through \(p-1\), even if \(U\) is not cheap enough for the earlier comparison cuts. The measured condition is weaker: only the one adaptive \(C-tI\) feed is needed. If wanted, the additional measured vanishing of \(\mathbf b\cdot AU\) and the test \(H=1\) give \(a_{ss}=1-t=0\) as well. For an origin-anchored odd-midpoint profile, forcing \(t=1\) suffices to rule out the nonzero null; no extra terminal purity is assumed.

There is a localization form not requiring the core to have any particular ordinary grade. Decompose \(u=\sum_\nu u_\nu\) in its actual clock-local components, and put \(r_\nu=\mathbf b\cdot(C-tI)A u_\nu\). Then the moments of \(r_\nu\) through \(p-j-3\) equal those of the single point mass \(\frac12 r_0(1-t)^2\) at \(t\). If \(r_0(1-t)\ne0\) and \(t\) is not among the nonzero \(r_\nu\) clocks, there must be at least \(p-j-2\) distinct such clocks: otherwise the monic product of their labels is a permitted \(P\) and gives contradiction. Alternatively it suffices that \(u\) has at most \(p-j-3\) distinct support clocks and none is \(t\). If the total support size is within that same paid interpolation window and \(t\) is present, then all non-\(t\) feed masses are zero by Vandermonde, and the complete obstruction is localized to the genuine core clock \(t\). At odd midpoint the support cutoff in the first criterion is \(q-2\). This is a physical-clock collision, not a reason to assign extra copies of a root.

### Output ranks for a surviving moving null

If \(t\ne1\), \(r_0P(t)\ne0\), and \(H=(x-t)K\), the scaled variable \(y=(x-t)/(1-t)\) turns the right side into a nonzero multiple of the ordinary \(y^k\) moment of \(K\). If \(M_k=p-j-2-k-\deg P\ge0\), the Hankel test against products of degree up to \(2\lfloor M_k/2\rfloor\) forces at least \(\lfloor M_k/2\rfloor+1\) actual \(b\)-visible clock values in the output of \(A^kP(C)u\), other than \(t\). Indeed the fixed \(y^k\) Gram is nonsingular at this cutoff and the numerical matrix factors through these weighted clock aggregates. All rows involved are at or after the first actual support of \(P(C)u\) by lower triangularity. If that first row has clock \(t\), the factor \(x-t\) makes the needed nonzero outputs strictly later than it. Multiple physical rows at one clock give one aggregate. This affine change of variable is formal, not a claim that the original clocks lie inside \([t,1]\).

For \(1\le k\le K_0\), test \(K(y)=1,y,\ldots,y^{K_0-1}\) if \(2K_0+\deg P\le p-1-j\). The observed moment rows of these \(K_0\) power iterates have full rank \(K_0\), after multiplying rows by the nonzero factors, from the fixed \(y\)-Hankel pairing. Thus actual nonterminal support or transported rank bounds can rule out a moving null even when its core feed is not identically zero. This is a conditional rank criterion, not a claim that a global surplus of one stage bounds those ranks.

## 3. Concrete diagnostics showing the needed hypothesis

**A real two-row order-three DIRK with no core.** Use \(A_{21}=A_{22}=1/3\), all other entries zero, and \(\mathbf b=(1/4,3/4)\). Then \(c=(0,2/3)\), and \(\mathbf b\cdot\mathbf1=1\), \(\mathbf b\cdot c=1/2\), \(\mathbf b\cdot c^{\odot2}=1/3\), \(\mathbf b\cdot Ac=1/6\), exactly the four rooted equations through three. The true grade-one profile \(x\) is numerical only at the last row and has an actual one-dimensional deletion nullity. Its terminal clock \(2/3\) is precisely the left-Radau residual for \(q=1\). The required \(x-t\) primitive feed test is not paid at this order.

**A real order-five explicit tableau with a genuine high pure core at the terminal clock.** This is a diagnostic counterexample to a rank inference, not a new small-stage construction claim. Let
\[
 a=(6-\sqrt6)/10,\qquad t=(6+\sqrt6)/10
\]
and use the three-node collocation matrix \(A^*_{ij}=\int_0^{c_i}\ell_j(x)\,dx\) on \(c^*=(0,a,t)\), with \(\ell_j\) the cardinal polynomials and output \(b_j^*=\int_0^1\ell_j\). The nodal polynomial is \(x(x^2-\tfrac65 x+\tfrac3{10})\), orthogonal to \(1,x\). Thus the scalar quadrature is exact through degree four. Actual collocation stage integration is exact on scalar polynomials through degree two, and \((\mathbf b^*)^\top A^*=(\mathbf b^*)^\top(1-C^*)\) by integrating the cardinal primitives and applying this quadrature. These prove all rooted conditions through five without a numeric existence claim: any root with children of size at most three has exact scalar stage profile; a child of size four can occur through order five only as the unique child, is already exact as a stage profile by the former rule, and its extension is integrated by the displayed \(b A\) identity.

Take four literal fixed-node substitutions, starting with the actual shared stage of clock zero and stage value \(\mathbf y_0\). At the first sweep on nodes \(a,t\), evaluate \(\mathbf y_0+h c_i^*\mathbf f(\mathbf y_0)\); at each further sweep apply the same collocation row to derivative values from the preceding sweep and the shared zero stage. Arrange both stages in each sweep before the next, with the fourth \(t\) stage last. Use only the shared zero stage and the fourth sweep for the output with \(\mathbf b^*\). This is an explicit lower triangular array with true row-sum clocks \(a,t\) at each sweep: first sweep uses \(c_i^*\), later ones have collocation row sum \(c_i^*\). The stage elementary weight of a tree is exact relative to \(A^*\) once the sweep index reaches its height in edges, by induction on its children; every tree through order five has height at most four. Therefore this actual array has order five. No high-order construction search is used here.

Call the four physical \(t\)-rows \(t_1,\ldots,t_4\), so the terminal is \(s=t_4\). The low true grade-two profile \(f=x(x-a)\) has numerical column \(c^{\odot2}-a c=t(t-a)\sum_{\ell=1}^4 e_{t_\ell}\). Let \(U\) be the span of \(e_{t_1}+e_{t_2}+e_{t_3}\). It is genuinely pure in \(F_5\), \(C\)-invariant at clock \(t\), and its numerical output weights are all zero. For purity, take \(\delta_2=A^2\mathbf1-c^{\odot2}/2\) and \(\delta_3=A^3\mathbf1-c^{\odot3}/6\). On the copies of clock \(t\), \((C-aI)\delta_3\) is a nonzero constant times the indicator of the first two sweeps; it vanishes off those copies since it kills the \(a\) copies and the true zero stage. The true pure \((C-aI)A^2\delta_2\) is supported only at \(t_3\) and is nonzero there. Indeed \(\delta_2\) is \(-c_i^2/2\) at the first sweep and zero thereafter; those two further collocation applications have value \(-\tfrac16\int_0^t\operatorname{Interp}(x^3)\), with
\[
 \operatorname{Interp}(x^3)=\tfrac65x^2-\tfrac3{10}x,\qquad
 \tfrac16\int_0^t\operatorname{Interp}(x^3)=t^2(8t-3)/120\ne0.
\]
The interpolation formula uses the actual nodal polynomial. This proves the pure assertion by genuine grade-four and grade-five witnesses.

The terminal output weight is nonzero: \(b_t^*=(1/3-a/2)/(t(t-a))\ne0\). Thus the actual anchored profile \(f\) gives a nonzero terminal-deleted null, even at order five with a true \(b\)-null \(C\)-invariant core. Its \(F_5\) core is not within the cheap \(F_{p-3}\) hypothesis. Its core sits at exactly the terminal clock and cannot be removed by the cheap support separation condition. The feed identity indeed forces a nonzero \(b(C-t)AU\). This example does not contradict a theorem about a suitably low pure core, and does not purport to meet any near-minimal rank chart.

## Exact conclusion

Movable \(c_s\) costs only the evaluation line in the ordinary rank calculation. Enough genuine fixed anchor degree removes it by two consecutive paid orthogonal tests. In the important one-origin odd-midpoint case, a nonzero null has one precise left-Radau profile, and a single actually paid \(b(C-t)AU\) test, or the stated core-support/rank criteria, excludes it without knowing endpoint purity first. An unmeasured high core and a literal terminal-clock collision cannot be declared harmless; the two explicit tableaux demonstrate separate failure modes. Nothing above counts an unobserved stage or modifies any existing endpoint hold.

### Combined endpoint-free cutoff and the already used anchored band

If actual core invisibility or localization has forced \(t=1\) for every nonzero moment-active null, only **one** extra weighted orthogonal test beyond the reproducer is needed, not two. Under the fixed Beta factor \(W=x^e(1-x)^f\), a quotient degree bound \(n\) and \(m\ge n+1\) would require \(P_{n+1}^{(W)}(1)=0\). This endpoint value is paid and nonzero: in the usual monic normalization it is \(\binom{n+1+f}{n+1}/\binom{2n+2+e+f}{n+1}\), with integer factors bounded by the already required \(p\). Thus the combined condition recovers the previously prescribed-terminal count without a prescribed final clock.

For example an actual ordinary \(U\subset F_6\), \(j=7\), \(p=15\), and genuine origin-vanishing profiles have zero terminal-deleted nullity without using any asserted terminal purity or marked D conditions: the adaptive \(A\)-feed vanishes through order, and the one origin factor supplies the one extra weighted orthogonal test. This only replaces the separation step for such already provided mask data; it does not derive the rest of a saturated or nonminimal chart. By contrast at even \(p=2q,j=q\) a lone origin factor may give \(m=n\) only. A nonzero \(t=1\) terminal reproducer is then not excluded by this argument, consistent with the actual Lobatto cardinal at this grade.
