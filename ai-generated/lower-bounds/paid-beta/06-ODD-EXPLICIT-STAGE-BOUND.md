# An extra stage at every odd explicit order from thirteen onward

**Theorem.** An explicit Runge–Kutta method of order \(p=2d+1\) with \(d\ge6\), and with coefficients in any nonzero commutative unital ring, requires
\[
                              s\ge3d+2 .
\]
This gives lower bounds of 20, 23, 26 and 29 stages at orders 13, 15, 17 and 19. The first three improve the bounds over arbitrary coefficient rings; order 19 was already known to require 29 stages. The proof was independently checked, but has not been formalized in Lean.

The proof is over a field in which \(p!\ne0\). Over a nonzero commutative unital ring, the order condition for the tall tree of size \(p\) makes \(p!\) a unit. Passing to any maximal ideal preserves the equations and the strict tableau shape, and gives such a field. Thus it suffices to work over that field. There is no positivity or ordering assumption.

At equality in the old bound, the reverse order conditions force a basis on the last few stages, one basis vector for each successive first nonzero coordinate. The exact action of the stage matrix on that basis either permits a reweighting onto a prefix that is too short, or forces two distinct stage abscissae to coincide.

## Inputs and exact rank flags

For \(g\ge0\), \(E_g\) is the span of actual Butcher weight vectors through tree size \(g+1\); \(F_g\) is the span of the combinations with zero exact polynomial. For a tree \(t\) the exact polynomial attached to \(\boldsymbol\Phi_t(A)\) is \(|t|X^{|t|-1}/t!\). Extension applies \(A\) to a numerical vector and the primitive from zero to its polynomial. Rooted sum uses the componentwise product on vectors and multiplication on polynomials. Use
\[
 \mathbf c\coloneqq A\mathbf1,\quad C\coloneqq\operatorname{diag}(\mathbf c),
 \quad Y\coloneqq I-C,\quad D\coloneqq CA-AC-A^2=AY-YA-A^2,
\]
and set
\[
 \mathbf h_1\coloneqq\mathbf b A-\mathbf bY,\qquad
 \mathbf h_2\coloneqq2\mathbf bYA-\mathbf bY^2.
\]
All outputs are rows; a row applied to a vector denotes their centered-dot pairing. In particular the genuine commutator obeys \(D E_g\subseteq F_{g+2}\) because \(XJ-JX=J^2\) for the formal primitive \(J\) from zero.

We use the following established results:
1. The ordinary paid stage floor for order \(p=2d+1\) is \(p+d=3d+1\). More generally a strictly lower triangular tableau with any output row exact for \((1-X)^m/m!\) through tree size \(r\ge10\), with \((m+r)!\ne0\), requires at least \(\lceil3r/2\rceil-1\) rows. A weighted output here means the read on all rooted profiles, not an extra condition on the output row. The [weighted stage bound](01-PAID-GRADE-FIVE-SURPLUS.md) proves both statements.
2. The [penultimate-tap theorem](../../research/clock-localized-tail/PENULTIMATE-PAID-TAP.md), [clock-closure theorem](../../research/clock-localized-tail/MAXIMAL-ODD-CLOCK-DELAY.md), and [reverse annihilator descriptions](../../research/clock-localized-tail/REVERSE-CLOCK-CHARTS.md) apply to a tableau at equality in the old stage bound. In an equality-stage tableau \(s=3d+1\), the last \(b\)-coordinate \(b_s\ne0\). Write \(\epsilon=0\) if \(\mathbf h_1=0\), and \(1\) otherwise. For \(\epsilon=0\), \(c_s=1\), \(A\mathbf e_s=Y\mathbf e_s=0\), and \(H_g\coloneqq E_g+K\mathbf e_s\); for \(\epsilon=1\), \(c_s\ne1\) and \(H_g\coloneqq E_g\), where \(K\) is the coefficient field.
3. In that equality case every \(\mathbf v\in H_d\) zero through the physical row \(k\coloneqq2d\) satisfies
\[
                       \mathbf b A^{d-1}\cdot\mathbf v=0.          \tag{1}
\]
All the positive taps \(\mathbf bA^m\), \(1\le m\le d\), cannot vanish on every such late vector of \(E_d\). Otherwise they admit separate rows on the actual first \(k\) stages. The corresponding exact weights \((1-X)^m/m!\) give separation through degree \(d\) by the weight-\(X(1-X)\) Gram and the literal origin coordinate. A linear combination of those weights gives the ordinary integral on degrees \(\le d-1\) by the weight-\((1-X)\) Gram. The actual prefix is then ordinary order \(d\), so its pure rank is at least \(d-1\) through degree \(d-1\) by the unrestricted size-six floor and strict growth. At degree \(d\) growth is still strict because the actual shift-one output reads \(\mathbf c\) nontrivially: an \(A,C\)-invariant pure plateau would put \(\mathbf c\) in that pure space using \(A\mathbf c-\mathbf c^{\odot2}/2\) and strict triangularity. Thus at least \(d+(d+1)=2d+1\) independent vectors would have to fit in the first \(2d\) rows. This is the [prefix argument in the clock-closure theorem](../../research/clock-localized-tail/MAXIMAL-ODD-CLOCK-DELAY.md#short-closure-would-recover-every-needed-early-output).

There are three cases in the exact dual flags. In the first two, a single row \(\boldsymbol\lambda\) spans the terminal reverse line, and
\[
        H_{q-r}^\perp=\boldsymbol\lambda P_{\le r}(C)
                           \qquad (0\le r\le q-d).                \tag{2}
\]
Here \(P_{\le r}(C)\) denotes polynomials in \(C\) of degree at most \(r\), and \(\perp\) denotes the algebraic annihilator, not an inner-product construction. The cases are
\[
\begin{array}{c|c|c|c|c}
 &q&\boldsymbol\lambda& m & H_{q+1}\\ \hline
 \epsilon=1,\ \delta=d   &2d-1&\mathbf h_1&0&K^s\\
 \epsilon=0,\ \delta=d-1 &2d-2&\mathbf h_2&1&K^s .
\end{array}
\]
The delay \(\delta\) is the number of steps until the actual clock span of \(H_d\) stabilizes.

The remaining case is \(\epsilon=1,\delta=d-1\). Now \(q=2d-2\), \(\boldsymbol\lambda_0\coloneqq\mathbf h_1\) is supported at a single clock \(\theta=c_s\ne1\), and \(\lambda_{0,s}=-b_s(1-c_s)\ne0\). There exists a row \(\boldsymbol\lambda\), independent of \(\boldsymbol\lambda_0\), with
\[
 E_{q-r}^\perp=K\boldsymbol\lambda_0+\boldsymbol\lambda P_{\le r}(C)
 \quad(0\le r\le q-d),\qquad
 E_{q+1}=\ker\boldsymbol\lambda_0.
                                                                    \tag{3}
\]
Subtracting a multiple of \(\boldsymbol\lambda_0\) allows us to take \(\lambda_s=0\); since \(\boldsymbol\lambda_0\) is clock-local, this replacement preserves (3).

## Actual clock detection fills the physical tail

For the secondary or sole detector \(\boldsymbol\lambda\), define the actual clock response of a vector \(\mathbf v\) by
\[
             \Gamma_\theta(\mathbf v)
                 \coloneqq\sum_{i:\,c_i=\theta}\lambda_i v_i
\]
at each physical clock \(\theta\). The space simultaneously killing every \(\Gamma_\theta\) is \(C\)-invariant. In case (3) intersect it with \(\ker\boldsymbol\lambda_0\), which is also \(C\)-invariant. By (2) or (3), as appropriate, the resulting space is contained in \(H_d\).

If \(\mathbf v\in E_d\) is late after row \(k\) and belongs to that space, each of its actual clock components belongs to the same space and is still late. Let \(\mathbf u\) be one such component at clock \(\theta\ne1\). The exact adjoint identity and (1) imply
\[
  0=\mathbf b A^{d-1}\cdot\mathbf u
    = (1-\theta)^{d-1}\mathbf b\cdot\mathbf u/(d-1)! .
\]
The identity still applies when \(\mathbf u\in H_d\) only: the added final basis vector is killed by both \(A\) and \(Y\), and the length is positive. Thus this nonendpoint component has zero output. The endpoint component makes no contribution to any positive tap either. Consequently all the positive taps on \(\mathbf v\) vanish. The early-prefix obstruction in input 3 therefore forces some actual late \(\mathbf v\in E_d\) to satisfy \(\Gamma(\mathbf v)\ne0\).

For this vector, (2) or (3) gives \(\sum_\theta \theta^a\Gamma_\theta(\mathbf v)=0\) for \(0\le a\le q-d\). A nonzero such response needs at least \(q-d+2\) distinct clocks. In the first case of (2) this is \(d+1\), exactly the entire physical tail after \(k\). In the second case of (2) and in (3) it is \(d\), and \(\lambda_s=0\) in both. Hence every row from \(k+1\) through \(s-1\) in those two cases is a supported detector row with a distinct clock. In the first case these are instead all rows through \(s\). This argument imposes no restriction on repeated clocks before row \(k+1\); no global singleton hypothesis and no assumption about clock aggregate values is needed.

## Newton vectors supplied by the same exact flag

Let \(T\) be the identified detector tail: it has physical indices \(i_j\coloneqq k+1+j\) for \(0\le j\le L\), where \(L=d\) in the first case of (2), and \(L=d-1\) in the other two. Set \(t\coloneqq i_L\), \(x_j\coloneqq c_{i_j}\), \(y_j\coloneqq1-x_j\), and
\[
 \nu(X)\coloneqq \prod_{j=0}^{L}(X-x_j),\qquad
 P_j(X)\coloneqq \prod_{a=0}^{j-1}(X-x_a)\quad(0\le j\le L).
\]
On \(T\), define a stage vector \(\mathbf v_j\) to have coordinate
\[
           (v_j)_{i_a}\coloneqq
               \frac{P_j(x_a)}{\lambda_{i_a}\nu'(x_a)}
               \qquad(0\le a\le L).                               \tag{4}
\]
Its coordinates before \(T\) are zero. In case (3) its coordinate at \(s\) is uniquely chosen to satisfy \(\boldsymbol\lambda_0\cdot\mathbf v_j=0\); in the second case of (2) take that unused final coordinate zero.

These are genuine numerical members of \(H_{d+j}\). More precisely the late subspace of \(H_{d+j}\), zero through row \(k+j\), consists of the line on \(\mathbf v_j\), plus the line on \(\mathbf e_s\) only in the augmented case. For \(j<L\), (2) or (3) says that the remaining \(L+1-j\) coordinates on \(T\) satisfy \(L-j\) independent Vandermonde rows: the degrees range from 0 through \(L-1-j=q-d-j\). Formula (4) satisfies these rows, since \(\sum_a P(x_a)/\nu'(x_a)=0\) for \(\deg P\le L-1\) by the highest coefficient of Lagrange interpolation. Its first available coordinate is nonzero. In (3), the final coordinate is fixed by the nonzero coefficient \(\lambda_{0,s}\), giving no additional line. The same description for \(j=L\) follows directly from the stated \(H_{q+1}\), which imposes no constraint on \(T\). The vector \(\mathbf v_0\) consequently captures the sole positively visible late mode at the original degree: in the augmented case the extra \(\mathbf e_s\) has zero positive taps.

On these vectors multiplication by \(C\) acts by
\[
 C\mathbf v_j=x_j\mathbf v_j+\mathbf v_{j+1}\ (j<L),
 \qquad C\mathbf v_L=x_L\mathbf v_L .
\]
This follows from \(XP_j=x_jP_j+P_{j+1}\) on \(T\). In case (3) the correction at \(s\) respects that equality, because \(\ker\boldsymbol\lambda_0\) is \(C\)-invariant and the final coordinate is uniquely determined. Strict chronology and \(AH_{d+j}\subseteq H_{d+j+1}\) yield
\[
             A\mathbf v_j=\alpha_j\mathbf v_{j+1}\quad(j<L),          \tag{5}
\]
with the equality understood modulo \(K\mathbf e_s\) only in the augmented case. At the last vector, \(A\mathbf v_L=0\) in the first case, belongs to \(K\mathbf e_s\) in the other two cases, and has no remaining detector coordinate. These are actual support statements, not graded model identities.

## The two one-detector cases: force the actual shifts, then reweight

In the two cases (2) take \(\boldsymbol\beta\coloneqq\mathbf b A^m\) with \(m=0,1\) as in the table, so \(m+L=d\). The last read of \(\boldsymbol\beta\) is exactly at \(t\). This is immediate for \(m=0\). For \(m=1\), use \(\boldsymbol\beta=\mathbf bY\), \(\beta_s=0\) and \(\boldsymbol\lambda=2\boldsymbol\beta A-\boldsymbol\beta Y\); at the last detector site \(t=s-1\), \(\lambda_t=-\beta_t y_L\ne0\). For \(m=0\) the analogous identity \(\lambda_t=-\beta_t y_L\ne0\) follows from \(\boldsymbol\lambda=\mathbf h_1\). In both cases \(\gamma_L\ne0\), where \(\gamma_j\coloneqq\boldsymbol\beta\cdot\mathbf v_j\). For the remainder of this paragraph the augmented case can be read modulo \(\mathbf e_s\), since \(A,Y,\boldsymbol\beta\) all kill it.

The paid identity on any \(\mathbf v_j\) in the available budget is
\[
 \boldsymbol\beta A^aY^r A^b\cdot\mathbf v_j
     =\frac{(m+a+r)!}{(m+a)!}
          \boldsymbol\beta A^{a+b+r}\cdot\mathbf v_j
          \qquad(a+b+r\le L-j).                                  \tag{6}
\]
This is the word identity of PENULTIMATE-PAID-TAP.md. Taking \(r=1,a=b=0\) gives
\[
                    y_j\gamma_j=(1+(m+1)\alpha_j)\gamma_{j+1}
                       \qquad(j<L).                               \tag{7}
\]

First, the \(\alpha_j\) are all nonzero. If none is nonzero, \(\boldsymbol\beta A\) kills the whole detector tail by (5), and would have final read no later than \(k\). Otherwise let \(n\) be one plus the largest index of a nonzero shift. The trailing zero shifts and (7) imply \(\gamma_n\ne0\). If some preceding shift is zero, let \(z<n-1\) be the latest such index. Set \(a=n-z-1\ge1\). The left side \(\boldsymbol\beta A^aY\cdot\mathbf v_z\) is nonzero: \(Y\mathbf v_z=y_z\mathbf v_z-\mathbf v_{z+1}\), the first term dies, and the second reaches \(\gamma_n\) along the nonzero shifts. Equation (6) makes it zero because \(A\mathbf v_z\) is zero in the relevant quotient. Thus the nonzero shifts form the entire initial run through \(n-1\).

If \(n<L\), use \(\boldsymbol\beta A^{n-i}Y A^i\cdot\mathbf v_0\) for \(0\le i<n\), a word of paid cost \(n+1\). The exact response is zero, since the \(n+1\)st tap hits the zero shift at \(n\). The successor term of \(Y\mathbf v_i\) also hits that shift. The actual response is therefore \(y_i\gamma_n\prod_{h=0}^{n-1}\alpha_h\), so every \(y_i=0\) for \(i<n\). Singleton clocks in the physical tail give \(n\le1\). Then \(\boldsymbol\beta A\) kills all vectors supported on detector positions after \(k+1\), since these are spanned by \(\mathbf v_1,\ldots,\mathbf v_L\). It also kills the possible final auxiliary position. Its actual last read is no later than \(k+1=2d+1\). But it is a genuine output tap exact for the shift \(m+1\) through tree size \(p-m-1\), so truncating at its last read and using input 1 requires at least \(3d-1\) stages for \(m=0\), or \(3d-2\) for \(m=1\). Both exceed \(2d+1\) because \(d\ge6\). This also handles the case with no nonzero shift. Thus all shifts are nonzero.

Write \(\mu_i\coloneqq\boldsymbol\beta A^i\cdot\mathbf v_0\). Then \(\mu_L\ne0\), and \(\mu_{L-1}=\mathbf bA^{d-1}\cdot\mathbf v_0=0\) by (1). In the shifted case it is the **original** penultimate \(b\)-tap that is used, so no additional minimum budget at shift 1 is needed. Let \(\boldsymbol\eta_j\coloneqq A^j\mathbf v_0\). Modulo the auxiliary coordinate,
\[
             Y\boldsymbol\eta_j
                   =y_j\boldsymbol\eta_j-\alpha_j^{-1}\boldsymbol\eta_{j+1}.
\]
Apply \(\boldsymbol\beta A^{L-j-1}\) and (6). Its two terms read \(y_j\mu_{L-1}-\mu_L/\alpha_j\), while the exact response is \((m+L-j)\mu_L\). Therefore
\[
                            \alpha_j=-\frac1{d-j}\qquad(0\le j<L).
                                                                    \tag{8}
\]

For \(0\le j\le L-2\), the actual commutator now satisfies
\[
 D\mathbf v_j\equiv\alpha_j(y_j-y_{j+1})\mathbf v_{j+1}
\]
modulo the auxiliary line when present. Indeed the coefficient on \(\mathbf v_{j+2}\) is \(\alpha_j-\alpha_{j+1}-\alpha_j\alpha_{j+1}=0\) by (8). The displayed coefficient is nonzero, since the physical clocks in \(T\) are distinct. The rooted commutator is pure at degree \(d+j+2\), which is still paid for \(\boldsymbol\beta\). Thus
\[
                            \boldsymbol\beta\cdot\mathbf v_j=0
                               \qquad(1\le j\le L-1).               \tag{9}
\]
This is obtained from actual pure directions even when \(\mathbf v_j\) differs from a pure vector by an auxiliary final coordinate.

By (4) and (9), the ratios \(\beta_i/\lambda_i\) are all equal on \(T'=T\setminus\{i_0\}\). Indeed the polynomials occurring in (9) span \((X-x_0)P_{\le L-2}\); cancel this factor against \(\nu'(c_i)=(c_i-x_0)\nu_{T'}'(c_i)\), where \(\nu_{T'}(X)\coloneqq\prod_{i\in T'}(X-c_i)\). On the \(L\) remaining distinct clocks, the moment rows through degree \(L-2\) have rank \(L-1\), and the barycentric constant-ratio column is their one-dimensional kernel. At \(i=t\), the ratio is \(-1/y_L\). It follows that the actual row
\[
                      \boldsymbol\beta'
                           \coloneqq\boldsymbol\beta+\boldsymbol\lambda/y_L
\]
vanishes on every detector position after \(k+1\) and on the possible final auxiliary position. On every rooted vector through degree \(q\), \(\boldsymbol\lambda\) vanishes. So \(\boldsymbol\beta'\) is exact for \((1-X)^m/m!\) through tree size \(q+1=p-m-1\) on a literal prefix of \(2d+1\) rows. Input 1 again needs \(3d-1\) or \(3d-2\) physical stages, respectively. Since both bounds exceed the length of the retained prefix, neither case in (2) is possible.

## The invariant terminal hyperplane

It remains to exclude case (3). Here \(L=d-1\), and no quotient is used in (5). Write
\[
            A\mathbf v_L=\omega\mathbf e_s,\qquad
            \gamma_j\coloneqq\mathbf b\cdot\mathbf v_j .
\]
The paid one-\(Y\) word gives \(b_s\omega=y_L\gamma_L\), since \(Y\mathbf v_L=y_L\mathbf v_L\). If \(\omega\ne0\), then \(\gamma_L\ne0\). If any \(\alpha_z=0\), take its last such index \(z<L\). The word \(\mathbf b A^{L-z}Y\cdot\mathbf v_z\) is paid, because its cost is \(L-z+1=d-z\). It must be zero since \(A\mathbf v_z=0\). Its actual \(Y\)-successor term runs through all later nonzero shifts to \(\omega\mathbf e_s\), giving a nonzero response because \(b_s\ne0\), a contradiction. Thus \(\omega\ne0\) would force all preceding shifts nonzero, and then the penultimate tap \(\mathbf bA^{d-1}\cdot\mathbf v_0\) would equal their nonzero product times \(\gamma_L\), contrary to (1). Therefore \(\omega=0\).

The sole late vector \(\mathbf v_0\) must have a nonzero positive \(\mathbf b\)-tap by input 3 and the late dimension shown above. Let \(n\ge1\) be the largest such index; since \(\omega=0\), \(n\le L\). This gives \(\alpha_0,\ldots,\alpha_{n-1}\ne0\), \(\gamma_n\ne0\), and \(\mathbf bA^{n+1}\cdot\mathbf v_0=0\). For each \(0\le i<n\), the paid word \(\mathbf b A^{n-i}Y A^i\cdot\mathbf v_0\) has expected value zero. Its successor contribution is also zero: if \(n<L\), this follows from \(\alpha_n\gamma_{n+1}=0\), which is the zero \((n+1)\)-st tap divided by the nonzero preceding product; if \(n=L\), it follows from \(A\mathbf v_L=0\). Its remaining term is \(y_i\gamma_n\prod_{a<n}\alpha_a\), so \(y_i=0\), in particular \(y_0=0\).

Finally let \(r\) be the largest index with \(\gamma_r\ne0\). Then \(r\ge n>0\). The paid first identity \(\mathbf bY\cdot\mathbf v_r=\mathbf bA\cdot\mathbf v_r\), together with \(\gamma_{r+1}=0\) if \(r<L\), or \(A\mathbf v_L=0\) if \(r=L\), forces \(y_r\gamma_r=0\). Thus \(y_r=0\) as well. This contradicts the distinct detector-tail clocks at indices \(0\) and \(r\).

All rank alternatives at \(s=3d+1\) are excluded. Together with the prior paid floor this proves the stated bound.
