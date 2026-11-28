# DIRK12/15: split-free scalar grid reconstruction and mixed grade-six rejection

Use the real order-twelve fifteen-stage \(C(2),f_5=3\) weighted-invisible four-distinct-dirty-ghost equality frame in either the [nine-site early return](../dirk12-fifteen-rank3-invisible-nine-site-early-return/README.md) or the [ten-site earliest extra reflected zero](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md) chronology. The [first-five ordinary prefix](../dirk12-fifteen-rank3-invisible-fifth-ordinary-live/README.md) is finite and algebraic. Here its remaining **unordered scalar support is unique**, with at most two eligible orders of the early reverse pair. All needed tests, including the actual mixed \(\alpha/\gamma\) condition, depend only on the scalar grid and uniquely determined aggregate weights. No physical pair split, unknown ghost coefficient, or scalar degree-twelve exactness is assumed.

This is an exact rejection procedure for a candidate grid, not a run of the full finite-grid elimination. The real DIRK12 interval remains **15–16**. These two reverse chronologies are essential hypotheses; the result does not classify other high-site subcharts.

## Exact reverse shape from the paid early barycentric head

Use physical reflected clock \(Y=1-c\), and \(d,v,u\) for the first three distinct nonzero reverse labels. The actual first four nonterminal reverse physical live rows are \(d,v,d,u\) at nine sites and \(d,v,0,u\) at ten sites. Thus \(r=v/d,\ t=u/d\) and
\[
  D_r=r^2-4r+1,\quad W_r=5r^2-14r+5,\qquad
  t=-r(r+1)/D_r.
\]
The actual guards exclude \(r=0,1,2,1/2,-1\) and \(D_rW_r=0\). The early pair at \(d\) in the nine-site chart has **nonzero aggregate mass**, not just two nonzero physical weights. In the ten-site chart \(d,v,u\) are singletons. The normalized \(d,v,u\) are \((1,r,t)\), denoted \(q_i\) below.

Let \(P(Y)\) be the monic hull of the fixed distinct reflected labels, including both endpoints and the first five ordinary nonzero live labels after reflection. These are exactly all labels other than \(d,v,u\). Let \(K(Y)=(Y-d)(Y-v)(Y-u)\), and \(m_j=\int_0^1 Y^jP(Y)\,dY\), \(0\le j\le4\). This moment budget is genuinely paid: \(\deg P\le7\). If \(B_s\) denotes aggregate scalar weight at \(s\), exact scalar quadrature gives
\[
       m_j=\sum_{s\in\{d,v,u\}} B_s P(s)s^j .
\]
The nonterminal reflected hull is \(PK\) if the literal terminal's reflected zero repeats, and \(PK/Y\) otherwise. At ten sites the zero repeats by hypothesis. Let \(\delta\) be \(0\) in the repeated-endpoint case, \(1\) in the unique-endpoint case. Then the derivative of the corresponding nonterminal hull \(D_{\mathrm{live}}\) at \(s=d,v,u\) is \(P(s)K'(s)/s^\delta\). This convention does not assert that the aggregate mass at a repeated endpoint is nonzero.

At ten sites the true weighted cubic \(\mathbf G\) is barycentric with scale \(\rho\). Its physical values divided by the three singleton weights are \(d^3\) times
\[
   H_{10}=\left(\tfrac16,\,
    -\frac{r^2(r-2)}{6(2r-1)},\,
    -\frac{r^2(r-2)(r+1)W_r}{6D_r^3}\right).
\]
At nine sites use the actual barycentric head \(\mathbf H=N\mathbf G-(d/2)\mathbf G\). Let
\[
 k=\frac{r-1/2}{3(r-1)(r-2)},\qquad
 h_v=\frac{r^3}{36(r-1)},\qquad
 h_u=-\frac{r^3(r+1)^2(2r-1)W_r}{36(r-1)D_r^4}.
\]
Its aggregate \(d,v,u\) readings divided by their aggregate weights are \(d^4\) times \(H_9=(-k/6,h_v,h_u)\). The first entry does **not** divide by an unknown split. In normalized units the second \(d\)-row only sees the difference \(\Delta=G_{d_2}/(b_{d_2}d^3)-1/6\), and \(H_{d_2}/(b_{d_2}d^4)=k\Delta\). Since \(G_{d_2}=-G_{d_1}=-b_{d_1}d^3/6\),
\[
                     H_{\rm agg}(d)=-d^4 k B_d/6 .
\]
Thus in either chart the three barycentric equations have the exact form
\[
             B_s\,d^\kappa H_{{\rm chart},s}\,D_{\mathrm{live}}'(s)=\rho ,
 \qquad \kappa=3\text{ or }4.
\]
The unknown \(\rho\ne0\) has now one common role, not a per-row free normalization.

For a list \(H\) of these normalized amplitudes put
\[
              S_j(H)=\sum_i
                   \frac{q_i^j}{H_i\prod_{\ell\ne i}(q_i-q_\ell)} .
\]
The exact moment equations above give \(m_j=(\rho/d^{\kappa+2-\delta})d^j S_{j+\delta}(H)\). A rational identity checked in the replay is
\[
          S_{j+1}(H_9)
               =-\frac{6(r-1)(r-2)}{2r-1} S_j(H_{10}),\qquad 0\le j\le4.
\]
Use \(n_j=m_j\) for the ten-site case and the nine-site unique-endpoint case, and \(n_j=m_{j+1}\) for the nine-site repeated-endpoint case. Then the same five-term rational sequence, up to overall nonzero scale and the degree scaling by \(d\), governs all available \(n_j\). In particular \(n_0,n_1,n_2,n_3\ne0\). In the repeated nine-site case \(m_0\) itself **can** vanish; it is not used as a divisor.

## Unique unordered cubic and scale-only gates

Put \(q=n_0 n_2/n_1^2\), \(h=3n_1/(2n_0)\). Direct simplification gives
\[
 q=\frac{9(r-1)^2}{4(r^2-r+1)},\qquad
 h=d\frac{r(r+1)}{(r-1)^2},\qquad
 L=\frac{4q}{9-4q}=\frac{(r-1)^2}{r}.
\]
Thus the exact guard on an actual real prefix is \(0<q<3\) with
\[
                 q\notin\{3/4,\,1,\,3/2,\,9/4\}.
\]
These follow respectively from \(r\ne2,1/2\), \(W_r\ne0\), \(D_r\ne0\), and \(r\ne0\). The lower and upper strict inequalities follow from \(r\ne1,-1\) and \(r^2-r+1>0\). The only unordered support is now rational in the fixed prefix:
\[
       s=d+v=hL,\qquad p=dv=\frac{h^2L^2}{L+4},\qquad
       u=-\frac{hL}{L-2}.
\]
All denominators are guarded. Thus one adjoins just the monic orientation root \(d^2-sd+p=0\) (then \(v=s-d\)); its two roots are distinct in an actual chart, and swap \(d,v\) while leaving \(u\) fixed. Equivalently \(r\) is a root of
\[
              4n_0n_2(r^2-r+1)-9n_1^2(r-1)^2=0.
\]
Its leading coefficient cannot vanish: equality \(4n_0n_2=9n_1^2\) makes the residual equation \(9n_1^2 r=0\), impossible. The unordered cubic \(K=(Y-u)(Y^2-sY+p)\) is already defined before adjoining this single orientation. In particular there is at most one unordered live scalar grid and two physical early orientations per exact ordinary prefix.

There are very cheap rejection tests before any extension:
\[
 \begin{split}
 (3n_1^2-n_0n_2)n_3-2n_1n_2^2&=0,\\
 2(9n_1^2-4n_0n_2)n_2n_4-5(3n_1^2-n_0n_2)n_3^2&=0
                       \quad\text{when }n_4\text{ is available}.
 \end{split}
\]
In the nine-site repeated-endpoint case the second is replaced by
\[
             3m_0m_3m_2^3
                 =m_1(4m_1m_3-3m_2^2)(5m_2^2-2m_1m_3).
\]
They are exact identities of the paid normalized moments, even if \(m_0=0\) in the last case. The replay uses a genuinely algebraic zero-\(m_0\) control for the division-free treatment. If the fourth distinct reverse nonzero-after-\(u\) read instead occurs at reflected zero in the nine-site chart, the already-paid quartic relation in its mixed note gives \(3r^2-7r+3=0\), hence **\(q=9/16\)** as a further split-free test. In that event the fifth ordinary nonzero live clock itself is ordinary \(1\).

## The exact mixed condition knows no physical weight split

Once the support is constructed, the aggregate scalar weights are uniquely given by the paid cardinal integrals on the full hull \(PK\). The actual unpaid moment is then exactly
\[
                  \varepsilon_{12}=\sum_s B_s(1-s)^{12}-1/13 .
\]
It is not imposed to be zero. It is also obtainable directly by division: for \((1-Y)^{12}=Q(Y)P(Y)K(Y)+R(Y)\), the moment discrepancy is \(-\int_0^1 QPK\) since the remainder degree is paid.

The ordinary pair \((\alpha,\gamma)\) up to a common nonzero factor is already known. If \(L_6'(a)\ne0\), use the coefficients of the geometry-free cardinal \(V\) on \(G_5,G_7\), since \(V\) is proportional to the actual \(r(s)-r(1)R(s)=\alpha G_5+\gamma G_7\). The true readings are \(V(x)=1,V(y)=\theta\) and the \(2\times2\) determinant is nonzero. If \(L_6'(a)=0\), use the \(L_5',L_7'\) coefficients of the known normalized \(r(s)\) in the three-mode interpolation on \(1,x,y\). The just-proved actual three-mode rank covers this first-root case as well. Its first three \(r\)-readings come from the two genuine scalar solves in the [first-root projection](../dirk12-fifteen-rank3-invisible-no-late-first-root-projection/README.md), not from early ghost parameters. In both cases \(\gamma\ne0\) by the original mixed proof.

At ten sites fix \(\rho=B_d d^3 D_{\mathrm{live}}'(d)/6\). At nine sites fix \(\rho=B_v d^4 h_v D_{\mathrm{live}}'(v)\). The remaining two early amplitude equations in each case should also be checked (discrepancies appear in the evaluator). For \(w\), the next distinct reverse label after \(u\), its physical value is \(1-f\), where \(f\) is the known fifth ordinary nonzero live clock. If \(w\ne0\), it is a singleton and its actual normalized head amplitude follows from \(\rho/D_{\mathrm{live}}'(w)\) and its unique aggregate weight; no physical split enters. If \(w=0\) it is the optional nine-site duplicated endpoint, and we **do not** divide by its physical weight.

Compute the actual reverse divided differences as follows. For these computations use normalized reflected clock \(Y/d\) and actual weighted reverse row divided by \(d\). Write \(E_6\) for the genuine scalar quintic-input discrepancy and \(Z\) for the actual pure word \(N(Y^2\mathbf G)\) at ten sites or \(N(Y\mathbf H)\) at nine sites. In the ten-site case use ratios \(E_6/G,Z/G\) on normalized labels \(1,r,0,t,w/d\), as in the [mixed source proof](../dirk12-fifteen-rank3-invisible-ten-site-early-zero/README.md). At the early zero, the positive-degree scalar ratios use \(T_1/g_0=-1/(r-1),T_r/g_0=1/[r(r-1)]\) directly, so neither the physical split nor unknown \(g_0\) enters. For \(u,w\), evaluate the true cubic/quartic nonzero-node cardinals and then their scalar degree-five and actual \(Y^2\mathbf G\) reads.

In the nine-site case use \((E_6-2d^3\mathbf G)/H,Z/H\) on \(1,r,t,w/d\), employing the second \(1\)-row at the pair label. In the normalized variables the pair read is exactly
\[
        (E_6-2G)/H\big|_{1_2}=(r^3+r^2+r-1)/k.
\]
Indeed its literal aggregate taps are \(1/2-\Delta/(r-1)\) and \(\Delta/[r(r-1)]\); the normalized \(G/H\) values are \(1/6+\Delta,k\Delta\); substituting cancels the physical split. For the \(Z/H\) ratio, the original true formula is \(\psi(1)+h_v/(rk)\), using the genuine affine lift ratio \(\psi\). At \(u\) or the next live label, the pair's \(H\) contribution is recovered by \(\Delta T_{1_2}=h_s-(1/6)T_1\), not by reconstructing either physical weight. At \(w=0\) the normalized \(T_j/h_w\) are the leading coefficients of the three cubic cardinals times \(3(r-1)(r-2)\); hence both needed ratios use only this charged \(\mathbf H\) amplitude cancellation. This is exactly the actual row used in the [nine-site mixed proof](../dirk12-fifteen-rank3-invisible-nine-site-early-return/mixed-grade-six.md).

Let \(C_E,C_Z\) be the respective divided differences of these normalized ratios. Their **ratio** equals that in physical units: in both columns the same powers of \(d\) from the ratio and divided difference cancel. \(C_Z\ne0\) is proved in the original respective mixed subchart rather than inferred from a numeric candidate. The exact split-free scalar mixed residual is now
\[
                   \alpha C_Z
            +462\cdot24024\,\gamma(\rho C_E-\varepsilon_{12}C_Z)=0 .
\]
All inputs derive from the algebraic live-grid hull and its orientation. This is the true mixed relation; in particular it is not legitimate to use merely an arbitrary degree-nine quadrature or neglect the whole \(\varepsilon_{12}\) term. On the monic orientation algebra one can use the norm of the mixed residual to reject both orientations at once when it is nonzero, or keep individual zero factors. Passing this test does not assert tableau feasibility.

## Monic continuation without tacit degree preservation

Here is a small candidate algebra for exact ensuing elimination. Start with the squarefree monic normalization of the nonzero \(x\)-obstruction for each of the two [ordinary root/nonroot prefix proofs](../dirk12-fifteen-rank3-invisible-all-ordinary-prefixes/README.md); those obstruction polynomials are specified by finite determinants but have not been expanded here. Work over the exact finite component fields. In a component, adjoining a real candidate coordinate uses the literal degree of its nonzero polynomial, not its generic leading coefficient. Split components by exact guard evaluation or factorization; remove only defects excluded for actual candidates.

* A first Legendre root \(a\) satisfies the fixed degree-five equation. In the nonroot case the exact two-clock polynomial in \(a\) is always nonzero, of degree at most five; when its leading coefficient drops on a permitted \(x\) factor, normalize the actual retained degree. The first \(y=c/a\) polynomial strips its two genuine excluded roots and has exact degree five above either component.
* If the fourth diagonal is **nonzero**, \(t_f=e/a\) is rational over the first three. In the nonroot case use the Möbius ratio \(x(y-1)/(2xy-x-y)\). In the first-root case use \(\mathcal I(TP_0)/\mathcal I(P_0)\), \(P_0=T(T-1)(T-x)(T-y)\). Indeed the grade-five ghost-zero mask criterion is \(\mathcal M(F)=0\), and the actual first root gives \(r(1)\mathcal M(F)=\mathcal I(F)\). A nonzero kernel combination of \(P_0,TP_0\) has zero genuine \(F_7\) commutator at the first three rows and therefore at the fourth, yielding the same true diagonal-only argument as in the Möbius case. If \(\mathcal I(P_0)=0\), the mask \(P_0\) contradicts the actual fourth diagonal and distinctness, so the ratio denominator is guarded.
* If the fourth diagonal is **zero**, \(t_f\) has a nonzero polynomial of degree **at most two** in either branch. In the nonroot case use the stripped \(R_6-R_0\) equation in the zero-diagonal note; it cannot be the zero polynomial since \(R_6(0)=-42/L_6'(a)\ne0\) but \(R_0(0)=0\). In the first-root case put \(I_i=\mathcal I(T^iP_0),\ K_i=\mathcal K(T^iP_0)\) using the normalized first-root scalar model; its exact determinant \(\Delta=I_0K_1-I_1K_0=-(5x^2-5x+1)D/10800\ne0\). Under zero fourth diagonal the two literal nodal equations solve the target \(k\)-mode as \(k_0=(I_0J(TP_0)-I_1JP_0)/\Delta\). The exact \(k-k_0\) vanishes at \(0,1,x,y\), hence its quotient by \(P_0\) has degree at most two. It is nonzero because \(k'(0)\ne0\) while \(k_0'(0)=0\) by the two genuine scalar primitives.
* The fifth ratio has degree at most three. It drops to at most two when the fourth diagonal is nonzero in **either** branch, by the corresponding masked nodal test eliminating the degree-eight term. Its polynomial is never identically zero on an actual prefix by the fixed quartic receipt. Incorporate the cheap reverse scale-only cubics/quartics as gcd cuts here: the \(m_j\) are linear in the fifth clock if it contributes a new fixed label. If it coincides with the terminal, treat that exact collision separately. The ordinary endpoint may be repeated only in the nine-site case among the five forward clocks here; in the ten-site case the repeated terminal is already in the fixed earliest reverse prefix.
* Reconstruct the unordered cubic rationally, adjoin the single monic orientation quadratic, and check paid scalar quadrature, both other barycentric amplitude equations, and zero mixed residual under its nonzero mode guards. In particular the maximum extension degrees after the \(x\)-obstruction are \(5,5,1,2,2\) for nonzero fourth diagonal and \(5,5,2,3,2\) for zero fourth diagonal. These are degree bounds, not a degree-preservation claim about arbitrary modular specializations. Any coefficient-prime elimination must justify integrality, nonzero local denominators and actual degree for the retained fields, not extrapolate from a reduced unknown tableau.

Run:

    python3 -B verify.py

The local exact replay checks the universal moment/scale factors, the pair-split and optional reflected-zero arithmetic, and three labeled rational negative-control arithmetic paths. Negative controls are not order-twelve tableaux or actual scalar grids. The module grid.py exposes exact algebraic evaluation of the necessary conditions; it does not enumerate the unexpanded finite obstruction roots. A separate native scalar guard checks the monic orientation pivot; the entire graded mathematical argument is not Lean-formalized.
