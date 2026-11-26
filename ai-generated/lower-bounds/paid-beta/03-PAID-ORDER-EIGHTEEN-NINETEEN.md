# The 27- and 29-stage ERK bounds need no characteristic-zero assumption

Let \(m\ge0\), let \(r\in\{18,19\}\), and let \(K\) be a field in which \((m+r)!\ne0\). Let \(A\) be a strictly lower triangular \(n\)-stage matrix. Suppose a row \(L\) assigns to every rooted stage-derivative vector of tree order at most \(r\) its exact scalar polynomial averaged with weight \((1-x)^m/m!\) on \([0,1]\). Then \(n\ge27\) when \(r=18\), and \(n\ge29\) when \(r=19\). All integrals below mean evaluation of a formal primitive. In particular the ordinary denominator-cleared bounds hold over every nonzero commutative unital ring, and the bounds also apply to the actual retained prefixes of these two orders in an explicit weighted tap.

This strengthens the coefficient domain of the existing characteristic-zero finite theorem, not its numerical statement in characteristic zero. The earlier chart and shape proof is in RKResearch commit c1d29976a37f7f264f7123bf0cd69a8126a107b3, ai-generated/lower-bounds/proof-dependencies/pass2245_finite_analytic.md and ai-generated/lower-bounds/characteristic-zero/erk_characteristic_zero_p16_p19_finite_gate_and_quadratic_quasirule_20261123.md. We give the complete nine-degree chart argument below using the elementary pair/separation, Hankel determinant, chronology and counted-bound lemmas from the companion 01-PAID-GRADE-FIVE-SURPLUS.md and the rank-one chain and two-endpoint lemma from 02-PAID-DOUBLING-SURPLUS.md. No other finite order exclusion is needed.

## The forward and reverse ranks

The notation \(c=A\mathbf1,\ C=\operatorname{diag}(c),\ Y=I-C\) is as in the companion. The space \(E_j\) contains first components of the rooted pairs through polynomial degree \(j\), that is, through tree order \(j+1\); \(F_j\) contains the pairs' vectors with polynomial component zero. Within separation \(E_j=P_{\le j}(c)\oplus F_j\), where \(P_{\le j}(c)\) denotes the evaluations of polynomials of degree at most \(j\). Pairing with \(L\) has scalar action
\[
 \ell_m(f)\coloneqq \int_0^1\frac{(1-x)^m}{m!}f(x)\,dx.
\]
Write \(r=2q+\epsilon\) with \(q=9,\epsilon\in\{0,1\}\).

For \(j\ge1\) define
\[
 \rho_j\coloneqq L Y^{j-1}A-\frac{L Y^j}{m+j},\qquad
 R_0\coloneqq0,\qquad
 R_j\coloneqq R_{j-1}+R_{j-1}A+R_{j-1}Y+\operatorname{span}(\rho_j).
\]
Formal integration by parts gives \(\ell_m((1-x)^{j-1}Jf)=\ell_m((1-x)^j f)/(m+j)\). Thus \(R_j\) annihilates \(E_i\) whenever \(i+j\le r-1\). The reverse triangular lemma applied with \(D=Y\) to \(LY\) and \(\rho_2\) gives strict growth of \(R_j\) from \(j=2\) onward in this budget (a plateau would contain \(LY\), which does not annihilate \(\mathbf1\)). Hence \(\dim R_j\ge j-1+\dim R_1\).

We will use the following Hermite rank argument in both directions. For a strictly lower triangular \(N\), diagonal \(D\), column \(v\), and \(D\)-invariant subspace \(U\), suppose \(v,Dv,\ldots,D^k v\) are independent modulo \(U\). Suppose a subspace \(W\) contains \(U\), \(NU\), and every
\[
 ND^a v-\frac{D^{a+1}v}{\mu+a+1},\qquad 0\le a\le k
\]
for an integer \(\mu\ge0\) with those denominators nonzero. Then \(\dim W\ge\dim U+\lfloor(k+1)/2\rfloor\). Indeed, chronologically compress on the sum of \(U\) with the displayed independent powers (the argument uses coordinate predecessor substitution as in the companion). Its annihilator of \(U\) decomposes by scalar label, one normalized row per represented label \(z\), each supported on that label and sending the compressed \(v\) to 1. There are \(k+1\) such rows, because a row supported on one label and killing \(v\) would kill the entire compressed coordinate space. Take the first \(\lfloor(k+1)/2\rfloor\) nonzero labels ordered by the latest index of each normalized row. If a nonzero combination \(\lambda\) of those rows kills the restriction of \(W\), then \(\lambda N\) kills \(U\) and is supported strictly before the latest index of the last label in the combination. It is therefore a combination of only earlier normalized rows. Let \(z\) range over all earlier nonzero represented labels. Choose
\[
 P(x)\coloneqq x^\eta\prod_z(x-z)^2,\qquad
 \psi(x)\coloneqq P'(x)+\mu P(x)/x ,
\]
where \(\eta=2\) if the zero label occurs earlier and \(\eta=1\) otherwise. Then \(\deg\psi\le k\) and \(\psi\) vanishes at every earlier label. The monomial map \(x^a\mapsto x^{a+1}/(\mu+a+1)\) carries \(\psi\) to \(P\). The assumed defects give \(\lambda N\psi(D)v=\lambda P(D)v\), whereas the left side vanishes and the right side is nonzero from the last label's coefficient. This proves the claimed rank bound, without choosing generic field elements.

For the forward use take \(N=A,D=C,v=\mathbf1,\mu=0\) and \(W=F_{k+1}\). For the reverse use transpose and reverse the physical order: \(N\) is the reindexed transpose of \(A\), \(D\) is the reindexed \(Y\), \(v\) is the reindexed transpose of \(L\), \(\mu=m\), and take \(U=R_k,\ W=R_{k+1}\) after the same reindexing. Whenever \(2k\le r-1\), the needed backward powers are independent modulo \(R_k\). Pair a relation among these powers with \(1,Y\mathbf1,\ldots,Y^k\mathbf1\). The scalar matrix is the Hankel matrix for \(y^m/m!\) under the substitution \(y=1-x\), nonsingular by the companion's determinant with \((a,b,h)=(m,0,k+1)\). Its last factorial index is \(m+2k+1\le m+r\).

Assume contrary to the theorem that \(n\le3q+2\epsilon-1\). The companion's paid fifth-degree surplus and its count force equality and \(\dim F_j=j\) for \(5\le j\le q\), using forward strict growth. Thus \(\dim E_{q-1}=2q-1,\ \dim E_q=2q+1\). The last weight \(L_n\) is nonzero: otherwise a strictly shorter prefix has the same hypotheses. There are three cases.

- If \(r=18\), dimension equality gives \(R_1=0\) and \(\dim R_t=t-1\) through \(t=q-1\). Use all coordinates. The last clock is \(c_n=1\); all reverse rows have last coordinate zero. The vector \(e_n\) is in \(E_q\) since \(R_{q-1}\) is its entire annihilator. For \(v\in F_{q-1}\), exactness on the product of pairs for \(e_n\) and \(v\) (degree at most \(2q-1\)) gives \(L_n v_n=0\).
- If \(r=19\) and \(R_1\ne0\), use all coordinates. The dimensions are \(\dim R_t=t\) through \(t=q\).
- If \(r=19\) and \(R_1=0\), then \(c_n=1\), reverse rows have last coordinate zero, and \(e_n\notin E_q\) by the odd missing-column argument in the grade-five companion (the determinant there is paid by \(m+2q+1=m+r\)). Keep the first \(n-1\) rows, so restriction is injective on \(E_q\). The dimensions are \(\dim R_t=t-1\) through \(t=q\).

Write a hat for the retained coordinates (the identity in the first two cases). In all cases, with \(t=r-1-j\), \(\dim\widehat E_j\le q+j+1\) for \(q\le j\le r-2\), by annihilation against the stated reverse ranks. When equality holds and \(j\le r-4\), \(\widehat E_j\) is not \(C\)-invariant. Otherwise its full annihilator on the retained coordinates, the restriction of \(R_t\), would be \(Y\)-invariant, so \(R_t\) itself would be invariant (also in the prefix case, where all its omitted entries are zero). Backward Hermite then forces the increment at \(t+1\) to be at least \(\lfloor(t+1)/2\rfloor\). For \(j>q\), this is at least two, contradicting the exact reverse increment one. For \(j=q\), \(t=q-1\) or \(q\); the upper bound from \(R_{t+1}\) annihilating \(E_{q-1}\), even after restriction, permits only two extra dimensions, not four or more. Therefore from every such equality the next \(\widehat E_{j+1}\) is exactly \(\widehat E_j+C\widehat E_j\).

## The one expanding chain and its polynomial complement

The forward Hermite bound excludes \(C\)-invariance of each \(F_j\) for \(5\le j<q\), since its increment is only one. Invariance at \(F_q\) is also impossible by the invariant endpoint count in the doubling companion:
\(\dim F_q\ge\lceil3q/2\rceil-3=11>9\). Apply the rank-one diagonal filtration to \(F_5\). For its largest \(C\)-invariant subspace \(U\), there is a head \(w\) such that, for \(k\coloneqq5-\dim U\),
\[
 F_j=U\oplus wP_{\le k+j-6}(c)\quad(5\le j\le q),\qquad
 Z\coloneqq F_q+CF_q=U\oplus wP_{\le k+q-5}(c).
\]
Here \(wP_{\le d}(c)\) means all coordinatewise products \(wP(c)\) with \(\deg P\le d\). In the even case \(F_q\) and \(Z\) vanish last since \(F_q=F_{q-1}+CF_{q-1}\). Hermite applied to \(U\subset F_5\) gives \(6\ge\dim U+3\), so \(k\ge2\); thus \(w,Cw\in F_5\). Restriction is injective on \(Z\), since \(Z\subset F_{q+1}\), which \(L\) kills, and the only coordinate possibly discarded has \(L_n\ne0\).

In the even case an intersection \(f(c)\in P_{\le q}(c)\cap Z\) would have \(f(0)=f(1)=0\). Test \(f=x(1-x)g\) against all polynomials through degree \(q-2\); the weight \(x(1-x)^{m+1}\) Hankel forces \(g=0\). In the full odd case the same argument uses only \(f(0)=0\), all tests through \(q-1\), and weight \(x(1-x)^m\). These factorizations use the exact moment identities, not positivity. For the odd prefix suppose \(\widehat{f(c)}\in\widehat Z\). In the full space \(f(c)-z=\gamma e_n\) for \(z\in Z\). Multiplying by \((1-c)P(c)\) kills that column, hence \(f/x\) (which exists by the first coordinate) is orthogonal for the weight \(x(1-x)^{m+1}\) to all polynomials of degree at most \(q-2\). Thus the possible intersection is at most one line, and the line, if present, has representative of degree exactly \(q\) by the same Hankel determinant. All budget inequalities here follow by testing \(Z\subset F_{q+1}\) through degree \(r-2-q\), and the factorial indices are at most \(m+r\).

If the intersection is zero, set \(d=q\). The dimension cap at \(q+1\) gives
\(\widehat E_{q+1}=\widehat P_{\le d}(c)\oplus\widehat Z\). Represent \(c^{q+1}\) there to obtain a monic polynomial \(G\) of degree \(d+1\) whose evaluation belongs to \(\widehat Z\). If the line is present, set \(d=q-1\) and let \(G\) be its monic polynomial of degree \(q\). The value \(G(c)\) after restriction is not in \(\widehat F_q\), by separation and injection on \(E_q\). Since \(Z/F_q\) is one-dimensional, \(\widehat Z\subset\widehat E_q\) and \(\widehat E_q=\widehat P_{\le d}(c)\oplus\widehat Z\).

In either case \(C\widehat P_{\le d}(c)\) lies in the base space, because it contains \(c^{d+1}\). As the dimension cap grows from this base through \(\widehat E_{r-3}\), the noninvariance just proved forces one new clock power of the head at each step. These are direct sums, including
\[
 \widehat E_{10}=
 \widehat P_{\le d}(c)\oplus\widehat U\oplus\widehat wP_{\le D}(c),\qquad
 D=\begin{cases}
 k+4,&\text{zero intersection},\\
 k+5,&\text{one-dimensional intersection}.
 \end{cases}
\]
The analogous decomposition at \(E_{11}\) uses \(D+1\). A label is effective if the clock-block projection of \(\widehat w\) is nonzero modulo the corresponding block in \(\widehat U\). Vandermonde rank on these labels shows that their number is at least \(k+r-8\) in the first case and \(k+r-7\) in the second, using the full direct chain through \(E_{r-3}\). Denote this number by \(N\); in particular \(N-1>D\).

## The polynomial component of the needed products vanishes

For \(v\in F_{10}\), let \(H\) be the polynomial in the \(E_{10}\) direct sum. In the even case restrict the following statement to vectors \(v\) with last coordinate zero; every product of two \(F_5\) vectors has that property. In the cases without a one-dimensional intersection, the extended head and core at degree 10 have lifts in \(F_{10}\). If the intersection is one-dimensional, the lift may require \(F_{11}\), from the one additional clock power.

The first coordinate gives \(H(0)=0\) in all cases. In the full even case \(H(1)=0\) too; \(H/[x(1-x)]\) has degree at most 7. The eight tests through degree 7, available for \(F_{10}\), force \(H=0\) by the \(x(1-x)^{m+1}\) Hankel. In the full odd case \(H/x\) has degree at most 8; the nine tests through degree 8 force \(H=0\) by the \(x(1-x)^m\) Hankel.

For the odd prefix use the tests with an additional factor \(1-x\) to kill the omitted coordinate. With zero intersection \(H/x\) is then of degree at most 8 and orthogonal through degree 7. With a one-dimensional intersection the corresponding numbers are 7 and 6 because the \(F_{11}\) lift costs one additional degree. Let \(a\) respectively be 8 or 7. Write \(D_j\) for the monic degree-\(j\) polynomial orthogonal through degree \(j-1\) for the form
\[
 \langle f,g\rangle\coloneqq\int_0^1 x(1-x)^{m+1}f(x)g(x)\,dx .
\]
Then \(H/x\) is a scalar multiple of \(D_a\). The same prefix tests give \(G/x\) orthogonal through degree 7 in both cases, since \(G(c)\) has a lift in \(Z\subset F_{10}\). In particular it is orthogonal to \(D_{a-1}\). There is no need to construct the next orthogonal polynomial or invoke any recurrence coefficient. If both \(v,Cv\) are in \(F_{10}\), write \(H_0,H_1\) for their polynomial components. Shifting the \(E_{10}\) decomposition to \(E_{11}\), subtracting, and dividing by the monic \(G\) gives \(H_1-xH_0=\kappa G\) for some \(\kappa\): the evaluated remainder has degree at most \(d\) and lies in the head-plus-core part of the direct sum at \(E_{11}\). Divide by \(x\) and pair with \(D_{a-1}\). The terms \(H_1/x\) and \(G/x\) disappear. But \(\langle xD_a,D_{a-1}\rangle=\langle D_a,D_a\rangle\ne0\), since \(xD_{a-1}-D_a\) has degree at most \(a-1\). The norm is nonzero by invertibility of the Gram matrix through degree \(a\). Thus \(H_0=0\); comparison of degrees with \(G\) also gives \(H_1=0\).

For this odd-prefix computation the last factorial index of the relevant Gram matrix is \(m+2a+3\le m+19\) (use \((a_{\rm Hankel},b,h)=(1,m+1,a+1)\) in the companion). Pairing \(G/x\) at the higher used degree costs at most \(m+2+9+7+1=m+19\) as well. The even full and odd full determinants use at most \(m+17\) and \(m+18\), respectively. Thus every invertibility assertion remains within the stated factorial budget.

## Two true chronological tests

If \(u\in U\) is confined to one clock and \(v\in F_5\), then \(uv\) and \(Cuv\) lie in \(F_{10}\); this uses invariance of \(U\). The preceding paragraph puts \(\widehat{uv}\) in the head plus core, and its head polynomial vanishes on the other at least \(N-1>D\) effective labels. Thus \(\widehat{uv}\in\widehat U\). This holds for every \(u\in U\) by applying the clock-block projections and summing. In particular \(\widehat U\) is a coordinatewise algebra. It contains the indicator \(e_T\) of its support \(T\): for each member interpolate its support indicator by a polynomial vanishing at zero, and take the union of these finitely many supports using \(e_{B\cup B'}=e_B+e_{B'}-e_Be_{B'}\). Subtract from \(w\) a lift in \(U\) of \(e_T\widehat w\), which belongs to \(\widehat U\) by the product result. The new head is disjoint from \(T\); let \(S\) be its support on the retained rows. Its distinct clock labels are exactly the \(N\) effective labels.

For \(0\le a\le2k-2\), \(C^a w^2\) is the product of two paid head powers from \(F_5\). Every consecutive pair has zero polynomial component by the preceding argument. On the retained coordinates it is supported on \(S\), so belongs to \(\widehat wP_{\le D}(c)\), with no core component. Divide by \(w\) at these nodes. The polynomial representatives of successive shifts are successive multiples by \(x\), because equality on \(N>D+1\) distinct labels uniquely identifies polynomials of degree at most \(D+1\). Therefore \(w_i=P(c_i)\) on \(S\), for a nonzero \(P\) of degree at most \(D-(2k-2)\). If the earlier intersection was zero this is at most \(6-k\le4\). Otherwise \(G(c)\) has a representation on \(Z\) with nonzero coefficient of the newest head power \(k+4\), since it was not in \(\widehat F_q\). On \(S\) this gives \(G(c)=P(c)Q(c)\) with \(\deg Q=k+4\) and product degree at most 11. There are more than 11 effective labels, so this is a polynomial factorization and \(\deg P=9-(k+4)=5-k\le3\). Thus \(\deg P\le4\) in all cases.

For \(M=x\) or \(M=x(x-u)\), form the retained contrast
\[
 z_M\coloneqq (MP)(c)(1-e_T)-M(C)w
\]
on those rows. The last terms have full-vector lifts from \(U\) and from the paid head powers, and \((MP)(c)\) has degree at most 6. Separation and injection on \(E_q\) make \(z_M\) nonzero. Its first nonzero retained coordinate lies outside \(S\cup T\), at some clock \(\xi\) with \(M(\xi)P(\xi)\ne0\). For each \(B\) with \(\deg(BM)\le4\), the lift of \(B(C)z_M\) has polynomial component \(BMP\) and degree at most 8: the head term uses \(w,Cw\in F_5\), then at most three further clock powers. Applying \(A\) uses degree at most 9. At the first nonzero retained coordinate its actual value is zero by strict chronology, and its difference from the formal primitive \(J(BMP)\) is a vector of \(F_9\), whose retained values outside \(S\cup T\) vanish. Consequently
\[
 \int_0^\xi B(x)M(x)P(x)\,dx=0.
\]
The choice \(M=x\) supplies \(u\ne0\) and four first tests; the choice \(M=x(x-u)\) supplies \(v\notin\{0,u\}\) and three second tests. Rescale by \(u\). The two-endpoint Rodrigues lemma for degree 4 from the doubling companion gives \(P=0\), a contradiction. It uses only integers through 9, not either fixed-knot quartic certificate or the free-pencil calculation of the order-16/17 proof.

We conclude \(n\ge3q+2\epsilon\). For a nonzero coefficient ring, the cleared tall-tree equation makes the order factorial a unit; the field statement applies after passage to any residue field. For actual weighted taps \(L=\mathbf b^{\mathsf T}A^m\) over a field, strict causal restriction to its last contributing index and the rooted unary rules verify the stated weighted hypothesis at \(r=p-m\). No new Lean certificate or stronger characteristic-zero numerical bound is asserted.
