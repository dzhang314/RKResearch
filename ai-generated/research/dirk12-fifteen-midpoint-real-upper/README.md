# An exact real-algebraic 15-stage DIRK method of order twelve

The real ordinary DIRK minimum for order twelve is **15**. This construction gives the upper bound over the real algebraic numbers, matching the [established ordered-field lower bound](../../lower-bounds/README.md). It does not assert that the minimum is 15 over the rationals or every ordered subfield. The exact order-thirteen bush fails. The method is an ordinary DIRK with nonzero implicit diagonals and both an explicit first row and explicit literal terminal, not an ERK or a strict SDIRK.

The coefficients are specified by algebraic root brackets and the complete rational expression evaluator [construct.py](construct.py). The [degree-216 field receipt](../dirk12-fifteen-midpoint-degree216-field/README.md) verifies the exact real field and a named embedding. The [characteristic-zero replay](verify-char0.py) proves the needed zero identities over its degree-108 subfield, with no modular inference of zero. The [selected finite component bridge](replay-mod17.py) proves that every used field denominator is nonzero and that the order-thirteen bush is nonzero. The [complementary-support proof](SUFFICIENCY.md) accounts for **all** rooted trees, not just scalar modes or a numerical scan. This is an exact mathematical construction and replay; a full native Lean theorem is not claimed here.

## Coefficient field and scalar quadrature

Use \(a=1/2\), \(x,y,t,f\) from the named real embedding in the field receipt, with \(x,y,t\) normalized ordinary ratios and \(f\) the physical fifth clock. The physical first five nonzero ordinary live clocks are \(a,ax,ay,at,f\). Let \(P_*(Y)\) be the monic polynomial with roots \(0,1\) and the reflections of those five clocks. Put \(n_j=\int_0^1Y^jP_*(Y)\,dY\). With the previous notation \(h=3n_1/(2n_0), q=n_0n_2/n_1^2,L=4q/(9-4q)\), choose \(d\) as the plus-square-root orientation of the quadratic, \(v=hL-d\), and \(u=-hL/(L-2)\). Thus the unordered reverse cubic is \(K(Y)=(Y-d)(Y-v)(Y-u)\), and the full ten-site hull is \(S(Y)=P_*(Y)K(Y)\).

Use the cardinal scalar weights \(B_s=\int [S(Y)/(Y-s)]\,dY/S'(s)\) on the ten distinct labels. These weights integrate all polynomials through degree nine. The two exact replay identities \(\int S=\int YS=0\) extend exactness through **degree 11**. For the one repeated nonterminal label \(d\), use two equal physical weights \(B_d/2\); all other live sites have their unique nonzero weights. The ordinary literal terminal of clock one is unique. This is a mathematical construction, allowed to use signed weights.

Define \(D_{\rm live}(Y)=S(Y)/Y\), the nonterminal live hull. Define the polynomial \(M(s)\) by synthetic cofactor integration of \(S\), so \(M(s)=\int S(Y)/(Y-s)\,dY\) on its roots, and \(B_s=M(s)/S'(s)\). For \(s\ne0\),
\[
                        B_sD_{\rm live}'(s)=M(s)/s.
\]
This identity will avoid any division by the physical pair weights in the characteristic-zero zero tests.

## Literal ordinary opening and reverse rows

The ordinary physical order is the literal origin, four ghosts, the five first nonzero live clocks, then \(1-u,1-d,1-v,1-d,1\), with the first of the two ordinary \(1-d\) rows denoted \(d_2\) in reverse and the later one \(d_1\). All four initial ghosts have zero weight. They use the rational normalized clocks \(p=(1/4,1/3,8/11,1)\), the explicit lower triangular four-row block \(A_g\) and tap weights \(\boldsymbol\ell\) in the constructor. Multiply the block by \(a\) for physical units. In the normalized block the actual cubic amplitudes \(h_g\) are nonzero and \(\ell_g h_g D_g'(p_g)\) is one common nonzero scalar, where \(D_g=\prod(Y-p_g)\). The exact identities from the literal rational block are
\[
 \sum_g\ell_g p_g^j=\frac1{j+1}\ (1\le j\le5),\qquad
 A_g p=p^2/2,\quad
 A_g^{\mathsf T}\boldsymbol\ell=(1-p)\boldsymbol\ell,\quad
 A_g^{\mathsf T}(p\boldsymbol\ell)=\frac{1-p^2}{2}\boldsymbol\ell.
\]
Here expressions in \(p\) act componentwise. The literal origin taps will be fixed by the row sums, so omitted origin terms do not affect any displayed positive-power or cubic-defect identity.

The first five ordinary live-only rows are specified by the exact polynomial operator
\[
 \mathcal A(F)(T)=JF(T)-r(T)\,\mathcal I(F)
                   -k(T)\{\mathcal I(TF)-\epsilon[T^5]F\},\qquad
 \mathcal I(F)=JF(1)
\]
in normalized \(T=X/a\), on \(F(0)=0,\deg F\le5\). The functions \(r,k,\epsilon\) are the root-chart scalar formulas explicitly encoded in the constructor. In physical units the nonterminal live taps to ghost \(g\) are
\[
      \ell_g X\bigl[(\mu+\nu c_g)L_6'(X)
                       +\alpha L_5'(X)+\gamma L_7'(X)\bigr],
      \qquad r(T)=T(\alpha L_5'(aT)+\mu L_6'(aT)+\gamma L_7'(aT)),
      \quad k(T)=a\nu T L_6'(aT).
\]
Apply \(\mathcal A\) to each available positive-clock cardinal to give one physical first-five live tap after multiplying by \(a\). The exact replay verifies the null readings of every degree-at-most-five polynomial vanishing at all available live inputs of each row. Thus these cardinals give the specified operator on **all** those scalar polynomials, not just the displayed coordinate vectors.

Write \(N=A^{\mathsf T}\). For nonzero weights and normalized reverse clock \(z=Y/d\), use reverse deweighted taps \(A_{j,i}b_j/(d b_i)\), target \(i\) and source \(j\). Set \(r_v=v/d,\ t_u=u/d,\sigma=1/6,\lambda=3(r_v-1)(r_v-2),k_d=(r_v-1/2)/\lambda\). The first physical reverse actor is the literal terminal, whose column in \(A\) is zero. At \(d_1\) the normalized diagonal is \(1/2\); at \(v\) the \(d_1,v\) taps are \(p_1=r_v^3/[6(r_v-1)]\) and \(p_v=r_v/2-p_1/r_v\). At \(d_2\), the half split gives cubic change \(\delta=-2\sigma\). Set the aggregate tap to the two \(d\)-sources to \(1/2-\delta/(r_v-1)\), the \(v\)-tap to \(\delta/[r_v(r_v-1)]\), and the own diagonal to \(1/2+\sigma/(r_v-1)+k_d\). The \(d_1\)-entry is the aggregate minus the own diagonal.

Let \(\mathbf G\) be the pair vector with \(G_{d_1}=\sigma d^3 b_{d_1}\) and \(G_{d_2}=-G_{d_1}\). Define the nonterminal live barycentric vector \(\mathbf H\) with \(H_{d_1}=0\), aggregate \(\rho/D_{\rm live}'(s)\), and zero at the literal terminal and ghosts. Here
\[
     \rho=d^4 h_v B_vD_{\rm live}'(v),
     \qquad h_v=\frac{r_v^3}{36(r_v-1)}.
\]
The scalar three-node moments give \(-d^4 k_d B_dD_{\rm live}'(d)/6=\rho\), and also the equivalent normalized barycentric amplitude at \(u\). Indeed \(M(s)\) at the roots of \(K\) is the integral of \(P_*K/(Y-s)\), determined by \(n_0,n_1,n_2\) alone. The exact scalar shape gives
\(h/d=r_v(r_v+1)/(r_v-1)^2\) and \(q=9(r_v-1)^2/[4(r_v^2-r_v+1)]\).
Substitute these in those three cofactor integrals, or run the symbolic replay. The same small identities give the actual zero diagonal at \(u\) in the formulas below.

In the \(u\) row and the next five reverse rows (the five ordinary opening clocks), prescribe all incoming entries from physical stages of the known first-five ordinary block. Solve for the three remaining **grouped** scalar taps to \(d,v,u\) using positive input degrees one, two, and three, whose desired normalized primitive values are \(z^2/2,z^3/3,z^4/4+\lambda H_i/(b_i d^4)\). The three unknown taps have a nonsingular positive-degree Vandermonde matrix, since the three numerical labels are distinct and nonzero. Their literal pair splitting is set by
\[
              T_{d_2}=(H_i/(b_i d^4)-\sigma T_d)/\delta,\qquad
              T_{d_1}=T_d-T_{d_2}.
\]
At each reverse live row in this prescription, set the additional literal terminal tap to make its deweighted sum equal the normalized reflected clock. This pays the first reverse primitive. Converting all these weighted taps back to physical coefficients gives the nonterminal live block. At the literal terminal set the four ghost taps so each actual ghost column has \(b\)-weighted sum zero, and restore the entire ordinary origin column by the literal row sums. This sets every coefficient of the 15-row tableau; no stage is projected out or padded.

The construction's nonzero guards, including all individual physical live weights and every field denominator used above, are checked by its exact p17 specialization. The field is irreducible over characteristic zero, so nonzero at that legitimate residue evaluation implies nonzero in the field and at the named real embedding. The rational formulas reduce to **all 225 entries** of the independently checked finite literal, not only to its scalar moments.

## Exact low reverse fields

The constructed reverse primitive errors
\[
    \mathbf E_j=N\mathbf W(Y^{j-1})-\mathbf W(Y^j)/j
\]
satisfy \(\mathbf E_1=\mathbf E_2=0,\ \mathbf E_3=\mathbf G,\ \mathbf E_4=(3d/2)\mathbf G+\lambda\mathbf H\). The first rows \(d_1,v,d_2\) follow by the displayed scalar taps (verified symbolically); the \(u\) and first-five rows follow by their three scalar equations. Likewise \(N\mathbf G=(d/2)\mathbf G+\mathbf H\): at \(v,d_2\) this is the stated normalized amplitude, and later by the pair decomposition. All these assertions are literal on the ghost positions: \(N\mathbf G\) there cancels since the two tap profiles at the pair have the same clock, and \(\mathbf E_j\) for \(2\le j\le5\) has zero ghost projection by exact quadrature of \(Y^{j-1}X L_\ell'(X)\) for \(\ell=5,6,7\). The positive \(Y\) factor kills the actual terminal and permits the Jacobi orthogonality against degree at most three. The first error's ghost coordinates vanish by construction.

At the ordinary origin, not independently assigned from the reverse side, each error \(\mathbf E_j\) has zero total sum: \(A\mathbf1=\mathbf c\) and exact scalar quadrature give equal integrals of \((1-Y)Y^{j-1}\) and \(Y^j/j\). The candidate right sides have zero total sum by their barycentric forms. The literal terminal reads zero on each error. This proves the origin equality. Likewise the sum of \(N\mathbf G-(d/2)\mathbf G\) vanishes by the local zero-sum \(\mathbf G\), proving the remaining origin read of \(\mathbf H\).

For the quartic, put \(S_3(Y)=Y K(Y)\). It vanishes on every early grouped source, so no as-yet unverified reverse tap appears in its read at an opening stage. Let \(\Theta(Y)\) denote the degree-at-most-one remainder of \(-M(Y)JS_3(Y)/Y\) modulo \(K(Y)\). This affine identity is exact, verified with cleared pseudo-division using the true cofactor integral at the three roots. On the early scalar labels, the error in the \(S_3\) primitive has \(\mathbf H\) coefficient \(\Theta(s)/\rho\), plus the single \(\mathbf G\) component fixed at \(d_1\) (then correct at \(d_2\) by the pair aggregate). At each later fixed opening label \(s_i\), require the literal identity
\[
 \sum_{\substack{j\ge i\\ j\ \mathrm{opening}}}
          A_{j,i}\frac{s_j M(s_j)}{P_*'(s_j)}
     = B_{s_i} JS_3(s_i)+\frac{\Theta(s_i)}{D_{\rm live}'(s_i)}.
 \tag{Q}
\]
Here \(B_{s_j}S_3(s_j)=s_j M(s_j)/P_*'(s_j)\), so the left side is exactly the actual reverse read of the quartic. The right side separates the primitive and the centered-head correction. The orientation-free characteristic-zero script checks **all five** identities after clearing denominators. Ghost errors and the literal terminal are zero as before; the origin follows from the total-sum argument. Thus \(\mathbf E_5\in R_5=\langle\mathbf G,\mathbf H,Y\mathbf H\rangle\), since \(S_3\) is monic quartic and all lower primitive errors are already in the flag.

The chosen spaces \(R_3=\langle\mathbf G\rangle,\ R_4=\langle\mathbf G,\mathbf H\rangle,\ R_5\) have exactly the required scalar annihilation degrees \(8,7,6\) by the true pair and nine-label barycentric identities. Clock lifts are immediate. The one remaining transpose closure \(N\mathbf H\in R_5\) is proved next without a new coefficient equation.

## Forward live profile by five-point uniqueness

For any ordinary scalar \(P\) of degree at most six, the difference \(A P(\mathbf c)-JP(\mathbf c)\) is constant on the physical pair: pairing it with \(\mathbf G\) gives zero using \(N\mathbf G=(d/2)\mathbf G+\mathbf H\) and the already proved scalar annihilations. Its nonterminal live values are therefore represented by a polynomial of degree at most eight, vanishing at the ordinary origin. For the actual \((1-X)^\ell\) pairings with \(\ell=1,2,3\), use the reverse primitives through \(\mathbf E_4\) and the \(R_j\) scalar orthogonalities. The weighted pairings are zero by scalar integration by parts. The literal terminal is killed; converting the resulting nonterminal degree-eight profile to the same scalar integrals spends at most degree eleven. **No** degree-eight-profile pairing with \((1-X)^4\) is converted to an integral.

This five-dimensional polynomial space has injective evaluation at the first five nonzero ordinary live clocks. A polynomial in its kernel is \(Q(X)U(1-X)\), where \(Q\) is the monic degree-six hull through the literal origin and those five clocks, and \(\deg U\le2\). The three pairings are the Hankel matrix \((n_{i+j})_{0\le i,j\le2}\), because \(Y Q(1-Y)=P_*(Y)\). Exact quadrature identifies it with the Vandermonde congruence of the three nonzero weights \(B_s P_*(s)\) at \(d,v,u\), so it is invertible even for signed weights.

For scalar input degrees at most five the actual first-five ordinary profiles, including the ghost taps, are known from the constructed cardinals and the rational ghost moments. The full scalar defects through input degree four vanish there, and input degree five has scalar profile a single multiple of \(X L_6'(X)\). Both proposed profiles are in the stated polynomial space, and the evaluation rank forces them globally on nonterminal live stages. For the degree-six nodal input \(Q\), the corresponding proposed profile is
\[
        \Lambda (X-(1-u))Q(X)-JQ(X)
          +\text{the polynomial ghost-feed contribution},\qquad
        \Lambda=\frac{3-2q}{6(q-1)}.
\]
It has degree at most seven. It matches the first-five actual reads because the live-only numerical input \(Q\) is zero throughout that prefix. The three required primitive pairings follow from the certified identities
\(\Lambda(u n_k-n_{k+1})=n_{k+1}/(k+2)\); the ghost contribution has the Jacobi orthogonality. This identifies the actual degree-six primitive throughout the nonterminal live rows. Consequently \(A P\) has polynomial degree at most seven there for every scalar \(P\) of degree at most six.

It follows that \(N\mathbf H\) annihilates scalar degree six, because \(A P\) has degree at most seven on the support of \(\mathbf H\). It is also zero on the ghosts (their tap modes have degree at most seven) and literal terminal. On the ten nonterminal live coordinates, the annihilator of scalar \(P_6\) is exactly the three-dimensional \(R_5\) by distinct-label rank, and the pair and barycentric vectors give all three independent directions. Hence the last reverse closure holds.

## Finish all rooted conditions

The forward low spaces are \(G_k=\mathbf hP_{k-3}(\mathbf c)\) for \(k=3,4,5\), supported on the four ghosts. On them, the exact rational block and its moment/adjoint identities give the needed primitive and \(A\)-lift conditions: the cubic defines \(\mathbf h\); the quadratic pair of annihilators \(\ell,p\ell\) cuts out \(\mathbf hP_1\); the single \(\ell\) cut gives \(\mathbf hP_2\). These claims follow by substituting the two literal adjoint formulas on the rational block, which annihilate precisely the needed scalar primitive differences and the lifts \(A\mathbf h,A C\mathbf h\). On nonterminal live rows, the scalar defects through input degree four vanish by the preceding rank proof. The indicated two low lifts vanish there by the literal two tap modes and \(\sum\ell_g h_g p_g^j=0\) for \(j=0,1,2\). The literal terminal values of those low defects/lifts are also zero: their weighted outputs vanish by the established \(N\mathbf b=\mathbf W(Y)\) and scalar quadrature, and the other live entries have just been shown zero.

The two grade-six bridge images, the quintic scalar primitive defect and \(AG_5\), have nonterminal live profiles proportional to \(X L_6'(X)\). For the latter this is the literal ghost tap formula and the same three \(\ell\)-moments, with at most one surviving \(k(T)\) coefficient. Their output is zero by \(N\mathbf b=\mathbf W(Y)\). Thus they annihilate the required \(\mathbf W(P_5)\) and \(R_5\) by the stated bridge lemma. All hypotheses of [the complementary-support rooted proof](SUFFICIENCY.md) hold. This proves order at least twelve for the exact algebraic tableau.

Finally the exact integer-scaled order-thirteen bush reduces to \(11+7z+12z^2\ne0\) in the selected \(\mathbb F_{17^3}\) field; it is therefore nonzero in characteristic zero and in the chosen real embedding. The method has **exact order twelve**.

## Replay

    python3 -B verify-early.py      # exact symbolic early scalar algebra (SymPy)
    python3 -B verify-char0.py      # exact F36/f3 reductions (python-flint)
    python3 -B replay-mod17.py      # independent standard-library literal and units

The final two commands use the previously frozen field and selected literal data from their sibling directories; their paths can also be passed explicitly. The first-root isolation is independently reproducible in the field receipt.
