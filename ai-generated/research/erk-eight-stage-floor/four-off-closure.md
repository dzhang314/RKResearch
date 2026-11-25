# Source proof: the actual ordered ERK8 four-off Fin 10 branch is impossible

**Conclusion.** On a literal strict-lower Fin 10 tableau with reviewed HasOrder 8 over an ordered field, four distinct defective clocks are impossible. This proof uses the public-only physical localization and cyclic/clean reduction already recorded in the two companion source notes. It closes both first-clean positions without paying the missing cubic reverse row. This is a mathematical source proof and an exact finite scalar certificate, not a Lean replay or the separate one-off branch.

## 1. Physical and polynomial data

Use \(c=\mathrm{nodes}\,A\), \(g=\mathrm{OneOff.g}\,A=A c-c^2/2\), and suppose there are four off tags. The native midpoint horizon and the checked census give five clean clocks, ranks \(F_3=2,F_4=3,E_4=8,E_5=9\), and the unique terminal clean coordinate \(e_9\in E_4\) at clock 1. The physical localization gives four distinct off clocks in rows 1–5, the first nonzero clean \(h\) at row 4 or 5, later clean \(x=c_6,z=c_7\), and a duplicate tag at row 8. Let \(a,b,d,e\) be the four off clocks in **first physical occurrence order**. Thus \(h=4\) as an index means \(h\) precedes the fourth off \(e\), and \(h=5\) as an index means it follows all four. The labels \(h,x,z\) in formulas always mean clock values.

The clean hull is \((X-1)Q\), where
\[
  Q=X L_3=X(X-h)(X-x)(X-z),\qquad
  L_3=(X-\tfrac12)(X^2-X+\tfrac17).
\]
Off tags have \(g=P(c)\ne0\), with \(\deg P\le2\). Write \(I\) for the zero-constant polynomial primitive. The actual clean chronological equations from the companion derivation give
\[
 \begin{split}
 E&=h/4-(x+z)/3+xz/(2h),\\
 P&=\Theta(X-x)(X-z)+
       \kappa\bigl(5X^2-(4x+3h)X+2hx\bigr),\\
 \Theta\,E&=\kappa(x/3-h/4),\qquad \kappa\ne0.
 \end{split}                                                   \tag{1}
\]
Recall why this shape is physical. The clean-to-clean tap sum integrates \(P,XP\) exactly, because the off inputs are \(g,cg\) and their \(A\)-images vanish at clean rows. The clean grade-five defect line is spanned by \(I Q\), forced by the terminal profile of \(e_9\) and \(A e_9=0\). With \(S=X(X-h)P\), the actual clean tap sum of \(S\) is \(I S-\Theta I Q\). Before \(h\) and \(x\) the only earlier clean clocks are 0 and possibly \(h\), the zeros of \(S\). Thus this integrated polynomial has double zeros at \(0,h\) and a zero at \(x\), and is a multiple of \(X^2(X-h)^2(X-x)\). Differentiating gives (1). The first-clean test \(I(XP)(h)=0\) gives its scalar ratio; a zero \(\kappa\) then forces \(P=0\) by \(E\ne0\). The finite symbolic table below checks \(E\ne0\), \(P(0),P(h),P(x),P(z)\ne0\), and \(p_2=[X^2]P\ne0\) for the normalized shape \(\kappa=1\); all nonvanishings therefore hold for the actual shape.

Since the actual terminal column belongs to \(E_4\), its clean polynomial has to be \(Q\) up to scale. Normalizing gives a polynomial \(R\) of degree at most two with
\[
   Q(c)+gR(c)=Q(1)e_9 .
\]
Consequently, for the monic off hull \(D=(X-a)(X-b)(X-d)(X-e)\),
\[
                  Q+P R = \sigma D,\qquad \sigma\ne0.          \tag{2}
\]
The polynomial on the left vanishes at the four distinct off clocks and has degree at most four. It cannot be identically zero: then \(P\) would divide \(Q\), whereas \(P\) has positive degree and is nonzero at all four distinct roots of \(Q\).

## 2. Transfer of actual off coefficients to the fixed clean grid

Write \(N_j\) for the monic hull of the first \(j\) off clocks. Define exact top divided differences
\[
 L_{j,r}=\sum_{o:N_j(o)=0}\frac{o^r}{P(o)N_j'(o)},\qquad
 C_r=\sum_{u\in\{0,h,x,z\}}\frac{u^r}{P(u)Q'(u)} .
\]
These are the coefficients of degree \(j-1\), respectively 3, in the corresponding Lagrange polynomial for \(X^r/P\). Formula (2) gives
\[
       L_{4,r}=\sigma C_r\quad(0\le r\le4),\qquad
       L_{3,r}=\sigma(C_{r+1}-eC_r)\quad(0\le r\le3).            \tag{3}
\]
Here is a certificate-friendly polynomial proof of the first identity, without roots of \(P\) or a division by any off moment. Let \(U_D,U_Q\) be the degree-\(\le3\) interpolation representatives for \(X^r/P\) on \(D,Q\). Write \(P U_D-X^r=D V_D\), \(P U_Q-X^r=Q V_Q\), where both \(V\)'s have degree at most one. Reducing modulo \(P\) and using \(Q\equiv\sigma D\) gives \(D(V_D-\sigma V_Q)\equiv0\). Since \(D\) is split and \(P\) is nonzero at its roots, they are coprime. Hence \(V_D=\sigma V_Q\) by their degrees. Compare degree five in the two identities; the leading coefficients are \(p_2 [X^3]U_D\) and \(p_2 [X^3]U_Q\). This proves the first assertion. The second follows directly by multiplying each summand for \(D\) by \(o-e\), which cancels the extra factor in \(D'(o)\) and suppresses the term \(e\).

Use the normalized off-only Newton operator from the companion note, \((\mathcal T f)(o)=(A(gf(c)))_{\mathrm{first}(o)}/P(o)\). Its first three columns are \(N_0\mapsto\beta N_1,\ N_1\mapsto\gamma N_2,\ N_2\mapsto\delta N_3\), and \(\mathcal T N_3=0\). The degree caps on its first two images are the actual \(Ag,A(cg)\) bands; the zeros of every image are provided by the physical prefix. Thus for *any* interpolated input \(f\), the cubic coefficient of \(\mathcal T f\) is \(\delta\) times its Newton coefficient of \(N_2\). This fact uses the full four-sender module.

For \(r=2,3,4\), apply that fact to the actual pure input \(c^{r-1}\). Its off component is \(g X^{r-1}/P\). In the four first-occurrence off rows the only possible nonzero clean contribution is a tap from \(h\) into the fourth off \(e\), and this exists only in the first-clean-index-4 branch. That contribution at \(e\), normalized by \(P(e)\), has cubic coefficient \(A_{\mathrm{first}(e),\mathrm{first}(h)}h^{r-1}/(P(e)N_3(e))\), because it vanishes at the preceding three off clocks. On the output side, the actual normalized primitive residuals for \(g,mDef_2,mDef_3\) have degrees zero, at most one, and at most two on off clocks. These corrections contribute **no cubic coefficient**. Taking the cubic coefficient and using (3) gives the single unified exact system
\[
       \delta(C_r-e C_{r-1})+T h^{r-1}=C_r/r
            \quad(r=2,3,4),                                  \tag{4}
\]
where \(T=0\) for first-clean index 5, and \(T=A_{\mathrm{first}(e),\mathrm{first}(h)}/(\sigma P(e)N_3(e))\) otherwise. All denominators here are nonzero by distinct off clocks, actual \(P(e)\ne0\), and (2). There is no assumption that \(\delta\) is nonzero. This is exactly where the relaxed tableau from the previous note lacks the two early pure primitive bands.

## 3. First clean at physical index 4

The actual clean row \(h\) has only the first three off senders, and earlier clean clock zero. Its linear functional on their normalized off values kills 1 and \(X\) by \(Ag=A(cg)=0\), so it is \(v_h\) times their top divided difference, where \(v_h=(A(c^2g))_h\). Testing \(c^{r-1}\) gives \(v_h L_{3,r-1}=h^r/r\) for \(r=2,3,4\), from the actual clean primitive tests. By (3),
\[
           v_h\sigma(C_r-e C_{r-1})=h^r/r .
\]
The \(r=2\) equation implies \(v_h\sigma\ne0\). Substitute into (4) and multiply by \(r\): \(C_r/h^{r-1}\) is affine in \(r\) at \(2,3,4\). Hence
\[
                  C_4-2h C_3+h^2 C_2=0.                       \tag{5}
\]
In its clean divided difference only \(x,z\) contribute. By (1), \(P(x)=\kappa x(x-h)\) and \(P(z)=\kappa[z(z-h)+(4z-2h)(z-x)]\). With \(Q'(x)=x(x-h)(x-z)\), \(Q'(z)=z(z-h)(z-x)\), this gives the exact formula
\[
 C_4-2h C_3+h^2 C_2
 =\frac{z(z-h)/P(z)-1/\kappa}{z-x}
 =-\frac{4z-2h}{P(z)} .
\]
Thus \(2z=h\), impossible for distinct Lobatto interior clocks. Indeed if \(z\ge1/2\) then \(2z\ge1>h\); otherwise \(z\) is the smaller quadratic root, and \(h=1/2\) would require \(z=1/4\), while \(h=1-z\) would require \(z=1/3\). Neither solves \(X^2-X+1/7=0\). No ordered positivity of the tableau weights was imposed.

## 4. First clean at physical index 5

Here \(T=0\). Put \(U=\delta,V=-e\delta\) in (4): the three linear equations are \(U C_r+V C_{r-1}=C_r/r\), \(r=2,3,4\). Their augmented \(3\times3\) determinant must vanish. Multiplication of the determinant by 12 gives
\[
 C_1 C_3 C_4-3 C_2^2 C_4+2 C_2 C_3^2
 = (C_1 C_3-C_2^2)\bigl(C_4-2(p_0/p_2)C_2\bigr).             \tag{6}
\]
For the factorization, \(p_0 C_j+p_1 C_{j+1}+p_2 C_{j+2}=0\) for \(j=1,2\), since the sum after multiplication by \(P\) is the top divided difference of \(X^j\) on four nodes. Thus \(C_2 C_4-C_3^2=(p_0/p_2)(C_1 C_3-C_2^2)\).

The first factor \(\Delta=C_1C_3-C_2^2\) is nonzero also without a clean-case table. The same interpolation proof as (3) gives \(C_r=-[X](Q^{-1}X^r\bmod P)/p_2\) for these \(r\). On the two-dimensional algebra \(K[X]/P\), the pairing extracting the linear coefficient after multiplication by the unit \(XQ^{-1}\) is nondegenerate: for a nonzero representative of degree at most one after that multiplication, multiply by 1 if it has a nonzero linear term and by \(X\) if it is a nonzero constant. The matrix of the pairing on \(1,X\), up to the nonzero scale \(-1/p_2\), has entries \(C_1,C_2,C_3\), so \(\Delta\ne0\).

For completeness, both factors have short exact clean-case expressions. Scale to \(\kappa=1\), put \(\omega^2=3/7\), and write \(L=(1-\omega)/2,\ C=1/2,\ R=(1+\omega)/2\). The three missing permutations below are the displayed ones with \(\omega\) replaced by \(-\omega\). The columns use (1) and the literal clean residue formula, with no off clocks:
\[
\begin{array}{c|c|c|c}
(h,x,z)&p_2&\Delta&C_4-2(p_0/p_2)C_2\\ \hline
LCR&9/2+\omega&2744(77-24\omega)/645&-63(5+3\omega)/185\\
LRC&3+7\omega/2&1372(\omega-1)/3&126(7-9\omega)/25\\
CLR&(48+28\omega)/11&21952(103-80\omega)/4029&126(-14+15\omega)/697
\end{array}
\]
Each displayed element is nonzero, as is its conjugate, by squaring a hypothetical rational value of \(\omega\) and comparing with \(3/7\). Returning to general \(\kappa\ne0\) multiplies \(p_2\) by \(\kappa\), \(\Delta\) by \(\kappa^{-2}\), and the last column by \(\kappa^{-1}\). Thus (6) is impossible. The attached tiny certificate expands exactly these three identities and their conjugates using rational pairs. It does not enumerate off nodes, tableau values or spatial orders of the off nodes.

## Native realization checklist

The final declaration should take literal strict triangularity and reviewed HasOrder 8 on Fin 10, and conclude that the card of OneOff.offKnots is not four. No independent assumed row-model field belongs in its signature.

1. Use the actual census/Horizon, typed tag interpolation, literal localization, and the prior clean shape derivation (source notes), keeping clean and off tags separate at coincident clocks.
2. Build the Newton quotient from the four **chronologically first** off rows; its shifted-degree coefficients come from actual \(F_3,F_4\), not a claimed stage merge. Use the actual \(mDef_2,mDef_3\) columns in those bands at the cubic comparison.
3. Implement (3) by Lagrange interpolation and the degree-\(\le1\) remainders of the two exact polynomial divisions; no extension field is needed. Alternatively supply its equivalent finite coefficient equality. Equation (4) uses only three literal normalized equations at the fourth off row plus the lower Newton shape, and is safe even when \(\delta=0\).
4. In index 4, use the three actual clean primitive rows to eliminate the one physical tap. In index 5, use the determinant polynomial identity and the six fixed clean chronologies. The scalar table can be proved by closed field identities modulo \(\omega^2=3/7\), or by the conceptual nondegenerate pairing for \(\Delta\) and the shorter last-column certificate.
5. The companion one-off contradiction is separate. Only after that branch and the native census and audits are checked can the Fin 10 exclusion be lifted by StagePadding to a stage floor of 11.

Every new mathematical step here is source-only and from the published stream or the stated exact algebra. No held order-eight artifacts, no numerical grids, no network or Lean, and no checkout edits were used.
