# Endpoint zeros and individual fixed-moment rank on the neighboring chart

**Scope.** In the fixed neighboring singleton topology of the [full corrected moment rank theorem](ERK11-NONZERO-TEN-TWELVE-NEIGHBOR-FULL-MOMENT-RANK.md), keep \(K_0\ne0\), the true centered widths \(s=c_8=c_9\notin\{0,1,a,d\}\), and actual \(z=c_{10}\ne d,s\). The result concerns the **actual** common profile \(P,Q\), not arbitrary vectors in a symbolic kernel. The two physical endpoint reads of \(Q\) cannot both vanish, either zero is simple, and each individual three-column fixed block has rank at least two. Thus any fixed determinant loss is exactly rank two. No rank-two fixed loss or unrestricted stage bound is claimed excluded by this note.

## Actual grade-five endpoint reads

Let \(T=Q(C)\mathbf1-P(C)F-Q(\theta)s_{\rm carrier}\) be the true grade-four lifted vector. The carrier vector here is separate from the scalar clock \(s\). The same \(T\) is obtained from the reversed profile by using \(F^\star=\kappa F\) and \(P/\kappa\), with numerical rows still physically numbered. Thus it has the physical values \(Q(0)\) and \(Q(1)\) at the endpoints, zero at the carriers and active singletons, and \(Q(s)\ne0\) at dormant 9. The last guard uses the active singleton sharing \(s\), not positivity.

If \(Q(0)=0\), literal \((C-a)T\) is zero through the first six rows: the centered factor kills the left pair, the calibrated singletons and carrier already give zero, and the first endpoint is zero. It is the anchored grade-five lift of \((X-a)Q\), and among mixed rows \(7,\ldots,11\) it has support exactly at 9, with live read \((s-a)Q(s)\). The reflected statement for \(Q(1)=0\) uses \((C-d)T\), the reversed first six rows, and read \((s-d)Q(s)\). All pairings below use total grade at most ten; no ordinary reverse order eleven is needed.

Consequently the following are actual identities of **model polynomials**, up to live scalar:
\[
 Q(0)=0 \Longrightarrow (X-a)Q(X)\propto k_L(X):=[\ell_X,R_9],
 \qquad
 Q(1)=0 \Longrightarrow (X-d)Q(X)\propto k_R(X):=[L_9,r_X^{\rm ev}] .
\]
Indeed, pair the corresponding lifted vector against every opposite anchored model. The numerical sum is its single support read times \(b_9\) times that opposite row-9 functional. The anchored Gram is nonsingular, giving exactly its primal representative. Thus the endpoint zeros respectively force \([\ell_a,R_9]=0\) and \([L_9,r_d^{\rm ev}]=0\).

The left endpoint zero must be simple: \(k_L'(0)=[D_L^0,R_9]\ne0\) by the original first-slope proof, while \(((X-a)Q)'(0)=-aQ'(0)\). On the right, suppose \(Q(1)=Q'(1)=0\). Then \(k_R'(1)=0\); the true \([L_9,R_{11}]=0\) with its two live extra-clock products forces also \(k_R'(d)=0\). Along with its two zero values this gives \(k_R=(\lambda+\eta X)V\), \(V=(1-X)^2(X-d)^2\). The actual forward width row has \(L_9(W)=W(s)\) and \(L_9(XW)=sW(s)\) for \(W=X^2(X-a)^2\), since \(W(a)=0\). Pairing with \(k_R\) therefore gives
\[
 0=\int (X-s)W k_R
   =(I_1-sI_0)\bigl(\lambda+\eta z\bigr),
 \qquad z=\frac{I_2-sI_1}{I_1-sI_0}.
\]
The live first factor proves \(k_R(z)=0\). Since \(z\ne d\), this gives \(Q(z)=0\) at the true active singleton \(z\), impossible. This proves right simplicity without assuming the actual rotated first slope live outside the endpoint-zero branch.

## The double endpoint zero would lose the whole moment rank

Use \(\omega=X(1-X)(X-a)(X-d)\), \(\rho=b_9\omega(s)=J_0/(uv)\). The three already paid rows give \(\int X^j\omega Q=\rho s^jQ(s)\) for \(0\le j\le2\). If \(Q=X(1-X)r\), then \(\deg r\le2\) and \(r\ne0\). Pair the forward centered vector of the previous section with the anchored right polynomial \((1-X)(X-d)\), whose row-9 read is \((1-s)(s-d)\) because the \(d\)-direction vanishes. Pair its reflected counterpart with the anchored left polynomial \(X(X-a)\), whose read is \(s(s-a)\). These two exact products yield
\[
 \int\omega(1-X)r=\rho(1-s)r(s),\qquad
 \int\omega Xr=\rho s r(s).
\]
Together the five tested multipliers \(1-X,\ X,\ X(1-X),\ X^2(1-X),\ X^3(1-X)\) span all polynomials of degree at most four. Thus \(r\) gives a nonzero row dependence of the full corrected moment operator, contrary to its earned rank three. This closes the simultaneous actual endpoint-zero mask with no new resultant.

More generally, if the left endpoint is zero \(Q=Xr\), the same single forward mixed test and the three corrected moments show that \(r\) is in the corrected moment kernel (indeed its rows through degree three vanish). Simplicity gives \(r(0)\ne0\). Reflect for a sole right zero. At either origin the full two-dimensional corrected moment kernel therefore contains a polynomial not vanishing there: use \(Q\) itself if its endpoint is live, or the divided \(r\) otherwise. The three fixed columns \(\phi,YB_0,YB_1\) are independent and all vanish at \(Y=0\). Their intersection with the full moment kernel has dimension at most one. Hence each fixed three-column block has rank at least two, even at a true fixed determinant zero.

## Exact profile inverse, and the temporal law in endpoint coordinates

In an orientation \(Y\), with live width \(w\), half \(h=w/2\), and both actual derivative slopes \(\ell_0,\ell_1\), put \(L(Y)=w\ell_0-(\ell_0-\ell_1)Y\). The five-column coordinates have the equivalent form
\[
 Q=U_f\phi+(Y-h)\bigl[(W_fY+A_f)Y(Y-w)+(T_fY+B_f)L(Y)\bigr],
 \quad B_f=tA_f .
\]
They are recovered directly from \(Q\), without a moment or temporal division: use \(U_f=Q(h)/\phi(h)\), put \(G=(Q-U_f\phi)/(Y-h)\), then
\[
 B_f=G(0)/(w\ell_0),\qquad
 T_f=(G(w)/(w\ell_1)-B_f)/w,
\]
and \(W_fY+A_f=(G-(T_fY+B_f)L)/(Y(Y-w))\). The polynomial divisions are exact. \(B_f\ne0\) iff the endpoint is live, in which case \(t=B_f/A_f\) and the sparse \(P=w[U_f+(T_f/t-W_f)(Y-h)]\) are measured. At a single zero endpoint, use the measured representer \(Q\) and the live opposite endpoint to obtain its \(P\), then calibrate the relative \(P,Q\) scale at the first orientation's own active half. Its \(T_f\ne0\) by the simple root (\(Q'(0)=T_f B_1(0)\)), so its product is then recovered by \(t=T_f/(P_1/w+W_f)\). Both products and the physical \(P,Q\) shape are width-measured on every actual sole-endpoint branch.

The original temporal equation is also a rank-free law in the endpoint values of \(Q\). Use the previously defined adjusted cubic \(E\), with \(E_0=E(0)\), and write the temporal row as
\[
 O(Y)=wY(Y-w)E_0U_f+(YW_f+A_f)S_0(Y)+(YT_f+B_f)S_1(Y).
\]
Direct substitution of \(S_0,S_1\) gives the polynomial identity
\[
 Y\ell_1 O(Y)=E(Y)\big[(w-Y)\ell_1Q(0)-Y\ell_0Q(w)\big]
              -w\ell_1 E_0Q(Y).
\]
This follows from \(B_1(0)(YT_f+B_f)=(1-Y/w)Q(0)-(Y/w)(\ell_0/\ell_1)Q(w)\). The numerator on the right is exactly divisible by \(Y\); the quotient equals \(\ell_1 O(Y)\) **even at a measured clock zero**. Thus no clock factor is dropped by using the simplified temporal test. This can impose the opposite actual temporal equation on the reconstructed single-endpoint profile, rather than dividing by an unavailable sparse moment or affine pivot.

Finally, if both raw affine coefficients of an orientation vanish and its full temporal-plus-moment matrix nonetheless has rank four, the two cofactors at \(A_f,B_f\) vanish, so its real endpoint is zero. The double-zero exclusion rules out this outcome in both orientations at once. The cases where a temporal row adds no full rank are separate.
