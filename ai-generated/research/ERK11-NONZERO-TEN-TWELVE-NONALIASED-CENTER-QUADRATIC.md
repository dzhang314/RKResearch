# A quadratic reciprocal gate for the remaining dormant center

**Scope.** Continue the [full-pair central chronology](ERK11-NONZERO-TEN-TWELVE-CENTRAL-FOUR-ALIASES-CLOSED.md): seventeen ERK11 stages, all live, half-clock with carriers at physical 2 and 16, both seventh boundaries new, \(q=10,n=12\), full plateau pairs, sole dormant physical 9. Let \(s=c_9\) be outside the four excluded clocks \(0,1,a,d\). The necessary quadratic below is valid even if \(s\) equals some active singleton. Recovering the outer clocks by the displayed fractions has separate centroid exceptions. The two exact interval exclusions apply at the indicated widths only. No unrestricted stage interval changes.

## 1. Direct mixed rows and the true chronology poles

Write \(x=c_8,\ z=c_{10},\ W=X^2(X-a)^2,\ V=(1-X)^2(X-d)^2\), with primitive models \(\mathscr P=JW,\mathscr Q=\bar J V\) where \(J,\bar J\) denote polynomial integration from the left and right endpoints. Let \(p=AV_L\), \(r=A^\star V_R\) be their actual numerical grade-five primitives. In the rest of this note let \(J_0=\int\mathscr P\mathscr Q=C_1-C_2\) denote the scalar mixed primitive pairing, to distinguish it from the integration operator. Keep the actual mixed moments \(H,C_1,C_2,I_0,I_1,I_2\) of the [two-pair chart](ERK11-NONZERO-TEN-TWELVE-ACTIVE-TWO-PAIR-GATES.md#3-topologies-and-actual-mixed-middle-restrictions).

Put
\[
 A_s=s(s-a),\qquad B_s=(1-s)(s-d),\qquad
 u=p_9/A_s,\qquad v=r_9/B_s .
\]
Both \(A_s,B_s\) are live by the four-clock guard. Dormancy gives \(V_L(9)=A_s^2,\ V_R(9)=B_s^2\). The literal supports \(pV_R\subseteq\{9,10\}\), \(V_Lr\subseteq\{8,9\}\), \(V_LV_R\subseteq\{8,9,10\}\) and \(pr\subseteq\{9\}\) give
\[
\begin{split}
 C_1-zH&=(s-z)b_9 p_9 B_s^2,\\
 C_2-xH&=(s-x)b_9 A_s^2 r_9,\\
 I_2-(x+z)I_1+xzI_0&=(s-x)(s-z)b_9 A_s^2 B_s^2,\\
 J_0&=b_9p_9r_9 .
\end{split}
\]
The shifted grade totals are at most ten; nothing is divided by \(s-x\) or \(s-z\) here. Thus \(u,v\ne0\) when the inherited \(J_0\) is live, and
\[
 u(C_2-Hx)=J_0 A_s(s-x),\qquad
 v(C_1-Hz)=J_0 B_s(s-z).
\]
Set \(K_L=J_0A_s,\ K_R=J_0B_s,\ P_L=K_L-Hu,\ P_R=K_R-Hv\) and \(\delta_1=C_1-Hs,\ \delta_2=C_2-Hs\). Then
\[
 P_L(x-s)=-u\delta_2,\qquad P_R(z-s)=-v\delta_1.
\]
Away from \(\delta_1\delta_2=0\) both pivots are live, \(s\ne x,z\) automatically, and these give a Möbius recovery of the two actual outer clocks. If \(\delta_2=0\), the shifted \(V_Lr\) moment requires \(s=x\) **or** the actual reverse primitive read \(r_8=0\); if \(s\ne x\) this is exactly the left Möbius pole \(P_L=0\). Indeed \(\delta_2=(x-s)b_8 V_L(8)r_8\) and \(V_L(8)\ne0\) since \(p_9=A_{98}V_L(8)\ne0\). If \(\delta_1=0\) the corresponding fork is \(s=z\) or \(p_{10}=0\), using \(V_R(10)\ne0\). The two centroid exceptions cannot occur simultaneously because \(\delta_1-\delta_2=J_0\ne0\). At a clock collision the corresponding zero-over-zero fraction is not used.

## 2. Two bilinear rows; the temporal cross is not a third independent cut

On the anchored degree-five evaluation spaces use the actual mixed inverse-Gram bracket \([L,R]\). Write \(\ell_y,r_y^{\rm ev}\) for point evaluation rows. The normalized central rows are
\[
\begin{split}
 L_* &= \frac{\ell_s-\mathscr P(s)\ell_a/\mathscr P(a)}{A_s}
          +u\,\frac{\ell_a}{\mathscr P(a)},\\
 R_* &= \frac{r_s^{\rm ev}-\mathscr Q(s)r_d^{\rm ev}/\mathscr Q(d)}{B_s}
          +v\,\frac{r_d^{\rm ev}}{\mathscr Q(d)} .
\end{split}
\]
The two first numerators are polynomially divisible by \(X(X-a)\) and \((1-X)(X-d)\) in their clock argument: they vanish at the actual origin anchor and the adjusted plateau. Thus their quotients are cubic row polynomials in \(s\). The only width divisions here are the live \(\mathscr P(a)=a^5/30,\mathscr Q(d)=(1-d)^5/30\). The true \(9,9\) reciprocal diagonal and \(J_0=b_9 p_9 r_9\) give the first bilinear equation
\[
 \mathcal A=[L_*,R_*]-uv/J_0=0 .
\]

A separate necessary temporal statement is \(\mathcal B=[\Phi_L,\Phi_R]=0\), where \(\Phi_L=\lambda_1D_L^0-\lambda_0D_L^a\), with \(\lambda_i\) the two derivative pairings against \(R_*\); define \(\Phi_R\) by the two pairings of \(L_*\) with \(D_R^1,D_R^d\) similarly. These are directions of the actual \(L_7,R_{11}\) if their first slopes are live. To see necessity without any nonzero slope condition, multiply the actual row formula for \(L_7\) by \(\lambda_0\), and use \([L_7,R_*]=0\): it becomes a live scalar times \(\Phi_L\), since the product of the two genuine extra clocks is nonzero. The same holds for the right formula. Then \([L_7,R_{11}]=0\) gives \(\mathcal B=0\), even when one recovered direction is the zero row.

There is a simpler second bilinear equation \(\mathcal C=0\) from the direct mixed moments. Put \(M_s=I_1-sI_0,\ T_s=I_2-2s I_1+s^2 I_0\). The coefficient row in \((1,u,v,uv)\) is
\[
 \begin{pmatrix}
 K_LK_R(J_0T_s-\delta_1\delta_2),&
 J_0K_R(-HT_s+\delta_2M_s),&
 J_0K_L(-HT_s+\delta_1M_s),&
 J_0\bigl(H^2I_2-H(C_1+C_2)I_1+I_0C_1C_2\bigr)
 \end{pmatrix}.
\]
In fact the four shifted support formulas give
\[
 (C_1-zH)(C_2-xH)
   =J_0\bigl(I_2-(x+z)I_1+xzI_0\bigr).
\]
Multiply by \(P_LP_R\), substitute \(P_L(x-s)=-u\delta_2,\ P_R(z-s)=-v\delta_1\), and expand about \(s\) to obtain \(\mathcal C=0\). This is a polynomial implication even at the centroid poles. The \(\mathcal A,\mathcal B,\mathcal C\) coefficient degrees in \(s\) are at most \((6,3,3,0)\); in \(\mathcal C\) the quadratic terms in \(-HT_s+\delta_i M_s\) cancel, and the \(uv\) coefficient is constant in \(s\).

The three rows are **not three independent cuts**. Here is the exact dependency. In the primal left anchored space the annihilator of the two derivative rows has basis \((W,XW,\mathscr P)\). All three have zero derivative at 0 and \(a\); their independence follows by evaluating at \(a\), where \(\mathscr P(a)\ne0\) and \(W=XW=0\). The right basis is \((V,XV,\mathscr Q)\) by the corresponding argument. In these bases the restricted pairing matrix is
\[
 G_3=\begin{pmatrix}I_0&I_1&H\\ I_1&I_2&C_2\\ H&C_1&J_0\end{pmatrix}.
\]
Extend both bases by two dual-to-derivative complement polynomials, with the two complements first. Let \(G_5\) be the full primal Gram in the extended bases and \(K\) the \(2\times 2\) derivative dual block, i.e. the top-left block in \(G_5^{-\mathsf T}\). The full matrix \(G_5\) is nondegenerate by the anchored Gram. Jacobi's complementary minor gives \(\det K\det G_5=\det G_3\). If \(\widehat l=(A_s,s A_s,u)^\mathsf T,\widehat r=(B_s,s B_s,v)^\mathsf T\) denote the restrictions of the normalized rows, the bordered Schur identity is
\[
 \det G_5\left(\det K[L_*,R_*]-\mathcal B\right)
       =\widehat r^{\mathsf T}\operatorname{adj}(G_3)\widehat l .
\]
Indeed \(\mathcal B\) is the product of the two cross columns against \(\operatorname{adj} K\). For \(G_3\) invertible, subtracting this border contribution projects the dual pairing to \(G_3^{-\mathsf T}\). The identity also holds when \(G_3\) is singular, by perturbing \(G_3\) over a rational function field, clearing denominators, and taking the original value; \(\det G_5\) stays live. Expanding the three-by-three adjugate gives
\[
 \mathcal C
   =J_0^2\bigl(\widehat r^{\mathsf T}\operatorname{adj}(G_3)\widehat l
                  -(\det G_3) uv/J_0\bigr)
   =J_0^2\det G_5\bigl(\det K\,\mathcal A-\mathcal B\bigr).
\]
Thus \(\mathcal A,\mathcal C\) suffice for this subsystem, even on \(\det G_3=0\). In particular a rank-three cofactor projection in \(1,u,v,uv\) would be identically zero.

## 3. The low-dimensional quadratic and exact ordered exclusions

Write the rows \(\mathcal A,\mathcal C\) as \((a_0,a_1,a_2,a_3)\) and \((c_0,c_1,c_2,c_3)\). Every actual candidate satisfies the division-free elimination
\[
 E(u)=(a_0+a_1u)(c_2+c_3u)-(c_0+c_1u)(a_2+a_3u)=0.
\]
Its coefficients \((E_0,E_1,E_2)\) have respective \(s\)-degrees at most \((9,6,3)\). For fixed \(a,d,s\), if \(E\) is nonzero there are at most two possible values of \(u\) even over a field extension. When either coefficient of \(v\), \(a_2+a_3u\) or \(c_2+c_3u\), is live, that row determines \(v\). If both vanish, their two constant terms must also vanish, or the branch is impossible. If all coefficients of \(E\) vanish, there is no finite-\(u\) conclusion from this subsystem. These affine-row exceptions are distinct from the clock-recovery poles in §1.

At the exact ordered width pair
\[
 a=\tfrac15,\qquad d=\tfrac25
\]
the exact coefficient degrees are \(9,6,3\), with joint gcd 1 in \(s\). Let \(\Delta=E_1^2-4E_0E_2\). It has degree 12. For each closed interval
\[
 [133/200,67/100]\qquad\text{and}\qquad[7/10,3/4]
\]
the replay checks that all thirteen coefficients of
\[
 (1+t)^{12}\Delta\!\left(\frac{l+r t}{1+t}\right)
\]
are strictly negative, where \(l,r\) are its endpoints, and checks the right endpoint separately. This proves \(\Delta<0\) throughout both intervals over any ordered field at these widths. A root \(u\) would give \(\Delta=(2E_2u+E_1)^2\ge0\), contradiction. No centroid, singleton separation or supplementary slope guard is required for this quadratic sign test. It gives no numerical assertion at other width pairs.

## 4. The surviving second-pool moments are a single rank-one update

Write \(\omega(X)=X(1-X)(X-a)(X-d)\). The actual grade-four two-pool vector \(T\) has model \(Q\); it vanishes on all active singletons and the carriers. Outside them it is supported on the endpoints, two full pairs and the dormant row. Multiplying by \(C^j\omega(C)\), for \(0\le j\le2\), removes all but the dormant row and is still paid, of grade \(8+j\). Even if another active stage shares \(s\), its \(T\)-read is already zero. Thus
\[
 \int X^j\omega(X)Q(X)=b_9 s^j\omega(s)Q(s).
\]
Since \(J_0=b_9 A_sB_suv\) and \(\omega(s)=A_sB_s\), this is precisely
\[
 \boxed{uv\int X^j\omega(X)Q(X)=J_0s^jQ(s),\qquad j=0,1,2.}
\]
It holds whether or not \(Q(s)\) vanishes. In particular the next sparse fit needs only the same three scalar moments corrected by the single rank-one evaluation update \(-J_0(1,s,s^2)^\mathsf T\operatorname{ev}_s/(uv)\). This is not a third independent reciprocal constraint.

The standalone exact replay uses python-flint 0.9.0, with no external data or randomness. It checks the full coefficient redundancy at three rational width pairs and the complete ordered sign certificates at the specified slice. The general dependency is proved above. The adjacent portable Lean checks the scalar elimination, centered constant, pole implication and rank-one mass relation, not the tableau or inverse-Gram bridge.

Run the [standalone exact replay](erk11-nonaliased-center-quadratic/replay_erk11_nonaliased_center_quadratic.py). The [Lean scalar companion](../lean/RKCert/ReviewedNative/ERK11NonaliasedCenterQuadraticGate.lean) was checked on the four supported releases from Lean 4.34.1 through 4.37.0-rc1.
