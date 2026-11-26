# A fifth-degree defect forces an extra explicit stage over every nonzero commutative ring

**Theorem.** Fix integers \(m\ge0,\ r\ge10,\ p=m+r\). Let \(K\) be any field in which \(p!\ne0\). A strictly lower triangular \(n\)-stage matrix with an output row \(L\) exact on all rooted stage-derivative profiles of tree order at most \(r\) for the weight \((1-x)^m/m!\) must satisfy
\[
 n\ge \lceil 3r/2\rceil-1 .
\]
All integrals in the proof are primitives of individual polynomials; no topology or ordering of \(K\) is used. In particular every denominator-cleared explicit RK method of order \(p\ge10\) over a **nonzero commutative unital ring** has at least \(\lceil3p/2\rceil-1\) stages. Its genuine \(m\)th last-path tap \(L=\mathbf b^{\mathsf T} A^m\), over a field, has last contributing index at least \(\lceil3(p-m)/2\rceil-1\) whenever \(p-m\ge10\).

This extends the coefficient domain of the existing fifth-degree argument, not its characteristic-zero numerical bound. Source: RKResearch commit c1d29976a37f7f264f7123bf0cd69a8126a107b3, ai-generated/lower-bounds/proof-dependencies/worker_log_standalone.md, §§1–5 (SHA-256 4bf2b15f34742c079335f3c55cbe90fb57472e327e2c1f26fd374ffcc293de17); its characteristic-zero surgery account is ai-generated/lower-bounds/characteristic-zero/erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md §1. Here all constants needed in positive characteristic are justified explicitly. The already-proved Beta rank argument is included for clarity.

## The two polynomial calculations behind the count

Within the stated order budget, write \(Jx^k=x^{k+1}/(k+1)\), let \(c=A\mathbf1,\ C=\operatorname{diag}(c),\ Y=I-C\), and use coordinatewise multiplication of stage vectors. Start with \((\mathbf1,1)\). Taking \((v,f)\mapsto(Av,Jf)\) uses one degree, and multiplying two pairs multiplies their entries and adds their degrees. Within each budget take the linear span. These are precisely the ordinary rooted stage profiles: adjoining a unary root integrates, identifying roots multiplies, and the degree is tree order minus one. In particular \((P(c),P)\) is available at degree \(\deg P\). Let \(F_k\) consist of \(v\) occurring in a pair \((v,0)\) through degree \(k\); let \(E_k\) consist of all first components through that degree. Every \(F_k\) vector vanishes at the first coordinate because there the numerical and polynomial profiles agree at \(0\).

For exponents \(0\le i\le r-1\), write \(\ell_m(x^i)=i!/(m+i+1)!\). The stated exactness says \(Lv=\ell_m(f)\) for every pair through degree \(r-1\). If \(2k\le r\), a pair \((0,P)\) through degree \(k\) must have \(P=0\): its first coordinate gives \(P=xQ\), and the \(k\) tests \(LC^a\) give \(\ell_m(x^{a+1}Q)=0\) for \(0\le a<k\). To see the matrix is invertible, more generally the size-\(h\) matrix
\[
 \left((a+i+j)!/(a+b+i+j+1)!\right)_{0\le i,j<h}
\]
is invertible if \((a+b+2h-1)!\ne0\). Scaling row \(j\) by \((a+j+b+h)!/(a+j)!\) leaves evaluations at \(u=a+j\) of the degree-\((h-1)\) polynomials \(\prod_{\nu=1}^{i}(u+\nu)\prod_{\nu=i+2}^{h}(u+b+\nu)\). At \(u=-1,\ldots,-h\) their matrix is triangular with pivots \((-1)^{v-1}(v-1)!\prod_{\nu=1}^{h-v}(b+\nu)\) in row \(v\). Hence the polynomials form a basis and their evaluations at the distinct \(a,\ldots,a+h-1\) are invertible too. The choice \(a=1,b=m,h=k\) costs only \((m+2k)!\). Thus \(E_k=P_{\le k}(c)\oplus F_k\), with polynomial dimension \(k+1\). We call this uniqueness of the polynomial component separation through \(k\).

The second calculation is triangular. For a diagonal \(D\), let \(D^\dagger\) invert each nonzero diagonal entry and send zero to zero. Interpolation on its distinct entries makes it a polynomial in \(D\) over this field. If \(U\) is invariant under \(D,A\), \(z\) is supported on nonzero entries of \(D\), and \(Dz-\alpha Az\in U\), then \(z\in U\). In the quotient \(z=\alpha D^\dagger A z\), and \(D^\dagger A\) is nilpotent. For rows the proof uses right multiplication by \(A D^\dagger\).

The quadratic defect \(d=Ac-c^2/2\) belongs to \(F_2\), and \(AF_k+CF_k\subseteq F_{k+1}\). If \(F_j=F_{j+1}\) for \(j\ge2\) within separation, the triangular calculation gives \(c\in F_{j+1}\), a contradiction. Also \(F_1=0\), and \(d\ne0\) by the same calculation applied to the zero space. Hence \(\dim F_k\ge k-1\) for \(k\ge1\) and every increment beyond degree one is strict as far as separation holds.

## The reverse rows and the five-stage impossibility needed below

Put \(q=\lfloor r/2\rfloor\), \(h_1=(m+1)LA-LY,\ h_2=(m+2)LYA-LY^2\). Set \(V_0=\operatorname{span}(h_1)\) and \(V_{j+1}=V_j+V_j A+V_jY+\operatorname{span}(h_2)\). The identity \(\ell_m(Jf)=\ell_m((1-x)f)/(m+1)\), and the same identity at \(m+1\), show that \(V_j\) annihilates \(E_q\) whenever \(q+j+2\le r\). At a plateau the row space is invariant under \(A,Y\) and contains \(h_2\), so it contains \(LY\) by the triangular calculation. But \(LY\mathbf1=(m+1)/(m+2)!\ne0\), whereas the space kills \(\mathbf1\). Hence \(\dim V_j\ge j+[h_1\ne0]\).

For \(r=2q\), use \(j=q-2\). For \(r=2q+1\), use \(j=q-1\). In the odd case if \(h_1=0\), choose the last nonzero entry \(L_i\). Strictness gives \(c_i=1\) and \(V_j\) vanishes there. Yet \(e_i\notin E_q\): if a corresponding polynomial were \(P=xQ\), exactness on its \(q+1\) clock tests would give \(\ell_m(x^aP)=L_i\) for \(0\le a\le q\). Subtract consecutive tests and use the same moment determinant with \(a=1,b=m+1,h=q\), scaled by the unit \(m+1\). This forces \(Q=0\), contradicting \(L_i\ne0\). This supplies a further column annihilated by \(V_{q-1}\). We have proved, for any \(r\ge5\),
\[
 n\ge\lceil3r/2\rceil-2+\dim F_q-(q-1).                     \tag{1}
\]
In particular the ordinary \(m=0,r=5\) inequality is \(n\ge6\), with no reliance on the fifth-degree surplus about to be proved.

## Why a separated explicit stage algebra has \(\dim F_5\ge5\)

All statements below concern \(p\ge10\), so \(2,3,4,5,6\) are field units. If \(\dim F_5\le4\), strict growth gives dimensions \(1,2,3,4\) at degrees \(2,3,4,5\). For any \(H=E_j\) select stage evaluations successively, keeping a row exactly when its evaluation on \(H\) is independent of those previously kept. Restriction to kept coordinates identifies \(H\) with their full coordinate space. Replace every omitted predecessor in a kept incoming row by its combination of earlier kept predecessors. The resulting matrix is strictly lower, has the retained row sums (apply to \(\mathbf1\)), and its action on restricted \(H\) is the restriction of the old action. Induction on extension and root sum therefore identifies all profiles through degree \(j+1\) with their restrictions; through degree \(j\) ranks and separation persist. Applying this at \(j=5\) gives ten independent rows. Two rows cannot now agree on every tree through degree five. In particular \(c_2\ne0\), since otherwise the first two incoming rows are identical.

We first justify that neither \(F_3\) nor \(F_4\) can be \(C\)-invariant in the alleged profile. Suppose \(C F_j\subset F_j\) with \(j\ge3\) and \(\dim F_{j+1}\le\dim F_j+1\). Compress separately on \(E_j\), and write \(U\) for its restricted \(F_j\). The row annihilator of \(U\) decomposes by clock value, using polynomial spectral projections. In any one clock block it has dimension at most one: a row there killing \(\mathbf1\) would kill all polynomial columns and \(U\), hence the whole compressed coordinate space. There are exactly \(j+1\) represented clock values; their unique normalized rows \(\lambda_x\) have \(\lambda_x\mathbf1=1\), disjoint supports and distinct last indices. At zero the row is \(e_1^{\mathsf T}\). Set \(a_x=\lambda_x A\), supported strictly before the last index of \(\lambda_x\). The primitive errors give \(a_x c^k=x^{k+1}/(k+1)\) for \(k<j\).

Let \(u,v\) be the first two nonzero represented clocks ordered by last index. Modulo \(U\), every vector in the restricted \(F_{j+1}\) is proportional to one \(w\) (or the quotient is zero). Write \(\sigma_x=\lambda_xw\). The row \(\sigma_u a_v-\sigma_v a_u\) kills \(U\), because \(AU\subset F_{j+1}\), and it is supported before the last index of \(\lambda_v\); consequently it is a combination of \(\lambda_0,\lambda_u\). Take \(g(x)=(x^2(x-u)^2)'\). Now \(g(0)=g(u)=0\), while the primitive test gives \(\sigma_u v^2(v-u)^2=0\); the error in the derivative-to-primitive identity belongs to \(F_{j+1}\) even at \(j=3\), so cancels in the cross combination. Hence \(\sigma_u=0\). Then \(a_u\) kills \(U\) and is supported before the last index for \(u\), so is a multiple of \(\lambda_0\), in contradiction to \(a_uc=u^2/2\ne0\). The same last contradiction directly applies if the quotient was zero. This proves the noninvariance assertion.

**First case: \(d,Cd\) independent.** They span \(F_3\). Noninvariance successively forces \(F_4=dP_{\le2}(c)\) and \(F_5=dP_{\le3}(c)\). Since \(d^2\in F_4\), there is a nonzero polynomial \(g\) of degree at most two with \(d_i=g(c_i)\) when \(d_i\ne0\). Put \(z=(xg)(c)-Cd\); its exact polynomial is \(xg\) and it vanishes at all defective and zero-clock rows. Separation therefore supplies a regular row at a nonzero clock; choose the first such row, with clock \(u\). There all defects through degree five vanish, so its incoming row integrates every profile through degree four to \(u\). Dividing the prefix tableau and this row by \(u\) gives an ordinary order-five method by homogeneity; (1) demands at least six predecessors. Among them at most one regular row has clock zero and defective rows at the same clock agree on all of \(E_5\). Thus at least five distinct defective clocks precede \(u\).

For some \(h\) of degree at most two, \(Az-(J(xg))(c)=d h(c)\). On those five clocks the first term vanishes, giving the degree-at-most-four identity \(J(xg)=-gh\). Comparing the first nonzero powers at zero shows that \(h\) is a constant multiple of \(x^2\). The coefficients \(1/(k+2)\) for \(k=0,1,2\) are distinct, so \(g\) is a single monomial. The regular row at \(u\ne0\) has \(Az=0\) by chronology but \(J(xg)(u)\ne0\), a contradiction.

**Second case: \(Cd=\lambda d\).** Here \(\lambda=c_2\ne0\); rescale the tableau by \(\lambda^{-1}\), which preserves the homogeneous degree spaces and row distinctness. Hence \(\lambda=1\). Put \(w=Ad\), independent of \(d\) by the triangular calculation with \(U=\operatorname{span}(d)\) if not. Noninvariance forces \(F_k=\operatorname{span}(d)+wP_{\le k-3}(c)\) for \(k=3,4,5\). The support of \(w\) contains at least two clocks different from 1: otherwise the \(C\)-invariant hull of \(d,w\) has dimension at most three, so equals \(F_4\). The two clocks applied to \(d^2\in F_4\) force \(d^2\) proportional to \(d\). Row two now shows that every defective row has clock 1 and \(d_i=-1/2\).

Set \(t=c_3,z=c_4,y=c_5\) and \(a_{ij}=A_{ij}\). Row three is regular: a defective row there has \(t=1,a_{32}=0\) and duplicates row two. Thus \(a_{32}=t^2/2,\ w_3=-t^2/4,\ t\ne0\), with \(t=0\) otherwise duplicating row one. The cubic defect \(Ac^2-c^3/3\in F_3\), fitted at rows two and three, is \((2/3)d+(4t/3-2)w\). For row four, with defect indicator \(\epsilon\), its two equations are
\[
 a_{42}+ta_{43}=(z^2-\epsilon)/2,\qquad
 (2t/3)a_{42}+t^2a_{43}=(z^3-\epsilon)/3 .
\]
Their determinant is \(t^2/3\ne0\). If defective, the row duplicates row two. Otherwise \(a_{42}=z^2(3t-2z)/(2t),\ a_{43}=z^2(z-t)/t^2\); \(z=0,t\) would duplicate one or three. Fitting \(Aw\in F_4\) first at rows two and three gives \(Aw=k(C-tI)w\). At row four this gives \(w_4=-z^2(3t-2z)/(4t)\ne0,\ k=t/(3t-2z)\).

Consider \(Q(x)=x^2(x-y)(x-3t/2)/4\). The tested defect \(AQ'(c)-Q(c)\in F_4\) is \(2Q(1)d+\chi(c)w\). At rows three and four, \(Q'(t)=tw_3/2,\ Q(t)/w_3=t(t-y)/2,\ Q(z)/w_4=t(z-y)/2\). Since \(t\ne z\), these fix
\[
 \chi(x)=-2Q'(1)+(t/2)k(x-t)+(t/2)(y-x).
\]
At row five \(Q(y)=Q(1)d_5=0,\ w_5=-a_{52}/2\). Subtracting \((t/2)Aw\) from \(AQ'(c)\) there cancels the stated row-two input and the row-three input, leaving
\[
 0=a_{54}\bigl(Q'(z)-(t/2)w_4\bigr)
   =(3/4)a_{54}z(z-t)(z-y).
\]
If \(a_{54}=0\), the quadratic and cubic equations for row five instead give \(a_{52}=\beta y^2(3t-2y)/(2t),\ a_{53}=\beta y^2(y-t)/t^2\), where \(\beta=1-\epsilon_5\). Its \(Aw\) equation gives \(\beta y^2(y-t)(z-y)=0\). For \(\beta=0\) it duplicates row two; for \(\beta=1\), it duplicates row one, three or four as \(y=0,t,z\), respectively. Therefore \(a_{54}\ne0\) and \(y=z\).

The row \(H=e_5^{\mathsf T}-\epsilon_5 e_2^{\mathsf T}-(w_5/w_4)e_4^{\mathsf T}\) kills \(d\) and \(wP_{\le2}(c)\), hence all \(F_5\). Yet \(ACw\in F_5\) and \(HACw=(z-t)a_{54}w_4\ne0\): the contributions at clock \(t\) are \(tHAw=0\) and only column four at row five has a different clock and nonzero \(w\). This excludes the second case. The grade-five surplus is proved.

## Counting and specializing

Separation through \(q\) and strict growth now give \(\dim F_q\ge q\), an improvement of one in (1). Actual \(L=\mathbf b^{\mathsf T}A^m\) is exact on the Beta functional because adjoining \(m\) unary roots uses \(m\) degrees and integrating \(J^m x^a\) over the unit interval gives \(a!/(m+a+1)!\). Truncating at the last nonzero coordinate of this row preserves all its tests by strict triangularity. For a denominator-cleared RK tableau over a nonzero ring, the tall order-\(p\) equation makes \(p!\) a unit. Pass to any maximal ideal. The residue field has characteristic zero or prime characteristic greater than \(p\), and the physical size and all polynomial order equations survive. This proves the uniform stage count (no requirement that the ring itself be a domain or contain the rationals).

At the cited commit the previously stated arbitrary-ring ERK floors for \(p=10,\ldots,20\) are \(13,15,16,18,19,21,22,24,25,27,28\). The theorem here gives respectively \(14,16,17,19,20,22,23,25,26,28,29\). It does not improve the characteristic-zero or ordered-field table. This is a mathematical proof, not a claim of new Lean coverage. A separate doubling argument can strengthen the last entry further.
