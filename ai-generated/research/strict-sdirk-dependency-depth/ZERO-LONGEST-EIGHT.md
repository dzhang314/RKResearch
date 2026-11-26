# The zero-longest order-eight chart: four pointwise boundary zeros

**Claim.** An actual eight-stage common-diagonal triangular RK tableau over a field with \(1,\ldots,8\) units cannot satisfy literal rooted order through eight with highest strict tall value \(L=\lambda_7=0\). This is only the zero-longest equality chart. No cyclic proof or new tableau search is used.

## 1. One compulsory physical vacancy gives a seven-slot path grid

Let \(B=A-\gamma I\), \(\mathbf c=A\mathbf1\), and \(\lambda_j=\mathbf b\cdot B^j\mathbf1\) for \(j\le7\). The case \(\gamma=0\) already has \(L=1/8!\ne0\), so take \(\gamma\ne0\). The paid tall recurrence
\[
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j-j\gamma^2\lambda_{j-1}
\]
and \(\lambda_0=1\) give \(M=\lambda_6\ne0\): otherwise the last two paid zeros descend. If \(b_8=0\), dropping the last row and column preserves literal rooted outputs by triangularity. It would give order eight on seven stages, excluded by the separate decorated-saturation proof. Thus \(b_8\ne0\), and \(L=b_8\prod_{j=2}^8 B_{j,j-1}=0\) supplies a broken physical edge \(B_{i,i-1}=0\).

Every path retaining both adjacent physical indices \(i-1,i\) has weight zero, regardless of marks. The only possibly nonzero one-omission weights omit one of this pair, with total \(M\). Set \(x=\mathbf c-\gamma\mathbf1\); for a one-omission path, occupied slot \(k\) sees physical index \(k\) or \(k+1\). Writing \(T'_k\) for cumulative one-omission weight through physical index \(k\), the paid shifted-clock word gives
\[
 M x_k+T'_k(x_{k+1}-x_k)=(k-1)\kappa,\qquad
 \kappa=\lambda_7+2\gamma M+\gamma^2\lambda_5 .
\]
In the formal model this is \(T^{d-a}(X-\gamma I)T^a1=T^{d+1}1+aJ^2T^{d-1}1\) at \(d=6,a=k-1\), with \([X,T]=J^2\) and \(\lambda_7=0\); it costs \(1+6+1=8\). Before the pair \(T'_k=0\), after it \(T'_k=M\), so the outer actual clocks are
\[
 x_j=(j-1)\delta\quad(j\le i-2),\qquad
 x_j=(j-2)\delta\quad(j\ge i+1),\qquad
 \delta=\kappa/M=(1-2\gamma)/6 .
\]
The last relation is the paid tall row at \(j=6\). No claim is made about the two actual pair clocks, and \(\delta=0\) is allowed.

Identify the pair with one virtual site in the **retained lists only**, on a virtual grid of size \(m=7\). A nonzero physical path with \(h+1\) physical holes has \(h\) virtual holes: if exactly one pair index was omitted, the virtual pair site is retained with either representative, and if both were omitted the virtual site is one of those holes. The two outer literal virtual runs are arithmetic of step \(\delta\), with lengths summing to six. A retained virtual list has \(m-h\) slots, and slot \(v\) sees an index in \([v,v+h]\). None of this is an ordinary compressed tableau or an averaging of the two pair clocks.

Use the top-zero functional
\[
 \nu(y^a)=\frac{\gamma^a \lambda_{7-a}}{\gamma M}\quad(0\le a\le7),
 \qquad \nu(1)=0,\quad \nu(y)=1,\quad \xi=\gamma^{-1},\quad t=\delta/\gamma .
\]
The letter \(y=\gamma/T\) is shorthand after clearing powers; \(T=J-\gamma I\) is not inverted. The normalization uses only the next paid nonzero \(M\) and \(\gamma\), never \(L\) or the step.

## 2. If there are four safe clocks, the earlier pointwise test already applies

The earlier four-clock vanishing proof only uses its \(s\ge9\) in obtaining a safe run of four from the outer count. Its local geometry and scalar evaluation apply here whenever one run has four clocks. For the chosen run \([u,u+3]\), with \(h\) free virtual holes and \(q\) consecutive marked links starting at occupied slot \(u\), when \(h+q\le3\) every marked endpoint lies in that run. Put mark \(P_d(w)=\prod_{a=1}^d(w-a\delta)\) on a directed difference. If any gap has fewer than its required \(d\) holes, it vanishes. Choose mark degrees \((1),(2),(3),(1,1)\) with \(h=0,1,2,1\) respectively, so total required holes \(h+1\) exceeds availability. These words vanish pointwise and cost \(1+(6-h)+(h+1)=8\). The bounded formal model at base \(T^7\) gives \(\nu(F_1)=\nu(F_2)=\nu(F_3)=\nu(F_1^2)=0\), with the ordinary normalized internal gap polynomials.

For completeness this scalar part really holds at eight: after setting \(u_y=y+1-t/2\), \(1,F_1,F_1^2\) span the even degrees through four. The odd parts of \(F_2,F_3\) have determinant \(\frac43 k^3(k-1)(2k-1)^2\) with \(k=t/2\). If \(t\notin\{0,1,2\}\) their vanishing forces \(\nu(y)=0\). For \(t=0,1,2\) respectively, \(\nu(F_1)=\nu(F_2)=0\) gives \((\nu(y^2),\nu(y^3))=(-2,3),(-1,1),(0,0)\). The top reverse row gives \(\xi=2+6t\). Reverse row 1 then equates 7 to, respectively, \(5,-1,0\), impossible by the paid units \(2,8,7\). Thus any safe four-clock run is enough, regardless of the other side.

## 3. The only remaining geometry: both literal sides have three clocks

If neither side has four, both have length three, so \(i=5\): physical stages \(4,5\) are the two representatives of the central virtual site. The first and last actual clocks are
\[
                         c_1=\gamma,\qquad c_8=\gamma+6\delta=1-\gamma.
\]
The first three actual deficit clocks are \(\gamma,\gamma+\delta,\gamma+2\delta\); the last three, in reflected coordinates \(1-c_8,1-c_7,1-c_6\), are the same list.

Here is the paid endpoint vanishing lemma. For \(j,k\) with their deficit roots in these literal runs, and \(j+k\ge1\), take
\[
                    h=j+k-1\quad\text{virtual holes}
\]
and the degree \(j\) polynomial with the first \(j\) actual clocks as roots at the first retained slot, and the degree \(k\) polynomial \(\prod_{a=1}^k(c_{9-a}-C)\) at the last. The empty mask is 1. If the virtual leading count \(u\) is less than \(j\), the first slot is a literal root in the prefix. If the virtual trailing count \(v\) is less than \(k\), the last slot is a literal root in the suffix. But \(u+v\le j+k-1\), so at least one of those deficits is forced. In particular, **the physical output vanishes term by term**. This includes either choice of actual retained pair representative and the case in which both were deleted. A deficit never evaluates the ambiguous pair as a root. There is no surviving path to calibrate or mode weight to divide by.

These reads have \(h+1=j+k\) physical holes, \(7-j-k\) strict hops, and \(j+k\) clock degrees, so all cost exactly eight. Put \(H_0=1\) and let the normalized formal boundary polynomials at the anchored arithmetic ends be
\[
 H_2=(1+F_1)/2,\qquad H_3=(1+3F_1+2F_2)/6,\qquad
 F_1=1+(2-t)y+y^2,\qquad
 F_2=(1+y)^3-\tfrac32t y(1+y)^2+t^2y^2.
\]
These formulas follow by applying \(X^j1=j!J^j1\) termwise in the boundary polynomial and factoring its cleared leading \(j!T^j\). Formally the trailing polynomial is reflected, so its polynomial in \(T^\ast=(J^\ast-\gamma I)\) moves to the leading side under \(\ell(fg)\); \(J^\ast\) is integration from \(x\) to 1. For monomials its adjunction uses only \((u+1)(u+v+2)\) and \((v+1)(u+v+2)\), with \(u+v+2\le8\) in the paid window. The two mark degrees plus plain hops give base \(T^{7}\), not the virtual fully paid base \(T^6\). Thus the formal read is \(j!k!\gamma M\,\nu(H_jH_k)\), and its pointwise physical zero gives \(\nu(H_j H_k)=0\). This is a vanishing identity, not the multiplicativity of independently calibrated survivors.

Use just four pairs \((2,0),(3,0),(2,2),(3,2)\), respectively with 1, 2, 3, and 4 virtual holes. Since \(\nu(1)=0\), their four identities in sequence give
\[
                      \nu(F_1)=\nu(F_2)=\nu(F_1^2)=\nu(F_1F_2)=0.
\]
If \(t=2/3\), the exact expansion \(F_2-(13/9)F_1=-4/9+(2/27)y\) already contradicts \(\nu(y)=1\). If \(t\ne2/3\), put \(g=F_1-\nu(yF_1)\), a monic quadratic. Then
\[
                \nu(g)=\nu(yg)=\nu(g^2)=\nu(gF_2)=0.
\]
Since \(g\) is monic, \(\nu(g^2)=0\) gives \(\nu(gy^2)=0\) after the first two. The cubic coefficient \(1-\frac32t\) of \(F_2\) is nonzero, so \(\nu(gF_2)=0\) then gives \(\nu(gy^3)=0\). These four annihilations force a fixed monic quadratic recurrence through \(\nu(y^5)\).

The same first four reverse tall rows, with physical size \(s=8\), act on this top-zero sequence:
\[
 (8-k)a_k=(\xi-2(7-k))a_{k+1}-(6-k)a_{k+2},
 \qquad a_k=\nu(y^k),\quad 0\le k\le3 .
\]
The fixed-quadratic incompatibility needs only nonzero initial data, not initial value one; here \((a_0,a_1)=(0,1)\). For a geometric mode \(r^k\) the residual coefficient is affine in \(k\), slope \(-(1+r)^2\), constant \(\xi\ne0\) at \(r=-1\). Two distinct nonzero modes form a monic fourth-order residual sequence; four zeros kill it, and squared shifts separate the modes. At a repeated nonzero root divide by the geometric factor to get a degree-at-most-two residual in \(k\), and use the first three indices; when \(r=-1\) the derivative of the affine coefficient in \(r\) is also constant in \(k\), so its nonzero value \(\xi\) still kills both amplitudes. A zero root leaves only a single tail mode, killed by rows 1 and 2; a double zero forces \(a_1=0\) by row 1. This contradicts the initial data. All pivots are nonzero field elements or products of paid integer units.

This proves the zero-longest order-eight branch with one run-length dichotomy and a single actual endpoint bank for the balanced case. It neither requires a nonzero step nor uses a two-node support square, separate skip calibrations, identification of the two clocks on the broken pair, or a pre-existing order-eight cyclic exclusion.

Together with the [cyclic order-eight chart](CYCLIC-EIGHT.md), this excludes eight stages at order eight. The [marked saturation proof](DECORATED-SATURATION.md) excludes seven; the paid tall cap excludes smaller widths. Passing to a maximal residue field gives the bound over every nonzero commutative ring, as in the [proof for all larger orders](../../lower-bounds/sdirk-paid-short-equality-floor.md).
