# A paid mixed-mask argument for cyclic equality at order eight

**Claim.** Let an actual common-diagonal triangular RK tableau with eight stages satisfy literal rooted order through eight over a field in which \(1,\ldots,8\) are units. If its highest paid strict tall value \(L=\lambda_7\) is nonzero, this is impossible. This closes the **cyclic** equality part only. The proof does not assert the zero-longest branch or an all-chart order-eight floor. It is hand mathematics, not a Lean certificate.

Write \(B=A-\gamma I\), \(\mathbf c=A\mathbf1\), \(\lambda_j=\mathbf b\cdot B^j\mathbf1\). For \(\gamma=0\) use the paid explicit equality obstruction. For the rest \(\gamma\ne0\) and put \(\xi=\gamma^{-1}\). Strict chronology gives \(L=b_8\prod_{i=2}^8 B_{i,i-1}\), so every adjacent factor and \(b_8\) is nonzero. Use the normalized reverse functional
\[
 \mu(y^j)=m_j=\gamma^j\lambda_{7-j}/L,\qquad 0\le j\le7 .
\]
As usual \(B,C=\operatorname{diag}(\mathbf c)\) are modeled by \(T=J-\gamma I,X\) on bounded polynomials, with \(\ell\) the scalar integral. If a word has \(d\) strict hops and \(h\) clock factors, its rooted cost is at most \(1+d+h\), since expanding \(B\) gives unary lifts and a clock factor adds a leaf. No unbounded primitive is used in finite characteristic.

## 1. Paid reductions and the first arbitrary anchor

The paid cyclic rectangle has a globally arithmetic nondegenerate chart, excluded by the seven-clock local argument. Its degenerate chart has \(D\ne0\), nonzero step \(\delta=-E/D\), normalized slope \(t=\delta/\gamma\), and either a prefix of six arithmetic clocks or two actual equal-step endpoint runs with lengths summing to six. In the split chart both endpoints are anchored: \(c_1=\gamma,\ c_8=1-\gamma\). The latter follows from the factored tail at its final target and the first two reverse tall rows, and holds even for a one-clock suffix. Reflection of the trailing marks gives the actual deficit roots \(1-c_8,1-c_7,\ldots\) with the same step. This is reflection of formal polynomial operations or index placement, not the tableau.

Set \(F_1=1+(2-t)y+y^2\), \(g=F_1-\mu(F_1)\), and \(\mathcal D=m_2-m_1^2\ne0\). The degenerate rectangle gives \(\mu(g y^i)=0\) for \(i=0,1,2\). We will repeatedly use that
\[
                         r=\mu(g y^3)\ne0.                 \tag{1}
\]
Indeed \(r=0\) would give a constant monic quadratic recurrence through \(m_5\), incompatible with the four paid reverse rows \(0,1,2,3\). The checked recurrence proof uses the affine geometric residual with slope \(-(1+z)^2\) and value \(\xi\ne0\) at \(z=-1\); distinct nonzero modes separate by their squared shifts, repeated roots by degree two interpolation, and zero roots by rows 1,2 and 0. The proof works with the paid integer units.

Use the arbitrary actual boundary-root product identity: on \(j+k\) holes, polynomials on the first and last retained clocks with roots the first \(j\) actual clocks and last \(k\) actual clocks kill every deficit. Only the exact allocation can contribute. Its two mark values may be zero, and are retained in the joint and single reads. After modeling and reflecting the last polynomial, this gives zero covariance of the normalized boundary polynomials whenever \(j+k\le7\). No extra clock beyond the \(j\) and \(k\) actual roots is assumed. For an arithmetic anchored side its normalized polynomials are
\[
 H_1=1,\qquad H_2=(1+F_1)/2,\qquad
 H_3=(1+3F_1+2F_2)/6,
\]
where \(F_2=(1+y)^3-\frac32 t y(1+y)^2+t^2y^2\).

For \(t\ne2/3\), a six-clock run supplies the ordinary internal \((1,2)\) placement, enforcing \(\mu(gF_2)=0\), contrary to (1) by its nonzero cubic coefficient. This covers the unsplit prefix. If both split runs have at least two clocks, at least one has at least three; the \((3,2)\) covariance of \(H_3,H_2\) gives the same contradiction. The only remaining nonspecial split shape is one five-clock end and one one-clock end.

For \(t=2/3\), every degenerate chart has a good anchored end with at least three arithmetic deficit clocks: use the prefix in the unsplit case. There
\[
 H_3-\mu(H_3)=\frac{53}{54}g+\beta(y-m_1),\qquad \beta=2/81\ne0 .
\]
The opposite end need not yet be anchored in the unsplit chart. Its actual degree-one boundary polynomial is \(1+e y\), where \(e=(\gamma-\rho)/\gamma\) for its first root \(\rho\) in direct or reflected coordinates. Pair it with the good \(H_3\). The \((3,1)\) covariance is \(e\beta\mathcal D\), forcing \(e=0\). Thus the opposite first root is \(\gamma\) even if the actual tail was not affine. If the next two actual roots are \(\gamma+\eta,\gamma+\zeta\), the quadratic boundary polynomial is \(H_2+c y\), \(c=(\delta-\eta)/(2\gamma)\). Pairing with good \(H_3\) gives \(c\beta\mathcal D=0\), so the second root agrees. The actual cubic is then \(H_3+d yH_2\), \(d=(2\delta-\zeta)/(3\gamma)\). Pairing with good \(H_2\) gives \(d r/4=0\), hence \(d=0\) by (1). Finally the \((3,3)\) square of \(H_3\) has covariance \(\beta^2\mathcal D\ne0\). These are all actual-root masks, not nonzero isolated reads. This handles the exceptional slope also in the unsplit six-clock chart.

## 2. The reusable mixed five-clock lemma

Suppose one actual end has five arithmetic clocks of step \(\delta\ne0\), and use an arbitrary actual two-deficit mask at the opposite end; denote its normalized polynomial by \(U\). In a cyclic \(s\)-stage word with \(s\ge7\), the following four covariances are forced (with orders through \(s\)):
\[
             \operatorname{Cov}_\mu(U,F_1)
            =\operatorname{Cov}_\mu(U,F_2)
            =\operatorname{Cov}_\mu(U,F_3)
            =\operatorname{Cov}_\mu(U,F_1^2)=0.             \tag{2}
\]
Here in general the normalized top is \(\lambda_{s-1}\); the application below is \(s=8\).
With \(w=1+y\), the remaining standard gap polynomial used here is
\[
 F_3=w^4-2t y w^3+\frac{11}{6}t^2 y^2w^2-t^3 y^3 .
\]
Indeed the operator for the three-gap mark is
\(6J^4-12\delta J^3+11\delta^2J^2-6\delta^3 T\), obtained by replacing a positive difference power \(j\) on a strict hop by \(j!J^{j+1}\) via the iterated commutator. Dividing the cleared formal polynomial by \(3!T^4\) yields the displayed shorthand.

To prove (2), choose internal target gap counts \(d_1,\ldots,d_q\) to be \((1),(2),(3),(1,1)\), and set \(h=\sum d_j\). Then \(h+q\le4\). Use \(h+2\) physical holes, the actual two-deficit mask at the short end, and \(q\) consecutive internal marks nearest the good end. When the good end is leading, any candidate not killed by the opposite mask already has at least two trailing holes. At most \(h\) holes precede any retained slot, so endpoints of the first \(q\) links have physical index between 1 and \(1+q+h\le5\). When the good end is trailing, a candidate not killed by the opposite mask has at least two leading holes. There are \(m=s-h-2\) retained slots; at every endpoint slot \(v\ge m-q\) of the last \(q\) links, the physical index is at least \(v+2\ge s-h-q\ge s-4\). Thus in either orientation **every** candidate that can contribute has its internal marks in the literal five-clock run. The slots exist because \(h+2+q\le s-1\).

Mark the directed difference on each link by \(P_{d_j}(w)=\prod_{a=1}^{d_j}(w-a\delta)\). A candidate not killed by these marks has at least \(d_j\) holes in each marked link, since its endpoints lie in the arithmetic run. All available holes are then used: exactly the prescribed internal gaps and exactly two short-end holes, with none elsewhere. The boundary deletions and the localized internal bypasses replace disjoint adjacent edge blocks, even if a retained endpoint is shared. Their actual normalized ratios multiply. The actual scalar of the short-end mask at the unique allowable endpoint can be zero; it occurs in the separate boundary read as well as the combined one and is never divided out. Each internal interval's ordinary one-mark calibration uses its own \(d_j+2\) literal clock window and only its own nonzero adjacent block in the denominator.

The mixed word has \(s-1-(h+2)\) strict hops, mark degree \(h+2\), and the initial leaf, so it is paid at \(s\). In the formal model each internal mark is \(d_j!T^{d_j+1}F_{d_j}(\gamma/T)\) and commutes with the remaining plain powers of \(T\). The arbitrary endpoint mark is modeled by its cleared power \(2!T^2U(\gamma/T)\), moving the reflected adjoint if it is trailing. Hence the formal base power is \(T^{s-1}\). Comparing the exact raw joint read with the single calibrations gives
\(\mu(U\prod_j F_{d_j})=\mu(U)\prod_j\mu(F_{d_j})\).
For \((1,1)\), the same ordinary internal placement without the opposing mask gives \(\mu(F_1^2)=\mu(F_1)^2\) (also implied by the rectangle radical in our application). This proves (2). Only bounded formal integration and paid factorials were used.

## 3. Applying the mixed lemma to the remaining split

The short end has first deficit root \(\gamma\) by the split anchors, but its actual second root is arbitrary. Its centered normalized mask therefore is
\[
                   S=U-\mu(U)=g/2+c(y-m_1)
\]
for a field scalar \(c\). Formula (2) means \(\mu(SP)=0\) for \(P\) in the span of \(1,F_1,F_2,F_3,F_1^2\).

For \(t\notin\{0,1,2\}\), that span is the whole degree-four window. Indeed, put \(\theta=t/2\), \(u=y+1-\theta\); the even span is \(1,F_1,F_1^2\), and the odd coefficients of \(F_2,F_3\) in \(u^3,u\) are
\[
 \begin{pmatrix}
 1-3\theta & \theta^2(1-\theta)\\
 \frac43\theta(6-23\theta+16\theta^2) &
 \frac43\theta^3(\theta-1)(4\theta-5)
 \end{pmatrix}
\]
with determinant \(\frac43\theta^3(\theta-1)(2\theta-1)^2\). Thus \(\mu(Sy)=c\mathcal D=0\) gives \(c=0\), and \(\mu(Sy^3)=r/2=0\) contradicts (1). The chart already excludes \(t=0\).

For the two exceptional slopes \(t=1,2\), the same paid tests have a common short calculation. Write \(a=2-t\in\{0,1\}\), \(z=y^2+a y\), \(A=\mu(z)\), \(b=m_1\), \(R=\mu(gy^4)\). Thus \(g=z-A\), \(\mathcal D=A-a b-b^2\), and \(\mu(z^2)=A^2,\ \mu(yz)=A b\) by the first radical identities. For \(t=1\), \(F_2=1+\tfrac32 z-\tfrac12 yz\); for \(t=2\), \(F_2=1+z-2 yz\). In each case (2) implies orthogonality of \(S\) to \(yz,z^2\), giving
\[
 0=r/2+c A\mathcal D,\qquad
 0=(R+2a r)/2+c r .                                      \tag{3}
\]
For the first, use \(\mu(g\,yz)=r\), and
\(\mu(y^2z)-b\mu(yz)=A\mathcal D\), since \(y^2z=z^2-a yz\).
For the second, use \(\mu(g z^2)=R+2a r\) and
\(\mu(yz^2)-b\mu(z^2)=r\). In particular \(A\ne0\) by (1).

The paid reverse tall recurrence at \(N=8\) is equivalently the polynomial identity
\[
 \mu\!\left(A_0 f\right)=\mu\!\left(y(1+y)^2 f'\right)
 \quad(\deg f\le5),\qquad
 A_0=8+(14-\xi)y+6y^2 .
\]
This is the ordinary reverse row on each \(f=y^j\), not a new order assumption. Put \(G_\ell=y^\ell(t y+1+A)(2y+a)\). Since \((1+y)^2=g+t y+1+A\), its application to \(f=g,yg,y^2g\) gives, using the three paid radical annihilations,
\[
                 0=\mu(G_1),\quad 3r=\mu(G_2),\quad
                 2R+(10-a-\xi)r=\mu(G_3).                  \tag{4}
\]
To record the scalar reduction all at once, reduce by \(g\), so \(y^2=A-a y\). The remainders are
\[
\begin{array}{c|ccc}
t & G_1 & G_2 & G_3\\\hline
1&A(1+2A+y)&A^2(1+2y)&A^2(2A-y)\\
2&2A(2y+1+A)&2A(2A+(1+A)y)&2A^2(2y+1+A).
\end{array}
\]
For \(G_1,G_2\) quotient terms contribute zero. For \(G_3\) the quotient has leading \(2t y^3\), so it contributes \(2t r\). The first equation in (4) gives \(b=-1-2A\) at \(t=1\) and \(A=-1-2b\) at \(t=2\). With those relations, the two other rows yield in both cases
\[
              3r=t^2 A\mathcal D,\qquad
              2(R+2a r)=(\xi-6)r .
\]
In detail at \(t=1\), the two remainder means are \(A\mathcal D,-A\mathcal D\), so \(\mu(G_3)=2r-3r=-r\); at \(t=2\) they are \(4A\mathcal D,0\), so \(\mu(G_3)=4r\). This checks both signs. Equations (3) now force \(c=-t^2/6\) and \(\xi=6+2t^2/3\).

The reverse row 0 solves for \(b,A\) using the corresponding affine relation above. The row 1 residual (right minus left) is as follows:
\[
\begin{array}{c|c|c|c|c|c|c}
t & \xi & b & A & m_2 & m_3 & (\xi-12)m_2-5m_3-7b\\\hline
1&20/3&3&-2&-5&-1&32/3\\
2&26/3&3/10&-8/5&-8/5&-12/25&169/30 .
\end{array}
\]
For the table use \(m_2=A-a b,\ m_3=A b-a m_2\). The first residual is nonzero because 2 and 3 are paid units. The second residual is \((3/40)\xi^2\) at \(\xi=26/3\), nonzero because \(\xi=\gamma^{-1}\ne0\) and 3 and 40 are units. There is no separate bad-prime check: even when \(13\) vanishes, the forced \(\xi=26/3\) already contradicts the nonzero diagonal inverse. This excludes both exceptional slopes without enumerating any tableaux.

Thus the mixed five-clock test closes the only remaining cyclic equality case. The argument uses nonzero field pivots and integer units generated by \(1,\ldots,8\); coefficients such as 53 may vanish without affecting the proof. No assertion about the zero-longest branch, differing diagonals, or the surplus-stage branch is made.
