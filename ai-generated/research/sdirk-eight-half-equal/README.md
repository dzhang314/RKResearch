# The active single-clock quadratic-residual branch of ten-stage strict SDIRK8

Suppose \(A,\boldsymbol b\) is a ten-stage strict SDIRK tableau of ordinary order at least eight over a characteristic-zero field. Put \(\boldsymbol c=A\boldsymbol1\) and \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\). Assume **all nonzero-residual rows have the same physical clock**, and at least one has a nonzero output weight. Then a surviving tableau must have
\[
 \gamma=c_1=c_{10}=\tfrac12,\qquad
 (g_1,g_2,\ldots,g_9,g_{10})=(1/8,0,\ldots,0,1/8),
 \qquad b_{10}=-b_1,
\]
and **all ten output weights nonzero**. In particular, the entire seven-zero-row branch in this physical-clock family is excluded. The remaining all-active eight-zero-row family is not excluded. Multiple physical off-zero clocks, entirely silent off-zero rows, and the zero-free branch are outside this result. The unrestricted interval remains **10–11**.

## 1. Shared physical and graded reductions

Write \(U\) for the zero coordinates, \(L\) for their complement, \(m=|U|\), and \(\ell=|L|\). Use the saturated spaces \(E_j,F_j,W_j,Z_j\) as in the [off-zero mass proof](../sdirk-eight-offzero-clock-mass/README.md), and \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(B=\operatorname{diag}(\boldsymbol b)\), \(N=A-\gamma I\), \(M=CA-AC-A^2\). In particular \(F_{j+2}=ME_j\), \(Z_j=\operatorname{Ann}(E_{7-j})\), \(F_j=\operatorname{Ann}(W_{7-j})\), and
\[
 \dim(W_j\cap U_{\rm row})=m-\dim(E_{5-j}\cap U),\qquad
 \operatorname{rank}(F_{j+2}|_U)=\dim(E_j\cap U).
\]
The ranks of \(E_2,E_3,E_4,W_2,W_3\) are \(4,6,8,4,6\). An off-zero group is *active* if a physical member has nonzero weight. As in the prior proof, every active joint \((c,g)\) group cancels, the terminal stage is active off-zero, and \(c_1=\gamma,c_{10}=1-\gamma\). Thus the sole common off-zero clock is \(\gamma=1/2\).

The first two physical zero clocks \(a,b\) are the second and third rows. Write \(t^2=1/2\), choosing the sign at the front. With \(u=1+2t\) these have
\[
 a=(1+u)/2,\qquad b=(1+w)/2,\qquad
 (w,r)=(2-u,0)\ \hbox{or}\ (2u,3u/2-1).
\]
Here \(r=A_{32}/\gamma\) is the normalized second strict tap in the third row. This is the [literal first-three calculation](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) with \(g_2=0\). Put \(\boldsymbol h=N\boldsymbol g\). The two front zero values are \(h_a=\gamma g_1u\) and \(h_b=\gamma g_1(w-r)\), both nonzero. The genuine pure grade-three space is \(\langle\boldsymbol g,\boldsymbol h\rangle\), and
\[
              A\boldsymbol c^{\odot2}-\boldsymbol c^{\odot3}/3
                         =(2/3)(\boldsymbol g+\boldsymbol h).                \tag{1}
\]
The two leading evaluations determine both coefficients.

The last two rows before the terminal one are active zeros. Indeed the actual reverse quadratic word
\[
 \widehat{\boldsymbol w}
  =\boldsymbol b^{\mathsf T}(I-C)A-\tfrac12\boldsymbol b^{\mathsf T}(I-C)^2
  =-\tfrac12\boldsymbol b^{\mathsf T}M
\]
is a nonzero multiple of \(\boldsymbol b^{\mathsf T}G\). The terminal two weights are nonzero and their clocks differ by \(D(1)\) and full reverse rank. If \(b_8=0\), the equations for \(D(1)\) and \(\widehat{\boldsymbol w}\) at that coordinate force both later strict taps zero, violating full reverse rank. So the last three coordinates can be normalized by their own weights and reversed, even if elsewhere weights vanish. Their reflected second residual is zero because the only active off-zero clock is \(1/2\). The [trailing three-row relation](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) gives the same star/arithmetic pairs as the front with independent sign of \(t\); their actual clocks \(z_1,z_2\) are one minus the reflected values. Both normalized reverse cubic defects \((\widehat{\boldsymbol w}N)_i/b_i\) are nonzero there. The two rear clocks cannot both be fourth-Gauss roots, by the exact ratio resultant. The four front/rear zero clocks are pairwise distinct by their rational parts in \(\mathbb Q(t)\), and differ from \(1/2\).

The [common scalar replay](check_endpoints_and_low_mass.py) checks these nonvanishings and the two-by-two nodal Hankel determinant for the five pegged sites (both front zeros, both rear zeros, \(1/2\)). If there were at most five different zero clocks, all ordinary sites would be on those five pegged sites plus at most one extra. A degree-six nodal polynomial would then pay two moments, which the nonzero Hankel determinant excludes. Thus there are at least six distinct zero clocks. Also there must be at least five **individually active** zero rows: four active rows would give exactly four ordinary sites, all Gauss, containing both rear clocks. Whenever there are just five active zero rows, they have five distinct clocks, by the same reasoning.

### Residual variation is impossible

Let \(L_4=70X^4-140X^3+90X^2-20X+1\). If the off-zero residual values vary, then \(E_2|_L\) has rank two, so \(F_4|_U\) has rank two by support duality. The two columns \(\boldsymbol h,L_4(\boldsymbol c)\) there are independent at the two front zero rows by a scalar determinant. Thus
\[
                         (c_i-\xi)h_i=\beta L_4(c_i),\qquad i\in U.          \tag{2}
\]
Solving on the front pair gives \(\xi=21/74\) (star) or \((59273u+42183)/112798\) (arithmetic), and \(\beta\ne0\) since \(h_a,h_b\ne0\) and \(a\ne b\).

The same calculation applies whenever an active zero restriction of \(F_4\) is a line extension of \(\boldsymbol h,L_4(\boldsymbol c)\), with both front zero rows active. Its obstruction is as follows. If (2) holds on all \(U\), the row \(\boldsymbol h^{\mathsf T}B\) is independent of \(\boldsymbol g^{\mathsf T}B\); otherwise \(h\) would vanish on active zero rows, and (2) would make even the active first rear zero a Gauss node. Therefore those two pure rows span \(Z_3\). The row \(\widehat{\boldsymbol w}N\) is proportional to \(\boldsymbol h^{\mathsf T}B\) on \(U\), with nonzero factor because its penultimate normalized value is nonzero. At the two active rear zeros, (2) then determines the reflected value of \(\xi\) to be \(1-\xi\), since \(L_4(1-X)=L_4(X)\). Neither pair of the four choices (two signs and two phases) can add to one; the replay checks all sixteen. This excludes varying residuals.

### Consequences of constant off-zero residual

Now \(g_i=g_1=1/8\) on \(L\). The ranks of the active \(W_2\) restriction and the physical \(E_2\) restriction are each one. The former follows by the weighted isomorphism \(E_2^{\mathsf T}B=W_2\), because a nonzero active residual detects the pure line. Hence \(\operatorname{rank}(E_3|_L)=\ell-1\) by support duality. This is at most two because \(E_3\) there is spanned by \(1,h\). Therefore \(\ell=2\) or \(3\). Also \(F_4|_U\) has rank three and \(F_4\cap \mathbb K^L=\langle\boldsymbol g\rangle\).

The fourth physical row is zero. For contradiction suppose its \(c,g\) equal the first row's \(1/2,1/8\). The strict taps to \(1,2,3\) then satisfy a homogeneous system with matrix
\[
 \begin{pmatrix}1&1&1\\ \gamma&a&b\\
 \gamma^2-(2/3)g_1&a^2&b^2\end{pmatrix}.                                      \tag{3}
\]
The equations are row sum, quadratic read, and (1), since \(h_4=g_1 A_{41}\). Its determinant is a unit for both phases, so all taps vanish and the row is a literal twin. The fourth reversed row is also zero. Its weight \(b_7\) is nonzero: if it were zero, the actual \(D(1)\), reverse quadratic, and reverse cubic pure words give the same homogeneous system on the three weighted trailing taps. Indeed the reverse pure cubic defect is \((2/3)(\widehat{\boldsymbol w}+\widehat{\boldsymbol w}N)\) by the two literal initial reads in reflected time. Invertibility would kill column seven of all reverse words. With \(b_7\ne0\), normalize the four trailing rows; the same twin proof works on this literal block. Thus any middle off-zero row is at physical position five or six.

At the fourth row, whose clock is \(s\), the strict taps are given instead by matrix (3) and right-hand side
\[
 s-\gamma,\qquad s^2/2-\gamma s,\qquad s^3/3-\gamma s^2,                       \tag{4}
\]
with \(h_s=g_1\) times the first tap. If \(s=a\) or \(s=b\), uniqueness makes this row a literal twin of that earlier zero row (insert zero taps before the diagonal). Consequently \(a,b,s\) are distinct.

## 2. Active zero receiver counts

If exactly two off-zero rows are active, their weights cancel and \(\boldsymbol b^{\mathsf T}G\) is a nonzero multiple of the difference of those two axes. This generates \(Z_2=\operatorname{Ann}(E_5)\), so the pair agrees on every \(E_5\) column, including \(h\). Thus the off-zero contributions of \(h\) and \(h^2\) cancel. If all three off-zero rows are active, \(h\) varies on \(L\) by the rank two of \(E_3|_L\). The three \(h\) values there must be distinct: the paid moments in \(1,h\) have zero off-zero aggregate, the second by \(\boldsymbol b^{\mathsf T}G\boldsymbol h=0\), and two distinct values would require both group aggregates zero, impossible for the singleton. Then the off-zero aggregate of \(h^2\) is nonzero by Vandermonde. In both cases the aggregate on \(U\) of \(h c^j\) vanishes for \(j=0,\ldots,4\). The aggregate of \(h^2\) is zero in the two-active case and nonzero in the three-active case (its global total is zero by the pure pairing).

If \(B\boldsymbol h\) is nonzero on \(U\), the two weighted pure rows span \(Z_3\), so both active rear zeros have \(h_i\ne0\). If there are five or six active zero rows with at most five individually active clocks, the \(h c^j\) moments force the \(h\)-weighted aggregate at each clock to vanish. Both distinct rear clocks would then need another active member. This is impossible: four individually active clocks would be all Gauss as above; with five clocks and at most six active rows at most one clock repeats. Thus there are at least six active zero rows, and with exactly six they have distinct clocks.

In the two-active case, exactly six active zero rows are impossible when \(B\boldsymbol h\) is nonzero on \(U\). On those six coordinates the \(B\)-orthogonal complement of the degree-three clock polynomials is a nondegenerate two-dimensional space: the degree-three Gram is the exact ordinary Hilbert matrix. It contains the nonzero isotropic column \(h\) and the column \(L_4\), both orthogonal to \(h\). In a nondegenerate two-dimensional space the orthogonal complement of an isotropic line is itself, so these columns are proportional. This contradicts the exact independent \(h,L_4\) reads on the two active rear zeros, because the normalized reverse \(h\) is proportional to \(h\) there.

## 3. Two active off-zero rows

If \(\ell=3\) with exactly two active off-zero rows, \(B\boldsymbol h\) must vanish on \(U\). Otherwise \(E_3^{\mathsf T}B=W_3\): ordinary probes detect scalar profiles, and both pure directions are weighted independently. The silent off-zero coordinate axis would then belong to \(F_4=\operatorname{Ann}(W_3)\), but \(F_4\cap\mathbb K^L=\langle\boldsymbol g\rangle\) has no literal axis. As \(h_a,h_b\ne0\), this forces \(b_2=b_3=0\). There are seven zero rows, hence just five active ones at distinct clocks. Row four is the first active zero.

If \(x=c_4\) is an active first zero and \(B\boldsymbol h=0\) on \(U\), its first tap vanishes and its three strict moments are taken just at \(a,b\). Hence
\[
 F(x)=x^3/3-x^2/2-(a+b)(x^2/2-x/2)+ab(x-1/2)=0.                            \tag{5}
\]
If the ordinary scalar quadrature has five sites, its two rear nodes \(z_1,z_2\) and \(x\) force the Hankel determinant of
\(I(X^{i+j}(X-x)(X-z_1)(X-z_2))\), \(0\le i,j\le2\), to vanish (the monic quadratic of the other two sites has its coefficient vector in the kernel). This determinant is coprime to (5) for every phase. Thus the \(\ell=3\), two-active case is excluded.

Now suppose \(\ell=2\) and \(B\boldsymbol h=0\) on \(U\). There are five or six active zero rows because \(b_2=b_3=0\); row four active with five sites fails as above. We detail the other cases.

* **Six active zero rows.** These are rows four through nine. They are at distinct clocks: if only four or five distinct clocks, the pure row \(\widehat{\boldsymbol w}N\) would have to vanish at a nonrepeated rear site by the scalar Vandermonde equations. In detail \(h,Ch\) are supported on precisely the two silent rows, independent there; hence this pure row annihilating \(E_4\) vanishes on both. It is supported on \(U\) because the endpoint pair agrees on \(h\) (so \(h_{10}=0\) and \(A_{10,1}=0\)). Thus its moments of degrees \(0,\ldots,4\) separate its active sites if there are at most five, and there are too few duplicate rows to hide both nonzero rear entries. The restrictions of \(h,Ch\) already use two of the three directions of \(F_4|_U\), so the latter restricts to the \(L_4\) line on active zeros. Write \(x=c_4\), \(y=c_5\). For the two supported cubic traces
\[
\begin{split}
 p_0(X)&=(X-x)(X-a)(X-b),\\
 p_1(X)&=(X-x)\{h_a(b-x)(b-X)+h_b(a-x)(X-a)\},
\end{split}
\]
add a multiple of \(g\) to kill the two off-zero rows, and a multiple of \(h\) to kill both silent rows (the ratios at \(a,b\) agree). On active rows their values are the stated traces. Thus their \(A\)-reads at \(x,y\) are just the diagonal, since they vanish at the first active clock \(x\). With \(D_p=\gamma p-Jp\), this gives \(D_p(y)L_4(x)-D_p(x)L_4(y)=0\) for both. Remove the known factor \(y-x\); the two remaining polynomials have resultant coprime to \(F(x)\) in both front phases. No continuation exists.

* **Five active sites, with row four silent.** Then rows two, three, four are the whole silent set, and the five active clocks are distinct. Put \(s=c_4\), \(x=c_5\), with \(s\ne a,b\) by the twin argument. The active nodal polynomial factors as \((X-z_1)(X-z_2)P_3(X)\). Its three orthogonality moments determine the monic \(P_3\) by an invertible exact Hankel matrix. In particular \(P_3(x)=0\). At row five, \(h_x=0\), so its first strict tap is zero. Its remaining three taps at \(a,b,s\) are determined by the three clean moments of orders zero to two. In \(F_4|_U\) the columns \(h,Ch,L_4(c)\) are a basis (the first two are silent and independent, the third is nonzero at active sites). Use this basis on rows two through five for the pure columns \(A\boldsymbol h\) and \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\). Their two four-by-four determinants, cleared of the Vandermonde denominator and factors \(s-a,s-b\), have gcd one in \(s\) over the \(P_3(x)\) quotient, in all eight relative phase choices. The [replay](check_five_sites_late.py) explicitly checks the inverses in this quotient. This excludes the last \(B\boldsymbol h|_U=0\) case.

Thus with \(\ell=2\), the receiver-count argument requires seven or eight active zero rows. The one-silent case is treated in Section 5.

## 4. Three active off-zero rows

Here \(\ell=3\), all three off-zero weights are active, and \(B\boldsymbol h\) is nonzero on \(U\) by its nonzero \(h^2\) mass there. There are at least six active zero rows by Section 2.

### Exactly one silent zero

Six active zero rows have distinct clocks by Section 2. The silent axis is in \(F_4\) by \(E_3^{\mathsf T} B=W_3\). Hence \(F_4\) restricted to the active zeros has rank at most two, spanned by \(h,L_4(c)\) by the independent rear evaluations. This gives (2) on the active zeros, with \(\xi=1-\xi^*\) read from the rear. If both front zero rows were active this would be the excluded sum of front/rear \(\xi\)'s. Thus one of rows two, three is silent. Let \(f\) be the other clock, so \(\beta=(f-\xi)h_f/L_4(f)\), with all required nonzero values checked. Row four is active and its literal \(h(s)\) from (3)–(4) gives the quartic
\[
                         (s-\xi)h(s)-\beta L_4(s)=0.                          \tag{6}
\]
Also \(L_4(\xi)\ne0\), so no active clock equals \(\xi\).

There are six ordinary sites, including \(f,z_1,z_2,s\). Let \(P(X)\) denote their four-factor product and \(Q(X)\) the monic quadratic for the other two sites, so the full nodal polynomial is \(D(X)=P(X)Q(X)\). Besides \(I(D)=I(XD)=0\), equation (2) and the paid \(h\) moment give
\[
 I\!\left(\frac{L_4(X)-L_4(\xi)}{X-\xi}\right)D(\xi)
       -L_4(\xi)I\!\left(\frac{D(X)-D(\xi)}{X-\xi}\right)=0.                   \tag{7}
\]
Indeed \([1-D(X)/D(\xi)]/(X-\xi)\) is the degree-five polynomial agreeing with \(1/(X-\xi)\) at all sites, and the ordinary moments integrate it exactly. Equations (7) and the two scalar moments are homogeneous linear equations on the coefficients of \(Q\), with last coefficient one. Their determinant is cubic in \(s\), and is coprime to (6) in every one of the sixteen oriented choices, by [exact replay](check_triple_one_silent.py).

### No silent zeros

All weights are nonzero, so use full weighted reflection if necessary to put the middle off-zero stage at row five. Its \(h\) value is nonzero because the three off-zero \(h\)'s are distinct and \(h_1=0\). The restrictions \(h,Ch,L_4(c)\) form a basis of \(F_4|_U\): the first two cannot be proportional, \(h,L_4(c)\) are independent on the front, and dependence would give the already excluded \(\xi\) relation at both ends. Thus \(g,h,Ch,L_4(c)\) span \(F_4\). In place of \(L_4(c)\) use \(L_4(c)-L_4(\gamma)g/g_1\), which vanishes on \(L\).

At row five, divide its strict taps by its nonzero \(h_5\). The tap to stage one becomes \(1/g_1\), and the remaining three normalized taps to \(a,b,s\) have moment vector
\[
                            -1/g_1,\quad-\gamma/g_1,\quad 2/3-\gamma^2/g_1 .
\]
This uses the identical \(c,g\) of row one and (1). Hence the taps are determined by a three-site Vandermonde. Subtract the initial value of each of \(A\boldsymbol h\) and \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) times \(g/g_1\) and use the remaining three pure basis vectors at rows two through five (divide the last read by \(h_5\)). The two exact rank determinants, with denominators cleared, have gcd \((s-a)^2(s-b)^2\) for each front phase. These repeated clocks were already excluded by the literal twin at row four, or by the normalized middle tap matrix. See [the exact script](check_triple_all_active.py).

## 5. Two off-zero rows and one silent zero

Now \(\ell=2\), and the arguments above leave seven or eight active zero rows. If seven, the silent coordinate axis lies in \(F_4\), and the same active rank-two argument gives (2) on all active zeros, with the silent row among two and three. Here all seven active clocks are distinct. To check this, \(L_4(\xi)\ne0\), so no active clock is \(\xi\), and \(h_i=\beta L_4(c_i)/(c_i-\xi)\) is the same within every active equal-clock group. Thus both the \(h\) moments and its zero norm transfer to the aggregate quadrature. If at most five ordinary sites existed, the first five \(h\) moments would force \(h=0\) there, hence four Gauss sites. Both active rear sites have \(h\ne0\); to cancel both while preserving four other sites would require at least eight active rows. If exactly six ordinary sites existed, \(h\) is nonzero there, and in the nondegenerate two-dimensional complement to cubic scalars the isotropic \(h\) and \(L_4\) would be proportional. Equation (2) would then force \(h\) to be supported at a single clock, contrary to its first five moments. Thus all seven ordinary clocks are distinct.

The active front site \(f\), the rear pole \(\xi\), the coefficient \(\beta\), and the quartic (6) for \(s=c_4\) are as in Section 4. For row five at \(y=c_5\), its prescribed \(h_y=\beta L_4(y)/(y-\xi)\) fixes the tap to row one as \(h_y/g_1\). The other three taps at \(a,b,s\) follow from row sum, quadratic moment and (1). The actual \(A\boldsymbol h\) and \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\) values at active sites \(f,s,y\) must each lie in the span of \(h,L_4(c)\) there. Their two three-by-three determinants are computed with denominators cleared in [the replay](check_pair_one_silent.py). For the \(s\) fiber, remove the known forbidden values \(a,b,\xi\); \(s\ne a,b\) by the literal twin and \(s\ne\xi\) by (2). There is no \(L_4(s)=0\) fiber since \(h(s)\) and \(L_4(s)\) are coprime. At \(y\) remove the known forbidden values \(f,s,\xi\). The remaining polynomials are cubic and have exact gcd one in every one of the sixteen oriented quartic fibers, with all inverse coefficients explicitly checked. So no silent zero remains possible in the two-off-zero branch.

## Verification boundary

All scripts use Python and SymPy with exact quotient arithmetic over \(\mathbb Q[t]/(t^2-1/2)\). Fixing the front sign and checking both rear signs is exhaustive by conjugation. Each unit or division used in the polynomial checks is verified exactly; nothing assumes an ordering on the coefficient field. The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8HalfPairReceipts.lean) binds the literal two-tap conditions to (5) and checks its incompatibility with the five-site Hankel gate in the eight relative front/rear phases. The wider tableau reductions and the remaining eliminants are source-level, not a complete Lean nonexistence theorem. The all-active \(\ell=2\) possibility remains viable as far as these tests go.

### A concrete remaining gate

In the all-active endpoint-pair family, \(\boldsymbol h\) vanishes on the two off-zero rows and has nonzero values at the four distinct pegged zero clocks (both front and rear). Hence \(\boldsymbol h,C\boldsymbol h,C^2\boldsymbol h\) give three independent vectors restricted to \(U\). The restrictions of the third, fourth, and fifth shifted Legendre columns are also independent because there are at least six distinct zero clocks. Both triples belong to \(F_5|_U\): for the Legendre columns use \(F_5=\operatorname{Ann}(W_2)\) and the scalar orthogonality to degrees at most two. That space has dimension \(5\) by the restriction rank of \(W_2\), as its active off-zero rank is one. Therefore there are nonzero polynomials \(q,p\) with
\[
          \deg q\le2,\quad p\in\operatorname{span}(L_3,L_4,L_5),
          \qquad q(c_i)h_i=p(c_i)\quad (i\in U).
\]
This is a finite-degree rational interpolation restriction, not a license to divide through a zero of \(q\) and not yet an exclusion. The all-active family must also satisfy the rank-three \(F_4|_U\) constraints at all true chronological rows.
