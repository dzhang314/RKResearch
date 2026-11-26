# A fifth causal pivot keeps the high exceptional row on the arithmetic tail

For \(n\ge4\), a fifth causal pivot preserves the exceptional row and its two next contacts while keeping the word space through length three at dimension six.

## 1. Four true tail constraints on the high polynomial

Keep the four physical suffix clocks and their literal taps from FORCED-ARITHMETIC.md. Their normalized reflected clocks are
\[
 \beta_0=1,\qquad \beta_1=u,\qquad \beta_2=2u-1,\qquad \beta_3\ne u,
\]
where \(u,\beta_3\) both tend to \(0\) as \(g=-\gamma\) tends to infinity, and the first, second and fourth sites refer to genuine distinct physical clocks for finite \(g\). Let \(L_1=I_0^\beta-I\). For each of these four reverse columns define its **actual** compensated discrepancy on polynomials \(f\) by
\[
 \mathcal D_i f
   \coloneqq (L_1 f)(\beta_i)-\sum_{k<i} R_{i,k} f(\beta_k).
 \tag{1}
\]
The dimensionless \(R_{i,k}\) are the literal taps already placed in that column. Constants are in the common kernel by the first equation (2) of FORCED-ARITHMETIC.md.

The exact exceptional prefix gives two real rows \(v,w\) supported on the first \(j=n+2\) and \(j-1\) physical sites, with \(v_j\ne0\), and a true model \(P\) of degree at most \(r-2\). The target high equation is
\[
 v=b(P-J^*Q)(C)+bQ(C)T,\qquad vT=w.
 \tag{2}
\]
Write \(f(\beta)=Q(1-\gamma\beta)\) and \(\widehat P(\beta)=P(1-\gamma\beta)/\gamma\). On the four established suffix sites \(v=0\), so the first equation of (2) is precisely
\(\mathcal D_i f=\widehat P(\beta_i)\), \(i=0,\ldots,3\).

These four linear constraints have rank four already on the space of degrees at most four. Here is the exact confluent check. Let \(W(\beta)\) be the monic nodal hull of the first three normalized sites. The first three test taps annihilate \(W,\beta W\) as point evaluation inputs, and the fourth does also. Thus the last two columns of the discrepancy matrix on the basis \(\beta,\beta^2,W,\beta W\) are their shifted primitives. For the first two columns, (2) of FORCED-ARITHMETIC.md gives the exact values \(H_i/2,H_i K(\beta_i)\). Subtract the second row (site \(u\)) from the fourth and divide by \(\beta_3-u\). This has a continuous limit as \(u,\beta_3\to0\): the fourth-site rational formula \(H=N/A\) is analytic there and agrees with the second row at \(\beta=u\). In the limit \(W=\beta^3-\beta\), \(H(0)=2\), \(H'(0)=-10\), and \(K=(\beta+3)/6\). The matrix tends to
\[
 \begin{pmatrix}
 -1/2&-2/3&-1/4&-2/15\\
 1&1&0&0\\
 17/2&17/3&-1/4&2/15\\
 -5&-14/3&1&0
 \end{pmatrix},
 \qquad \det=-17/45 .
\]
This proves exact nonzero rank for all sufficiently large finite \(g\). It uses divided differences of genuinely distinct physical sites; no duplicated control column is used.

## 2. A homogeneous direction gives a real fifth pivot

Set \(s=r-3=2n-2\ge6\). We construct a monic degree-\(s\) polynomial in the homogeneous kernel of the four actual constraints whose effect on the fifth pivot can be certified. In the same confluent limit, let \(I(\beta)=\beta^2-\beta\) be the quadratic interpolant at \(1,0,-1\). Seek
\[
 f_\infty=I+(\beta^3-\beta)S,\qquad
 S(\beta)=\beta^{s-3}+s_2\beta^2+s_1\beta-1/3.
\]
Its discrepancy at \(\beta=0\) is zero because \(I(1)=I(0)\). The derivative of that discrepancy is zero because \((f_\infty-I)'(0)=1/3\). Specifically, for a degree-two interpolant with coefficients \(I_1,I_2\), the local formula for the discrepancy at the variable fourth site is
\[
 L_1(f_\infty-I)(\beta)+H(\beta)\,[I_1/2+I_2(\beta+3)/6].
\]
Here the derivative at zero is minus that first derivative plus \(1/3\). The remaining two homogeneous equations at \(1,-1\) prescribe \(\int_0^1(f_\infty-I)\) and \(\int_0^{-1}(f_\infty-I)\). The \(s_1\) and \(s_2\) columns in those two equations are independent: \(\int_0^1 (\beta^3-\beta)\beta^k=-2/[(k+4)(k+2)]\ne0\), and the reversed integral at \(-1\) is this value multiplied by \((-1)^k\). Thus exact \(s_1,s_2\) exist. For nearby finite sites correct \(f_\infty\) by a polynomial of degree at most four to solve the actual four homogeneous equations. The invertible normalized constraint matrix from Section 1 shows that this correction tends to zero. Denote the resulting monic degree-\(s\) homogeneous polynomial by \(f_R\).

For a general polynomial \(f\), interpolate its actual measured values on the first four sites in the form
\[
                  f(\beta_i)=A_f(\beta_i)+c_f H_i,\qquad \deg A_f\le2.
 \tag{3}
\]
This is a true four-coordinate invertible representation by the already proved pivot. Its coefficients have continuous confluent limits by subtracting the second site from the fourth and dividing by their difference. To compute them for \(f_R\), the limiting first three \(H\) values have quadratic interpolant \(I_2=6\beta^2-9\beta+2\). The derivative difference is
\(H'(0)-I_2'(0)=-1\), while \(f_\infty'(0)-I'(0)=1/3\). Therefore \(c_{f_R}\to-1/3\) and \(A_{f_R}\to I+\tfrac13 I_2\), whose linear and quadratic coefficients are \(-4,3\).

For a new column with normalized clock \(\beta\), using the four existing sites as its taps, the exact low equations give
\[
 L_1f(\beta)-R\!\cdot f
      = L_1(f-A_f)(\beta)+H K_f(\beta),\qquad
 K_f(\beta)\coloneqq (A_f)_1/2+(A_f)_2K(\beta)
                                     -c_f(\beta-1)/\kappa .
 \tag{4}
\]
Indeed substitute (3) into the four paid moments. For \(f=f_R\), \(K_f\) tends to \((\beta-1)/3\) by the coefficients just computed.

Choose an inhomogeneous solution \(f_0\) of degree at most four of Section 1 and put \(f=f_0+\eta f_R\). Avoid \(\eta=0\) and any value making \(K_f\) identically zero. This removes only finitely many choices. Define the polynomial
\[
 \Gamma_f(\beta)
    \coloneqq (f-A_f)K_f-c_f\bigl(\widehat P-L_1(f-A_f)\bigr).
\]
We can also insist \(\Gamma_f\not\equiv0\). The degree is at most \(s+1\), and its coefficient in that degree is quadratic in \(\eta\). Its quadratic coefficient is
\[
   [\beta]K_{f_R}+c_{f_R}/(s+1)
       \longrightarrow \frac{s}{3(s+1)}\ne0 ,
\]
because \(f_R\) is monic and \(\deg\widehat P\le s+1\). Thus at most two additional choices are forbidden for sufficiently large finite \(g\). Take algebraic \(\eta\) avoiding them. The polynomial \(\Gamma_f\) has its four already established zeros at the actual first four sites, because both their compensated constraints and their interpolation values hold there.

Choose a fifth distinct interior site \(\beta_4\) avoiding the roots of \(K_f,\Gamma_f\). There are enough moving interior sites: \(K_f\) is affine and \(\Gamma_f\) has at most \(s-3\) additional zeros, and the scalar grid provides \(q=n^2+n-4\) moving sites before allocating the fourth and fifth slots. Now set
\[
 H_4=\frac{\widehat P(\beta_4)-L_1(f-A_f)(\beta_4)}
                           {K_f(\beta_4)} .
\]
Use the four already paid taps in (2) of FORCED-ARITHMETIC.md for this new \(H_4\); (4) makes its high compensation exact. Here
\(f(\beta_4)-A_f(\beta_4)-c_f H_4=\Gamma_f(\beta_4)/K_f(\beta_4)\ne0\).
Therefore the five actual input rows \(b,bM,bM^2,h,bQ(C)\) are independent on these five **physical** sites. The common row scales \(\gamma\) and the actual \(b_i\ne0\) do not change the rank.

## 3. Real common taps and scope

Prescribe \(h_i=\gamma^2 b_i H_i\) at the measured five suffix sites. On the other \(d-5\) actual sites solve for \(h\) annihilating \(D\mathbb P_{\le p-5}\). There are \(p-4=4n-1\) moments against \(d-5\ge4n-1\) distinct non-anchor sites in this range. At each earlier column there are now five actual simultaneous equations: the four low equations (1) of FORCED-ARITHMETIC.md and the first high equation in (2). Their right sides are known after choosing \(h\) and the retained \(v\). Before using the five suffix pivots, set earlier physical taps within the exceptional prefix so \(vT=w\), possible because \(v_j\ne0\) and \(w\) has the shorter support. The suffix retaps cannot affect that row product. All other off-pivot taps may likewise be fixed first, and then one invertible five-tap solve per column realizes **every** displayed equation on the same strict matrix.

The actual \(v\) is a word combination through \(r-2\) by (2) and \(\deg Q=s=r-3\). Its true next strict contact is \(w\); its next mark is paid by its actual prefix moments with one smaller degree budget. The grade-three word space is exactly six-dimensional and fully paid as in FORCED-ARITHMETIC.md. Attach the usual literal earlier taps to preserve true clocks and local order. This proves full rooted order **at least \(m+3\)** and keeps the genuine high prefix on the required arithmetic suffix. Through order \(20\) the joint construction applies to the order-19 geometry and proves actual rooted order at least \(13\), not order 19. It changes the previously excluded scalar grid, uses the required maximal compensation degree, and avoids the prior rank-eight grade-three obstruction. The grade-four and higher mixed constraints and any unrestricted stage improvement remain unknown.
