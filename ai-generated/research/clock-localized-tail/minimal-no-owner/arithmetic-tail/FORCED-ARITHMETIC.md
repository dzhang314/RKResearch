# The arithmetic tail with a negative third reverse clock is physically possible

An exact scalar rule and a minimal word space through length three for the mixed-sign arithmetic tail. The ordinary rooted order proved below is smaller than the order that specifies the geometry.

## 1. An exact scalar rule on the required mixed grid

Let \(r=2n+1,\ n\ge2,\ m=r+1,\ p=m+r\), \(d=(n+1)^2\), and keep either actual simple exceptional negative prefix of length \(j=n+2\) from [the odd exceptional-prefix construction](../ODD-REALIZATION.md). Choose the large diagonal magnitude in that construction so \(g\coloneqq-\gamma>1\) is as large as needed below. Write \(z\coloneqq1-\gamma=1+g\). Choose an interior physical clock \(y>0\) sufficiently close to zero and impose the actual final three physical clocks, in reverse order,
\[
            z,\qquad y,\qquad c\coloneqq2y-z .
\]
Thus \(c<0\), on the branch with a nonzero adjoining tap. Exclude the finitely many \(y\)'s causing equality of \(c\) with an old clock or either early anchor \(\alpha,a\). The prescribed exterior set consists of the \(j\) exceptional clocks, \(c\) and \(z\). Denote its monic nodal hull by \(H_{\rm ext}(X)\). Its sign is constant on \([0,1]\); the polynomial \(W_{\rm ext}\coloneqq-H_{\rm ext}\) is positive there.

Besides the single pinned interior clock \(y\), use
\[
           q\coloneqq d-j-3=n^2+n-4
\]
additional nodes, the roots of the monic degree-\(q\) polynomial orthogonal through degree \(q-1\) for \((X-y)W_{\rm ext}(X)\,dX\). At \(y=0\) this is an ordinary positive weight on \((0,1)\). Its finite Gram matrix is nonsingular, and its monic orthogonal polynomial has \(q\) simple distinct interior roots. Small \(y>0\) preserves invertibility and the real simple interior roots by continuity, even though the weight becomes signed close to zero. The roots stay distinct from the pinned \(y\). If two prescribed exterior clocks happen to coincide at \(y=0\), the same positive limiting polynomial weight still works; choose \(y>0\) avoiding the finite collisions before using actual interpolation.

The interpolation weights on all \(d\) distinct sites integrate through degree \(d+q-1\ge p-1\). Indeed division by their full nodal hull leaves the interpolating polynomial of degree at most \(d-1\); the quotient term integrates to zero through that degree by the displayed orthogonality. Every weight is nonzero for sufficiently small \(y>0\). At a moving interior node isolate its mass by \(H_{\rm ext}(X)(X-y)\) times the square of the product of all other moving factors. At the pinned \(y\) use \(H_{\rm ext}\) times the full squared moving hull. At an exterior site omit its exterior factor and use \((X-y)\) times the full squared moving hull. Each test has degree at most \(d+q-1\); at \(y=0\) its integral has strict sign by positivity up to an overall sign. This nonzero numerator persists for small \(y>0\), while its value at the tested clock is then nonzero by distinctness. Algebraic \(y>0\) can meet all the conditions, making the moving roots and every weight algebraic. All weights refer to literal scalar quadrature support; no later-stage output order follows from this alone.

## 2. Actual grade-three identities and the first four reverse pivots

Put
\[
  Y=1-X,\quad M=\operatorname{diag}(1-x_i),\quad
  L=I_0^Y-\gamma I,\quad D(X)=(X-\alpha)(X-a).
\]
Let \(b\) be the exact scalar weight row. A minimally ranked grade-three dictionary can be realized using an actual row \(h\) and these four simultaneous strict tap equations:
\[
 \begin{aligned}
 bT&=b(M-\gamma I),\\
 bMT&=b(LY)(M)-h/2,\\
 bM^2T&=b(LY^2)(M)
          -h\bigl(M+\gamma I+(M-\gamma I)/\kappa\bigr)/3,\\
 hT&=\kappa^{-1}h(M-\gamma I).
 \end{aligned}                                                   \tag{1}
\]
The scalar \(\kappa\ne0\) will be defined at the actual penultimate clock. When (1) is realized on one literal matrix, each actual word of length \(k\le3\) has form \(bP(M)+hQ(M)\), where \(P\) is its exact formal polynomial and \(\deg Q\le k-2\) (zero if \(k<2\)). This follows directly by marking and by primitive action on \(b,bM,bM^2,h\); the formal model of \(h\) is zero. In particular the actual rank of \(V_3\) is at most six. One can also check the grade-three identities explicitly: \(h=b\Omega\) where
\(\Omega=(T+\gamma I)M-M(T+\gamma I)-(T+\gamma I)^2\). Writing \(q_0=bT\), the three genuine zero-model combinations in §4 of no-owner-active-tail-rigidity have rows \(0,(\kappa-1)q_0\Omega,\kappa q_0\Omega\) in the order \(\tau,\rho,\sigma\). For example \(\sigma=h(M-\gamma I)\) and \(q_0\Omega-hT=\tau=0\) by the four equations. Thus (1) enforces minimal relations and not merely their polynomial projections.

Use the normalised variable \(\beta=Y/\gamma\); for a reverse column at physical index \(i\) let \(H_i=h_i/(b_i\gamma^2)\) and denote its dimensionless tap from an already earlier reverse site \(k\) by \(R_k=T_{ki} b_k/(\gamma b_i)\). Then (1) is the actual system
\[
 \begin{aligned}
 \sum R_k&=\beta-1,\qquad
 \sum R_k\beta_k=\beta^2/2-\beta-H/2,\\
 \sum R_k\beta_k^2&=\beta^3/3-\beta^2-H K(\beta),\qquad
 \sum R_k H_k=H(\beta-1)/\kappa,\\
 K(\beta)&\coloneqq \bigl(\beta+1+(\beta-1)/\kappa\bigr)/3.
 \end{aligned}                                                   \tag{2}
\]
Here a reverse column has taps from physically later stages. The first three normalised clocks are \(1,u,2u-1\), where \(u=(1-y)/\gamma\) lies in \((-1/g,0)\). Put
\[
 \delta\coloneqq u-1,\qquad
 H_0=-1,\qquad H_1=u^2-4u+2,\qquad \kappa=-H_1 .
\]
At the first site there are no taps, at the second the unique tap is \(\delta\), and (2) holds at each by substitution. At the third, take
\[
 R_1=\frac{2\delta(3\delta-2)}{-\delta^3+4\delta^2+\delta-2},
 \qquad R_0=2\delta-R_1,\qquad
 H_2=4\delta^2-4\delta-1-2\delta R_1.                         \tag{3}
\]
The formula solves the first, second and fourth equations. To check the third, multiply its difference by \(3\) and use the fourth equation in the form
\(2\delta H_2/\kappa=-2\delta+\delta(\delta-2)R_1\). The difference reduces to
\[
 -2-10\delta+8\delta^3-2(4\delta^2-4\delta-1)(1+\delta)=0 .
\]
For \(u\) near zero all denominators in (3) are nonzero; at \(u=0\) the third tap \(R_1\) is \(5\). Hence this really has a nonzero physical tap between the penultimate and antepenultimate stages.

Let \(I_2(\beta)\) be the quadratic interpolant of \(H_0,H_1,H_2\) at the first three sites. At a fourth site the first three equations of (2) determine its three taps for any proposed \(H\), by an ordinary Vandermonde invertible system. Their fourth equation becomes
\[
                 A(\beta)H=N(\beta),
\]
where \(A\) is affine and \(N\) is cubic, found by applying those moments to \(I_2\). Coefficients vary continuously with \(u\) near zero. At \(u=0\) the sites and values are \(1,0,-1\) and \(-1,2,17\), so
\[
 I_2=6\beta^2-9\beta+2,\quad
 A=(\beta-2)/2,\quad
 N=2\beta^3-\tfrac{21}{2}\beta^2+11\beta-2,\quad
 N-A I_2=-\beta(\beta-1)(\beta+1).
\]
For nearby \(u\), \(N-A I_2\) still has nonzero cubic coefficient, and vanishes at exactly the first three distinct sites because their actual taps already solve (2). Any next distinct interior site gives a normalised \(\beta\) near zero with \(A(\beta)\ne0\). Set \(H=N/A\) there. Its residual from \(I_2\) is nonzero, so the four input functions \(1,\beta,\beta^2,H\) have full measured rank on the first four physical suffix sites. Thereafter (2) has a single literal four-tap solve at each earlier column, for any assigned \(H\); other available taps can first be set freely and included on its right side.

## 3. Lower rooted order and exact minimal grade-three rank

Take a requested order window \(p'\le p\) with \(p'\ge m+3\). The entire true word band through length three at that window is paid if the actual hidden row \(h\) annihilates
\[
                         D\,\mathbb P_{\le p'-5}.
\]
For a length-\(k\) word, the \(hQ(M)\) read then vanishes on \(D\mathbb P_{\le p'-k-3}\) because \(\deg Q\le k-2\); the polynomial part is integrated by the scalar rule. On \(d-4\) free actual sites the Vandermonde moment solve can impose these \(p'-4\) equations after freezing the four \(H\)'s, provided \(d-4\ge p'-4\). This works at the full stated lower-word budget \(p'=p\) for \(n\ge3\). At \(n=2\), use \(p'=m+3=9\), where equality of the counts holds. All \(D(x_i)\) are nonzero. Attach the true late rows to the known repaired earlier decoder by \(EJD'-TED'\); this preserves the clocks and gives true local order through \(m\). Because the actual early-source residual has double factor \(D\), the single-large-child spine argument then gives full rooted order through \(m+3\).

There are exactly six independent numerical rows through word length three, not eight. The displayed identities give the upper bound. For the lower bound, the exact weighted contacts make the reverse model map well defined through three by the positive pairing of \(D\) times a polynomial against itself; the tested band through that grade contains its square test because \(p'\ge9\). The ordinary commutator \(\Omega\) is invertible and sends both rows in \(V_1\) to model-zero rows of grade three; these add to its four independent monomial models. This proves the claimed measured rank. The separate high row \(v\) from the prefix determinant is not yet asserted to be a word row for this four-tap matrix; PAID-HIGH-PIVOTS.md supplies that joint realization when its higher-degree freedom is available.
