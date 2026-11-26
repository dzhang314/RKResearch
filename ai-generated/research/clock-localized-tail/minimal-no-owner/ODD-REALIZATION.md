# Two real exceptional prefixes and a literal paid row pair

This realizes an exceptional row and its next two contacts in the minimum-width late block, together with the required scalar quadrature and first reverse primitive. The [generic prefix obstruction](LOWER-CUT.md) remains valid. The construction does not establish the entire lower dictionary or the target order.

## 1. Exact moment determinant and its first Taylor coefficients

Let \(r=2n+1\), \(n\ge2\), \(m=r+1\), \(p=2r+1\). The minimum late width and prefix length are
\[
 d\coloneqq L(r)=(n+1)^2,\qquad j\coloneqq n+2.
\]
Use the actual even-\(m\) repaired earlier bank from ACTUAL-DOUBLE.md. Its distinct negative anchors are \(\alpha,a\), and \(D(X)\coloneqq(X-\alpha)(X-a)\). Set \(J=I_0-\gamma I\), \(J^*=I_1-\gamma I\) and \(\ell=\int_0^1\). These are respectively the lower and upper shifted polynomial primitives and integration over the order interval.

Choose \(\gamma=-g<0\), with \(g\) to be made large, and negative preceding prefix clocks \(x_1,\ldots,x_{j-1}\). In the scaled variable \(U=X/g\), put
\[
 G_0(U)\coloneqq\prod_{i=1}^{d_G}(U+\rho_i),\qquad d_G\coloneqq n+3,
\]
where the \(\rho_i>0\) are the magnitudes of the two actual anchors and the \(j-1\) preceding clocks in that variable. They are distinct, and can all be chosen arbitrarily close to \(\lambda\), the fixed positive normalised final Laguerre root of the admissible earlier bank. The repaired sampler's normalised \(a\) has only finitely many forbidden choices, and all its conditions are invariant under the common physical scaling \(X=gU\). Thus it can be chosen close to, but different from, the old anchor; the remaining \(\rho_i\) are freely chosen distinct algebraic positives near \(\lambda\).

Let \(z=x_j\) and \(\zeta=z/g\). The actual finite prefix gate is
\[
 \ell(P\, G(X)(X-z)Q)=\ell(P\,J(GQ))=0,\quad
 \deg Q\le n-1,\quad 0\ne P\in\mathbb P_{\le2n-1},
 \qquad G(X)\coloneqq D(X)\prod_{i<j}(X-x_i).
 \tag{1}
\]
After changing variables to \(U\) and rescaling nonzero factors, its determinant is the dual moment matrix on \([0,\epsilon]\), \(\epsilon\coloneqq1/g\), for the \(2n\) functions
\[
 f_i(U)\coloneqq(U-\zeta)U^i,\qquad
 k_i(U)\coloneqq U^i+\frac{1}{G_0(U)}\int_0^U G_0(V)V^i\,dV,
 \qquad 0\le i<n,
\]
against \(U^aG_0(U)\), \(0\le a<2n\). The diagonal shift is \(+1\) in this scaled variable because \(\gamma=-g\).

After a nonzero normalisation independent of \(\zeta\), this determinant converges coefficientwise as \(\epsilon\) decreases to zero to the determinant of the Taylor coefficients of these functions in degrees \(0,\ldots,2n-1\). To see this, first substitute \(U=\epsilon t\) and divide moment row \(a\) by \(\epsilon^{a+1}\). With \(F_i=G_0 f_i,G_0 k_i\) the actual polynomial test columns, the resulting matrix has leading expression \(H\,\operatorname{diag}(\epsilon^l)\,C\), where \(H_{a,l}=1/(a+l+1)\) is the \(2n\) square Hilbert matrix and \(C_{l,i}=[U^l]F_i\). Terms of degree at least \(2n\) give an error \(O(\epsilon^{2n})\) coefficientwise. Multiplying by \(\operatorname{diag}(\epsilon^{-l})H^{-1}\) makes that error \(O(\epsilon)\). Finally multiplication by \(G_0\) is an invertible triangular transform on these Taylor coefficients because \(G_0(0)\ne0\). This is a limit of exact finite determinants, not an approximate tableau acceptance criterion.

## 2. A positive discrete orthogonality problem supplies the roots

Put \(\Theta\coloneqq G_0'/G_0=\sum_i 1/(U+\rho_i)\). A combination of the \(k_i\) with input \(Q\in\mathbb P_{\le n-1}\) can lie in the \((U-\zeta)\mathbb P_{\le n-1}\) span in the Taylor test only when its Taylor coefficients at degrees \(n+1,\ldots,2n-1\) vanish. Write its primitive part through degree \(n\) as \(L\). The condition is equivalently
\[
 L(0)=0,\qquad Q=L'+[\Theta L]_{\le n-1},\qquad
            [U^k](\Theta L)=0\quad(n\le k\le2n-2).
 \tag{2}
\]
Indeed differentiate \(G_0 L-\int_0^U G_0Q=O(U^{2n})\), divide by \(G_0\) and compare coefficients; conversely integrate that resulting equivalence, using \(L(0)=0\). The map \(L\mapsto Q\) is injective: the first nonzero term of \(L'\) has degree one below the first nonzero term of \(L\), and cannot be cancelled by \(\Theta L\).

Write \(L(U)=U B(U)\) and \(S(Z)\coloneqq Z^{n-1}B(-1/Z)\). For \(s_i\coloneqq1/\rho_i\), the last conditions of (2) are exactly
\[
 \sum_i s_i S(s_i)s_i^l=0,\qquad 0\le l\le n-2.
 \tag{3}
\]
Indeed the polynomial part of \(\Theta L\) has degree at most \(n-1\); its residue at \(-\rho_i\) is \(L(-\rho_i)=-s_i^{-n}S(s_i)\). The degree-\(k\) Taylor coefficient of the remaining pole is \((-1)^{k+1}S(s_i)s_i^{k+1-n}\). This gives (3).

The positive masses \(s_i\) on distinct positive sites make (3) the unique degree-\((n-1)\) orthogonal polynomial up to scale. It has \(n-1\) simple roots strictly between the extreme sites, by the usual sign-change proof for positive discrete orthogonality. In particular \(B\) has degree \(n-1\) with simple negative roots between the extreme \(-\rho_i\). Normalise \(L\) to be monic. The admissible \(Q\)'s form a line by (2) and (3), so the first \(2n\) Taylor determinant is a nonzero scalar times
\[
 H_0(\zeta),\qquad H_0(U)\coloneqq L(U)+L'(U)+[\Theta L(U)]_{\le n-1}.
 \tag{4}
\]
For detail, the \(k_i\) map onto the \(n-1\) high Taylor coefficients with one-dimensional kernel. After eliminating those coefficients, their remaining column is the degree-\(n\) polynomial \(H_0\). The other \(n\) columns span exactly the degree-\(\le n\) polynomials vanishing at \(\zeta\), with unit leading pivots in degrees \(1,\ldots,n\). Their determinant with \(H_0\) is therefore a constant sign times \(H_0(\zeta)\).

As the distinct \(\rho_i\) cluster at \(\lambda\), the roots just identified give \(L(U)\longrightarrow U(U+\lambda)^{n-1}\) and \(\Theta\longrightarrow d_G/(U+\lambda)\) in Taylor coefficients near zero. Formula (4) thus tends to
\[
 (U+\lambda)^{n-2}\bigl(U^2+(\lambda+n+d_G)U+\lambda\bigr).
 \tag{5}
\]
The quadratic is positive at \(0\), negative at \(-\lambda\) (its value is \(\lambda(1-n-d_G)\)), and positive near negative infinity. It has two simple distinct negative roots on opposite sides of \(-\lambda\), separated from it. Choose disjoint negative intervals strictly away from \(-\lambda\) around them with signs changing and nonzero derivative. For sufficiently close but distinct real-algebraic \(\rho_i\), and then sufficiently large finite algebraic \(g\), the actual determinant has one simple real root in each interval by coefficientwise convergence and the intermediate value theorem. These are real algebraic clock choices; neither can coincide with an anchor or any of the preceding negative prefix clocks. At either root the finite matrix in (1) has nullity exactly one: any smaller rank would make every first cofactor, and therefore the derivative of the determinant, zero. Use a nonzero actual algebraic \(P\) on this line.

## 3. Actual support, moments and next paid contacts

The exact nodal-hull test (1) gives unique actual rows \(v,w\), supported respectively on the first \(j\) and first \(j-1\) sites, with
\[
 v E(DQ)=\ell(PDQ)\quad(\deg Q\le m-1),\qquad
 w E(DQ)=\ell((J^*P)DQ)\quad(\deg Q\le m-2).
 \tag{6}
\]
This is ordinary polynomial evaluation duality on distinct actual sites with \(D(x_i)\ne0\). The kernels are the two nodal hulls multiplied by \(\mathbb P_{\le n-1}\), exactly the tests in (1); thus no untested representative of the numerical data is assigned. The entry \(v_j\ne0\): otherwise the first identity would give \(\ell(PGQ)=0\) through degree \(n-1\), and the second gives \(\ell(PJ(GQ))=0\) there. The full-rank limiting sign lemma in LOWER-CUT.md applies to these very equations at the fixed negative roots of \(G\), and forces \(P=0\). Also \(w\ne0\) by testing the second identity with \(Q=J^*P\), whose degree is at most \(m-2\), and using \(D>0\) and \(J^*P\ne0\). Thus the actual supported rows are independent. This is not just a formal determinant root.

Choose a scalar quadrature on the full \(d\) sites as follows. Pin the \(j\) distinct negative prefix clocks and the compulsory final physical clock \(z_*\coloneqq1-\gamma>1\). Let \(q\coloneqq d-j-1=n^2+n-2\) and fill the remaining sites with the \(q\) roots in \((0,1)\) of the monic orthogonal polynomial for the positive weight given by the absolute value of the exterior nodal hull. The interpolation weights \(b_i\) on all \(d\) clocks integrate through degree \(d+q-1\ge p-1\), by division by the full nodal hull and the orthogonality of that interior factor. Every weight is nonzero. At an interior site isolate its weight using the exterior hull times the square of the interior nodal hull with that site omitted. At an exterior site isolate its weight with the remaining exterior factors times the full squared interior hull. In each case the degree fits the scalar rule, the polynomial at the selected site is nonzero, and the integral has strictly constant sign on \([0,1]\) except at zeros. These weights and clocks are algebraic.

We now make \(v\) and \(w\) actual word rows of a literal strict lower \(T\), while also paying
\[
                    bT=b(z_*I-C),
 \tag{7}
\]
where \(C\) is the actual clock diagonal. One can choose the penultimate clock \(y=x_{d-1}\) among the \(q\) interior sites so that a quadratic \(Q_*\) satisfies
\[
 Q_*(z_*)=1,\qquad (J^*Q_*)(z_*)=P(z_*),\qquad
 (J^*Q_*)(y)-(z_*-y)Q_*(z_*)=P(y),\qquad Q_*(y)\ne1.
 \tag{8}
\]
Put \(s=z_*-y>g\) and write \(Q_*(X)=1+A(X-z_*)+B_*(X-z_*)^2\). In (8), the two equations for \(A,B_*\), after subtracting the first evaluation from the second as needed, have determinant \(g^2s(s^2+2gs-2g^2)/6>0\). Explicitly the first linear coefficients are \(g^2/2,-g^3/3\), the second after subtraction are \(-s^2/2-gs,\ s^3/3+gs^2\). If \(Q_*(y)=1\), then \(A=sB_*\), and the two equations force
\[
 g^2(3s-2g)\bigl(P(z_*)-P(z_*-s)\bigr)-P(z_*)s^3=0 .
\]
This polynomial in \(s\) is not identically zero: at \(s=2g/3\) an identity would make \(P(z_*)=0\), which then gives \(P=0\). Its degree is at most \(2n\) and it vanishes at zero. Thus at most \(2n-1\) interior sites can be disallowed. Since \(q>2n-1\), a \(y\) satisfying (8) exists.

Choose the physical rows of \(T\) through index \(d-2\), initially arbitrarily except that row \(j\) is assigned so \(vT=w\); this is possible on strictly earlier taps because \(v_j\ne0\), and neither of the last two rows can affect it. Put \(A_0\coloneqq P-J^*Q_*\). Solve the last two rows columnwise to impose (7) and
\[
                      b A_0(C)+b Q_*(C)T=v .                 \tag{9}
\]
At the final column both desired equations are zero. At column \(d-1\) the unique strict tap set by (7) is \(T_{d,d-1}=s b_{d-1}/b_d\); (9) is then precisely the second physical-clock clause of (8). At every earlier column the last two tap coefficients solve a \(2\) square system with determinant \(b_{d-1}b_d(Q_*(z_*)-Q_*(y))\ne0\). This is one literal strictly lower matrix.

Attach its real earlier taps \(EJD'-TED'\) from the repaired earlier decoder \(D'\). The actual clocks are preserved and the late bank is genuinely locally exact through \(m\), as in ACTUAL-DOUBLE.md. Equation (9) gives \(v\) as an actual linear combination of word rows of length at most \(r-2\) (the degree of \(A_0\) is at most \(r-2\), and \(Q_*\) has degree two). Its true formal model is \(P\). The actual \(vT=w\) satisfies its entire next double-factor band by (6). The actual \(vC\) does too, by inserting \(XQ\) in the first equation of (6) with degree budget \(m-1\). Equation (7) additionally pays the first primitive followed only by marks through the scalar budget. This is a real physical channel with both next operations, not two independently chosen formal covectors.

Through \(20\), the applicable balanced odd targets are \(11,15,19\). These constructions have not paid the complementary mixed lower-word channels or final feeder, and are not stage table entries. They are exact candidates through a previously obstructed necessary gate; they do not prove that it is possible to realize the whole minimum dictionary on either candidate prefix.
