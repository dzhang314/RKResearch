# No coprime simple pole in the all-active half-diagonal endpoint pair

In the [all-active half-diagonal family](../sdirk-eight-half-equal/README.md) of ten-stage strict SDIRK8, the only nonzero quadratic residuals are \(g_1=g_{10}=1/8\), at \(c_1=c_{10}=\gamma=1/2\), and \(b_1=-b_{10}\). Let \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). Under the rational reduction
\(q(c_i)h_i=p(c_i)\) on the eight zero rows, \(p\in\operatorname{span}(L_3,L_4,L_5)\), this packet excludes **every coprime linear \(q\)** over a characteristic-zero field. This upgrades the [previous finite-pole reduction](../sdirk-eight-half-rational/README.md) to an exact exclusion. It also excludes the coprime double central pole \(q=(X-1/2)^2\), and proves a proper algebraic locus (not a full parameter plane) for generic quadratic denominators. No common-factor chart is excluded by canceling a factor. The unrestricted order-eight interval remains **10–11**.

## 1. Cleared moments for a general simple pole

Normalize \(q=X-\xi\). Work over \(\mathbb Q(t)\), \(t^2=1/2\), for the known front/rear coefficients. The two front site values and the rear ratio determine \(p\) through the [corner system](../sdirk-eight-half-rational/README.md); its singular value is inconsistent. Let \(\Delta(\xi)\) be its nonzero determinant and \(\widetilde p=\Delta p\) its Cramer numerator. Set \(v=[X^5]\widetilde p\ne0\), \(r=\widetilde p(\xi)\ne0\), and write
\[
      \widetilde p=(X-\xi)S+r,\qquad
      S=(X-\xi)S_3+\sigma,\qquad XS=(X-\xi)U_4+\xi\sigma .
\]
Coprimality and the prior degree guard justify \(v,r\ne0\). Write \(I_{<8}\) for ordinary integration of terms of degrees zero through seven only. The following four scalar numerators give precisely \(\ell(X^8)=A_8/v,\ \ell(1/q)=B_1/r,\ \ell(1/q^2)=B_2/(v r^2),\ \ell(X^9)=A_9/v^3\):
\[
\begin{aligned}
 A_8&=-I_{<8}(X^3\widetilde p), & B_1&=-I(S),\\
 B_2&=-\{v I_{<8}(S^2)+v^2 A_8+2rv I(S_3)+2v\sigma B_1\},\\
 A_9&=-\{v I_{<8}(XS^2)+[X^8](XS^2)A_8
               +2rv I(U_4)+2v\xi\sigma B_1+v r B_1+\xi B_2\}.
\end{aligned}
\]
Indeed the scaled trace \(\widetilde p/q\) equals \(\Delta h\) on zero rows. Use the four paid moments \(\ell(h)=0,\ell(hX^4-\xi hX^3)=0,\ell(h^2)=0,\ell(Xh^2)=0\), and the identities \(S/q=S_3+\sigma/q\), \(X/q^2=1/q+\xi/q^2\). Thus all these expressions use ordinary moments only through seven plus the paid pure equations.

For a test polynomial \(f\) of degree at most eleven, divide by \(q^2\), with quotient \(V\) of degree at most nine and remainder \(V_0+V_1(X-\xi)\). Then the common scaled moment
\[
 \mathcal T(f)=v^3r^2 I_{<8}(V)+v^2r^2 A_8[X^8]V+r^2 A_9[X^9]V
                   +v^2B_2V_0+v^3r B_1V_1
\]
equals \(v^3r^2\ell(f/q^2)\). It is polynomial in \(\xi\) over \(\mathbb Q(t)\). The Cramer numerator of the literal fourth-row compatibility is the polynomial
\[
                        F(X)=\Delta q(X) H_{\rm tap}(X)-\widetilde p(X),
\]
where \(H_{\rm tap}\) is the genuine cubic of the [earlier three-tap calculation](../sdirk-eight-half-rational/README.md). No operation in this step divides by a potentially vanishing physical clock gap.

## 2. Seven ordinary sites: exact rational fibers

By the earlier profile result there are seven or eight active distinct ordinary sites. Let \(a,b,c,d\) be the two front and actual two rear zero clocks, \(P_4=(X-a)(X-b)(X-c)(X-d)\), and \(T_j=\mathcal T(P_4 X^j)\). The monic factor of the other three nodes has a kernel coefficient vector in the four-by-four matrix \([T_{i+j}]_{i,j=0}^3\). Its three-by-three principal submatrix is nonsingular by signed Vandermonde, so its ordinary Cramer cubic scaled by this determinant is \(Q_c\).

The [exact seven-site replay](check_seven_sites.py) computes the four-by-four determinant, then repeatedly removes common factors with the known nonzero guards \(\Delta,v,r,\prod_{e\in\{a,b,c,d\}}(\xi-e)\) and the principal determinant. The remaining squarefree polynomial in \(\xi\) has degree three in all six distinct relative phases (a reflected star pair does not change by switching its root sign). The rear evaluations \(F(c),F(d)\) are coprime to that polynomial. In every remaining cubic fiber, \(F\) and \(Q_c\) have gcd one. All inverses used by fiber Euclid are checked; a nonunit leading coefficient, if found, splits the fiber rather than being divided through. Since the fourth clock is neither \(a\) nor \(b\) by the literal twin argument, there is no permissible value for it.

## 3. Eight ordinary sites: exact row-four projection

Now all eight physical zero rows have different clocks and nonzero weights. Use the four-by-four principal matrix \([T_{i+j}]_{i,j=0}^3\), nonsingular by signed Vandermonde on the four noncorner sites, to construct the Cramer-scaled quartic \(Q_c(X)\). Row four is a noncorner zero, so \(F,Q_c\) have an actual common root \(s\). We remove common content from their coefficient lists only by factors of the exact nonzero guards (and use the reduced nonzero leading coefficient of \(Q_c\)). The [eight-site replay](check_eight_sites.py) then forms their resultant by fraction-free elimination, strips those guarded factors, and makes the projection squarefree. Its degree is fifteen in the same-phase matched case, sixteen in the remaining mixed cases.

Recover \(s\) uniformly without factoring into numerical roots. Make the seven columns of coefficients of \(X^i F\) for \(i=0,1,2\) and \(X^j Q_c\) for \(j=0,1,2,3\); the six rows of degrees \(2,\ldots,7\) define a cofactor vector. Its signed combination of columns is a polynomial \(A_1(\xi) X+A_0(\xi)\) vanishing at any true common root. The two coefficients are just the determinants obtained by appending the degree-one or degree-zero row, respectively. The replay verifies \(A_1\) coprime to the squarefree projection. Hence \(s=-A_0/A_1\). Removing the exact factors on which \(s=a\) or \(s=b\) deletes six degrees in every phase; these roots would be literal twins of an earlier zero row. The remaining pole factor \(M(\xi)\) is monic, squarefree, degree nine or ten. No other projected roots are discarded.

## 4. Literal row five and a finite-quotient unit certificate

All weights are active here. The three restrictions \(\boldsymbol h,C\boldsymbol h,L_4(\boldsymbol c)\) span the rank-three pure \(F_4|_U\): the front pair detects independence of \(h,L_4\), and a relation involving \(C h\) would give the incompatible front/rear poles in the half-diagonal proof. Thus the pure column \(A\boldsymbol h\) satisfies a rank-four determinant test on the literal first four zero rows (stages two through five).

The actual values at \(a,b,s\) are known from the first three strict rows and from the literal row-four tap matrix. At row five, \(y=c_5\), its \(h_y=\widetilde p(y)/(\Delta q(y))\) fixes the tap to row one as \(h_y/g_1\). The other three strict taps at \(a,b,s\) follow from row sum, quadratic read, and the cubic pure relation. Explicitly their clock moments of degrees \(0,1,2\) are
\[
 y-\gamma-h_y/g_1,\quad
 y^2/2-\gamma y-\gamma h_y/g_1,\quad
 y^3/3-\gamma y^2+(2/3)h_y-\gamma^2 h_y/g_1 .
\]
A three-site Vandermonde determines their reads, since \(s\ne a,b\). Clearing this Vandermonde determinant and \(\Delta q(y)\), the rank-four test for \(A\boldsymbol h\) is a polynomial \(G(y)\) with coefficients in the pole quotient \(E=\mathbb Q(t)[\xi]/(M)\).

The monic quotient \(Q_3(Y)\) of the normalized \(Q_c(Y)\) by \(Y-s\) contains the three remaining noncorner nodes. Row five is one of these by physical distinctness. The exact script proves that \(G\) is a **unit** in the finite algebra \(E[Y]/(Q_3)\) in every phase. It uses good reduction at the prime \(1009\), at the root \(t=285\) of \(2t^2=1\) modulo that prime:

* All rational coefficient denominators in the reduction are checked. The monic pole polynomial retains its degree. A coefficient used as a divisor is verified a unit in the reduced pole quotient by exact Euclid; its multiplication determinant is therefore nonzero in characteristic zero as well, and its inverse can be reduced at the same prime.
* In the monic three-dimensional \(Y\) quotient over the reduced pole algebra, compute the \(3\times3\) multiplication matrix of \(G\) by exact remainders. Its determinant is a unit in the reduced pole algebra in every phase. Since both quotients are monic and preserve their free bases, this certifies the characteristic-zero multiplication map is invertible. In particular this is not inference from absence of sampled \(\xi\) or \(Y\) points, and does not require a separable reduction or degree preservation of \(G\).

Thus a true \(y\) cannot be a zero of both \(G\) and \(Q_3\), proving the eight-site exclusion.

## 5. Further guarded quadratic cuts

For the coprime quadratic case, the earlier square-denominator reconstruction gives \(Q\) rationally in the two denominator coefficients wherever the corner and moment matrices are nonsingular. The [exact quadratic benchmark](check_quadratic_benchmark.py) at \(q=X^2+X+1\) gives full-degree fourth-row gates, nonzero rear evaluations and nonzero resultants with both monic nodal factors in all phases. Hence those necessary rational eliminants are not identically zero: the generic quadratic denominator lies on a proper plane algebraic locus, rather than a free open set of two coefficients. This is not a complete quadratic exclusion. The script also tests \(q=(X-1/2)^2\) directly and excludes every coprime phase with that double pole, including the possible seven-site chart. Phases with a numerator vanishing at its repeated pole are explicitly outside the coprime claim.

## Reproducibility

Run the three check files with Python 3; the pole replays use python-flint 0.9.0 and the quadratic benchmark uses SymPy. Once those libraries are installed the runs need no network. The finite-field checks in Section 4 are only invertibility receipts in fixed monic quotient bases. The symbolic eliminations and tableau reductions are source-level; they do not constitute a fully formal Lean theorem. The preceding rational packet contains the Lean square-denominator independence theorem.

To install the replay dependencies in an isolated Python environment,
run `python3 -m venv .venv` and
`.venv/bin/python -m pip install -r requirements.txt` from this directory.
Then use `.venv/bin/python` for each replay command above.
