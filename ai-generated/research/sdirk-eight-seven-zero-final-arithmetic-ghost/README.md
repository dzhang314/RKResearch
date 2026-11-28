# Final arithmetic-front / silent-eighth ghost chart is impossible

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a characteristic-zero field. Let \(\gamma\ne0\) be the common diagonal, \(\mathbf c=A\mathbf1\), and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Assume exactly seven physical quadratic zeros at seven different clocks, and three distinct physical off-zero clocks. The first three rows are off in the literal arithmetic phase, the second reflected residual ratio is nonzero, and physical row 8 is a silent zero.

**Result.** This chart is impossible over every characteristic-zero field. It is the last exactly-seven-zero branch in the [combined characteristic-zero exclusion](../sdirk-eight-seven-zero-char-zero/README.md). It does not by itself change the general order-eight stage interval.

## 1. The ghost ordinary moments are two-atom moments

Use \(D=1/\gamma\) and the normalized reflected clock \(Y=(1-c)/\gamma\). The rear sites of rows 10, 9 and 8 are \(1,t=1+v,r=1+2v\). The genuine literal silent ghost gives \(H(v)=v^3-4v^2-v+2=0\), \(v\ne0\), and the second ratio \(\kappa=1+2v-v^2\ne0\). Let \(\mathcal P_4\) be the monic node polynomial of the four early zero rows in \(Y\). Write \(I_D(Y^j)=D^j/(j+1)\). Ordinary precision and the rear cardinal numerators \(B_s,B_t,B_r\) satisfy
\[
 I_D(\mathcal P_4(Y)(Y-1)(Y-t)(Y-r))=0,\qquad
 B_s=\kappa B_t,\quad B_r=0,\quad B_t\ne0 .
\]
The ordinary quadratic cardinal polynomials on \(1,t,r\) form a basis of degree-at-most-two polynomials. By interpolation on that basis and the cubic nodal moment,
\[
 \frac{I_D(Y^j\mathcal P_4)}{B_t}=\alpha+\beta t^j,\qquad
 \alpha=\frac{\kappa}{2v^2},\quad \beta=-\frac1{v^2},\quad 0\le j\le3.     \tag{1}
\]
The assertion is a masked polynomial moment identity; it does not assign an actual nonzero weight to the silent row.

Pass to the physical reflected coordinate \(X=\gamma Y=1-c\). Write \(p_4\) for the monic early quartic in \(X\), \(\psi=B_t/D^4\ne0\), \(I(X^j)=1/(j+1)\), and
\[
 \ell(X)=\frac{70X^4-140X^3+90X^2-20X+1}{70},\qquad
 {\cal C}_f(x)=I_X((f(X)-f(x))/(X-x)).
\]
The four-by-four ordinary Hilbert inverse applied to (1) gives
\[
 p_4=\ell+\psi S,\quad \deg S\le3,\qquad
 I(X^jS)=\gamma^j(\alpha+\beta t^j),\quad 0\le j\le3.        \tag{2}
\]
No division by a prospective quartic value is needed for this reconstruction.

## 2. Cancel the ghost's latest-clock projection to degree two

Let \(e\) be the normalized reflected clock of the latest of the four early zeros and put \(x_e=\gamma e\). In the genuine fourth reverse read take the weighted profile \(R(Y)=(Y-1)(Y-t)\). Its last three physical inputs vanish: \(R\) kills the two live sites, and the eighth weight is zero. All off inputs also vanish. Its fourth reverse read is diagonal, as in the [affine fourth-read argument](../sdirk-eight-seven-zero-final-cubic-front/README.md#1-a-fourth-reverse-affine-gate). Put \(K(Y)=\int_0^Y R(T)\,dT,\ F(Y)=R(Y)-K(Y)\). The pure error is affine after multiplication by the nodal derivatives. At \(1,t\) its values are \(-\kappa B_tK(1),-B_tK(t)\), so at \(e\)
\[
 B_e F(e)+B_t\left[\kappa K(1)+(e-1)\frac{K(t)-\kappa K(1)}{v}\right]=0.
\]
Since \(6(2K(t)-\kappa K(1))=H(v)=0\), the bracket is \(q(e-r)\) with \(q=-\kappa K(1)/(2v)\). Dividing the rear cubic modulo \(Y-e\) and evaluating its quadratic quotient using (1) gives
\[
 B_e=(e-1)(e-t)(e-r)\left[I_D\!\left(\frac{\mathcal P_4(Y)}{Y-e}\right)
                           + B_t\!\left(\frac{\alpha}{e-1}+\frac{\beta}{e-t}\right)\right].
\]
All three differences are nonzero. Thus the fourth read is equivalent to
\[
 F(e) I_D(\mathcal P_4/(Y-e))+W(e)B_t=0,\qquad
 W(e)=\frac{F(e)[\alpha(e-t)+\beta(e-1)]+q}{(e-1)(e-t)}.
\]
The numerator of \(W\) vanishes at both \(1,t\) by \(2K(t)=\kappa K(1)\), so \(W\) has degree at most two. In physical reflected coordinates the relation is
\(\gamma^3 F(e){\cal C}_{p_4}(x_e)+\gamma^2 W(e)\psi=0\).

The two linear equations for \(\psi\) are this relation and \(p_4(x_e)=0\). To eliminate \(\psi\), use the exact *two-atom* identity
\[
 \ell(x){\cal C}_S(x)-S(x){\cal C}_\ell(x)
 =-\alpha\frac{\ell(x)-\ell(\gamma)}{x-\gamma}
  -\beta\frac{\ell(x)-\ell(\gamma t)}{x-\gamma t}.             \tag{3}
\]
For a proof, in formal Laurent series write the divided mean of \(f\) as
\(f(x)\sum_{j\ge0} I(X^j)x^{-j-1}-\sum_{j\ge0} I(X^j f)x^{-j-1}\).
The terms involving the first series cancel. The polynomial part of the term from \(S(x) I(X^j\ell)\) is zero because \(\ell\) has four zero moments and \(\deg S\le3\). In the remaining term from \(\ell(x) I(X^j S)\), only \(j\le3\) contribute; (2) gives the two evaluation atoms, proving (3).

Substituting (3) into the linear determinant, the high-degree terms cancel. The necessary numerator simplifies to the quartic
\[
 q\,\ell(\gamma e)+F(e)\bigl[
        \alpha\ell(\gamma)(e-t)+\beta\ell(\gamma t)(e-1)\bigr].
\]
It is exactly divisible by the forbidden collision factors \((e-1)(e-t)\), leaving
\[
                   A(v,\gamma)e^2+B(v,\gamma)e+C(v,\gamma)=0.          \tag{4}
\]
Its coefficients have degree at most four in \(\gamma\) and lie in \(\mathbb Q(v)\). The exact synthetic divisions are checked in the replay. This step retains \(A=0\) separately and uses no approximate curve or first-gap parametrization.

## 3. The generic exact ordered-root norm

Use the [division-free arithmetic forward graph cubic and cofactor projection](../sdirk-eight-seven-zero-final-arithmetic-star/README.md#2-a-division-free-forward-graph-equation), unchanged from the live star. For generic \(A S(x_e)\ne0\), recover \(\psi=-\ell(x_e)/S(x_e)\), and introduce the monic scaled intermediate \(\widehat e=Ae\), \(S_* = A^3 S(\gamma e)\), \(L_*=A^4\ell(\gamma e)\), and \(M=A S_*\). The monic early polynomial on the scaled reflected clocks is
\[
 \widehat p_4(Z)=M^4\ell(Z/M)-M^3L_*S(Z/M).
\]
Remove its known exact root \(Mx_e=\gamma\widehat e S_*\). Then take an ordered pair of roots from the remaining monic cubic and its complementary quadratic. The graphs are evaluated on scaled original forward clocks, endpoint \(M\), and diagonal \(M\gamma\). Successive determinants of multiplication in the rank \(2,3,2\) monic algebras project the cofactor equation to the variable \(\gamma\) over the exact cubic ghost field \(K=\mathbb Q(v)\). The graph cofactor relation is valid even if its own two-by-two pivot vanishes.

The raw degree in \(\gamma\) is 8868. In \(K[\gamma]\) the leading guard \(A\) is an irreducible quartic, and the norm of \(S_*\) in the two-root \(\widehat e\) algebra has the exact guard factors \(A^3 S_{126}S_{198}\), up to a unit, with \(S_{126},S_{198}\) both irreducible of degree twelve. The exact division by
\[
 \gamma^{48} A_{\rm monic}^{990}S_{126}^{126} S_{198}^{198}
\]
leaves degree 972 over \(K\). The script verifies the full exact quotient by reversed-polynomial Newton division and a multiplication-back check; no approximate factor stripping is used. The outer norm over the cubic \(v\) field is rational of degree 2916 and factors as \(1836^1,144^3,36^{18}\). The leading and scale guards are not discarded: their outer norm factors have degrees \(12,36,36\) and are checked separately.

## 4. Six fixed geometric fibers

The generic factors are exactly coprime to the leading and scale guards. The degree-144 factor divides the exact norm, over \(v,\widehat e\), of the scaled early quartic discriminant. The degree-36 factor divides the exact norm of \(L_*\), so its indicated \(e\) would force \(\psi=0\). In each case at the selected residue diagonal the replay identifies **one** \(v\) branch of the corresponding exact degeneracy norm and **one** \(e\) branch within it. The simple geometric gap and latest-node roots then identify the actual forbidden repeated-clock or zero-cardinal branch. The other \(v,e\) possibilities are not removed with it.

For each admitted \(v\) whose scale guards are units, the reduced exact degree-972 polynomial is checked before testing that branch: if nonzero it cannot come from an actual generic projection. For a root of the leading guard, its exact zero \(A=0\) branch is matched by the unique zero among three simple geometric \(v\) roots; the linear \(e\) equation then has unit coefficient. For the scale guards use one of the two \(\psi\) coefficients, \(S(x_e)\) or \(\gamma^3 F(e){\cal C}_S(x_e)+\gamma^2 W(e)\), when it is a unit. If both reduce to zero and the first pivot has an exact unique zero branch from its norm, a nonzero \(\ell(x_e)\) rejects that actual branch. These checks preserve any unaffected \((v,e)\) branch over the same diagonal.

At each surviving \(e\), reconstruct the monic early quartic. Check the first two forward graph equations in \(u\) for all ordered early triples of the other three clocks. Their degree is at most three and a unit-leading degree-three equation is checked whenever needed to reduce \(u\). The additional supported off-cubic second read removes the only remaining common-gap candidate in the degree-1836 case. The arithmetic inputs and the division-free graph and optional third-forward determinants are the same literal tests as in the [live-star fiber verification](../sdirk-eight-seven-zero-final-arithmetic-star/README.md#4-all-generic-and-exceptional-fibers).

All six cells below use \(p=101\). Each residue factor divides the corresponding irreducible exact factor with preserved degree and has simple roots.

| Exact diagonal factor | Simple residue factor | Directed early triples tested |
|---|---|---:|
| Generic degree 1836 | \(\gamma+64\) | 12 |
| Generic degree 144, one repeated early quartic | \(\gamma+79\) | 6 |
| Generic degree 36, one zero-cardinal branch | \(\gamma+46\) | 6 |
| Leading guard degree 12 | \(\gamma+96\) | 30 |
| Scale guard degree 36 from \(S_{198}\) | \(\gamma+50\) | 36 |
| Scale guard degree 36 from \(S_{126}\) | \(\gamma^2+94\gamma+16\) | 30 |

Choose an embedding of the exact irreducible diagonal field lifting its indicated simple residue factor and extend it to the required algebraic choices. The cubic for \(v\), the allowed quadratic or linear equation for \(e\), the unit coefficient for \(\psi\), and the monic early quartic justify reduction in that order. All three \(v\) roots and all relevant \(e\) and early-root choices are tested in a full finite extension, which also contains the needed factors when they do not split in the prime field. A front-gap root is integral at these tests, so the final constant gcd gives a characteristic-zero contradiction. This is not a claim about nonexistence over every positive characteristic.

## 5. Replay and native scope

Run `python check_ghost.py` with SymPy 1.14 and python-flint 0.8; it calls `ghost_projection.py` for the complete exact projection, and needs no external coefficient files. Expect several minutes for the fraction-free cubic-field norm and exact guard division. The native `RKCert.Research.SDIRKEightSevenZeroFinalArithmeticGhost` verifies the affine ghost polynomial factor and the cleared two-atom plane equation. Its scalar types do not claim the full rooted-tableau or number-field result directly.
