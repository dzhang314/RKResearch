# No coprime quadratic profile with two arithmetic ends in the SDIRK8 endpoint pair

This completes the **coprime** branch of the all-active half-diagonal endpoint-pair chart for ten-stage strict SDIRK8 over a characteristic-zero field. The [polynomial and line-pole proof](../sdirk-eight-half-line-pole/README.md) excludes degrees zero and one of the denominator, and the [star-end proof](../sdirk-eight-half-star-quadratic/README.md) excludes a coprime quadratic with either end star. Here we exclude the two remaining relative signs when both ends are arithmetic.

Therefore the rational interpolation relation in this endpoint-pair chart must have a common factor and an actual physical zero-stage discrepancy at one of its roots. It is not legitimate to cancel that factor at the discrepancy clock. Other endpoint families and shared-root cases are not decided here. The unrestricted strict SDIRK8 interval remains **10–11**.

## 1. Exact Bézout projection to the literal fourth clock

Use the [eight-distinct-clock theorem and moment identity](../sdirk-eight-half-distinct/README.md). Write \(s=c_4,y=c_5\), \(a,b\) for the front pegged zero clocks, \(c,d\) for the rear pegged zero clocks, and \(P_6=\prod_{x\in(a,b,s,y,c,d)}(X-x)\). All eight physical zero clocks are distinct under a coprime profile. Let \(q\) be monic quadratic and \(p\in\langle L_3,L_4,L_5\rangle\) be its nonzero numerator. The Bézout moment identity for the full nodal polynomial \(D\) is
\[
 p W_D-D W_p=\lambda q^2,\qquad
 W_f(X)= I_Z\!\left(\frac{f(X)-f(Z)}{X-Z}\right),\qquad \lambda\ne0,
\]
where \(I_Z(Z^j)=1/(j+1)\). In particular if \(D=P_6(X^2+uX+v)\), the degree-at-most-four coefficient columns
\[
       \mathcal B_p(P_6),\quad \mathcal B_p(XP_6),\quad
       \mathcal B_p(X^2P_6),\quad q^2,\qquad
       \mathcal B_p(f)=pW_f-fW_p
\]
have rank at most three. Thus all five four-by-four minors of their five-row matrix vanish. Their entries are linear in the coefficients of \(p\) and \(P_6\) for the first three columns, and quadratic in the coefficients of \(q\) for the last. This computation uses no inverse of \(p\) in the quadratic denominator algebra. The exact coefficient formula is the ordinary integral of the monomial divided difference,
\[
 I_Z\!\left(\frac{X^iZ^j-X^jZ^i}{X-Z}\right)
       =\sum_{k=j}^{i-1}\frac{X^k}{i+j-k}\quad (i>j),
\]
with the negative swapped formula for \(i<j\), and zero for \(i=j\).

Work first over \(K_0(s)=\mathbb Q(t)(s)\), \(t^2=1/2\). The [chronological reduction](../sdirk-eight-half-quadratic/README.md) gives a monic degree-two equation for \(y\), then a monic degree-two rear-ratio equation in the denominator-pencil variable \(\beta\) after front interpolation. These may be used over the open chart where the named coefficient pivots and their norms are defined and nonzero. This is a monic degree-four tower over \(K_0(s)\). In the open chart the norm of each of the five minors must vanish at an actual candidate \(s\). The [exact replay](arithmetic_projection.py) takes these norms and the final coefficient norm over \(K_0/\mathbb Q\), a possible enlargement by conjugation, and computes the exact rational-polynomial numerator gcd. It has degree \(232\) and squarefree degree \(46\) in both signs. All its factors already belong to the exact scalar pivot support of degree \(108\). All coefficient denominator factors in the reconstruction and in the norms are verified to be among this support. The support is factored over \(\mathbb Q\) and the reconstruction of its factorization checked.

Thus every hypothetical \(s\), including any specialization with a failed generic pivot, is a root of an explicit finite product. No argument is made from a search over real or finite-field roots of the original order equations.

## 2. Exact finite reconstruction and the largest pivot

In each finite scalar quotient, recompute the literal \(h_y\) read, the four-point Legendre interpolation and the rear ratio. As in the [star proof](../sdirk-eight-half-star-quadratic/README.md), the scaled square-denominator moment determinant is necessary on every coprime fiber. Its entries are computed from the two quadratic monic bases and from the two physical unpegged zero rows. It is a unit after good reduction on the surviving finite algebras, which certifies invertibility in characteristic zero on the same bases. All finite scalar factors below degree \(44\) pass either directly with the generic model or after exact splitting. The splitting checks which affine read, interpolation determinant and denominator-pencil direction can be used, allowing degree drops in both the clock and rear-ratio equations. A nonzero zero-divisor splits the finite algebra by an exact gcd or a verified quadratic-root split; it is not discarded.

The remaining degree-\(44\) scalar factor \(M\) is the exceptional norm of the leading rear-ratio coefficient \(e_2(s,y)\). Recompute the *unmonic* rear equation
\[
               e_2(s,y)\beta^2+e_1(s,y)\beta+e_0(s,y)=0
\]
on this factor. In the rational number field \(\mathbb Q[s]/(M)\), the numerator \(u+t v\) of the norm of \(e_2\) through the clock quadratic satisfies \(u,v\ne0\) and \(u^2-v^2/2=0\). The exact element \(\theta=-u/v\) has \(\theta^2=1/2\); the two values \(t=\theta,-\theta\) cover the characteristic-zero fibers over the chosen \(M\). This can be evaluated in the rational monic scalar basis rather than explicitly factoring degree \(44\) over \(K_0\).

At \(t=\theta\) the norm of \(e_2\) is zero. The affine \(y\)-representative of \(e_2\) therefore identifies the unique clock root where the rear equation is linear, provided its linear coefficient is nonzero. The other \(y\) is obtained from the quadratic trace. All needed nonzero coefficients or inverses, including \(e_1\) on the linear branch and \(e_2\) on the other branch, are checked by the monic reduction. At \(t=-\theta\), the clock quadratic and both rear roots are retained in the usual monic bases. The three finite algebras just described all have a scaled Hankel unit by good reduction at \(997\), for **both** relative endpoint signs. Thus the degree-\(44\) factor also gives no coprime solution.

The full [finite checker](check_arithmetic_family.py) preserves the monic bases and checks every divisor needed in the reductions. A failed finite-field inverse gives no characteristic-zero inference; only successful unit tests are used. The result does not assume reduction of any proposed tableau at the chosen prime.

## 3. Verification boundary

Run `python3 check_arithmetic_family.py` from this folder in the repository. It imports the preceding two quadratic research folders and uses `sympy==1.14.0` and `python-flint==0.9.0` on Python 3. One sign can be selected by a single argument `1` or `-1`. No network is used during replay.

The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8BezoutDefectReceipt.lean) proves the polynomial scalar extraction \(qS=Rp,\ \gcd(p,q)=1,\ \deg R\le2 \Longrightarrow R=\lambda q,S=\lambda p\) with \(\lambda\ne0\) for the nonzero dual profile. The chronology, moment certificate, and exact finite polynomial computations are source-level mathematics and replay, not an end-to-end Lean tableau nonexistence theorem.
