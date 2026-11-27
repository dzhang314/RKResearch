# An eleven-stage explicit order-eight method over the rationals

**Later result.** A [single exact eleven-stage tableau](../erk-eight-dispersed/README.md) over the factorial localization now supersedes the universal upper bound discussed here. It uses seven active sites and a dispersed defect space.

A [later Lean-checked rational portfolio](../erk-eight-local-rings/README.md) also covers all admissible local rings and all admissible positive-characteristic commutative rings. The finite prime portfolio below remains a separate exact check.

The literal [eleven-stage tableau](tableau.json) satisfies all 200 rooted-tree conditions through order eight and fails order nine. Combined with the [eleven-stage lower bound over ordered fields](../erk-eight-stage-floor/README.md), this closes the rational stage minimum at eight: **11 stages are necessary and sufficient**. The same conclusion holds over any ordered field by extending the rational coefficients. No claim of a historical first is made.

The [native Lean certificate](../../lean/RKCert/ReviewedNative/ERK8RationalEleven.lean) proves the literal result for the repository's reviewed predicates. It also proves exact order eight over any nontrivial commutative ring in which the specific common denominator \(D\) is a unit. That is stronger than requiring \(8!\) to be a unit; this literal tableau is **not** a witness over the universal factorial localization \(\mathbb Z[1/210]\).

* In ai-generated/lean, run: **lake build RKCert.ReviewedNative.ERK8RationalEleven**. The two printed theorems use only standard axioms on Lean 4.36.0.
* In this research directory, **python3 replay.py** independently reads the literal rational array, enumerates all rooted trees with at most eight nodes, and checks the denominator-cleared integer equations. It verifies the two explicit ninth-order defects
  \[
    \text{ninth-order bush residual}
      =-\frac{271627373}{102186724640},
    \qquad
    \text{tall residual}=-\frac{10905669725135589343}{355459290115923175}.
  \]
  Here the normalization is \(t!\,\boldsymbol{b}^{\mathsf T}\boldsymbol{\Phi}_t(A)-1\); the ninth bush tree factorial is 9, and the ninth tall tree factorial is \(9!\). The two cleared numerators are coprime, and the Lean Bézout identity shows exactness after specialization to every nontrivial ring inverting \(D\).
* **python3 construct.py** reproduces the literal tableau from the six-site rational quadrature and separately checks the rooted conditions by exact rational, rather than denominator-cleared integer, arithmetic. It tries the 24 chronological orders of its four nonendpoint sites and each of five choices of repeated nonterminal site. All 120 cases pass exact order eight on this input; the supplied literal table is the smallest under the script's text-size score.

## Finite-prime arithmetic portfolio

The [modular array portfolio](finite-prime-tableaux.json) covers each of the 24 prime divisors \(p\ge11\) of \(D\), including \(11,13,41\). **python3 finite_replay.py** verifies the factorization coverage, primality by trial division, all 4,800 order identities, and a ninth-order failure in every array. It uses the Python standard library only. The optional generator **finite_primes.py** uses SymPy for modular square roots and integer factorization. **prime_coverage.py** gives the weaker alternate-chronology denominator gcd for the fixed rational quadrature.

Consequently eleven stages suffice for exact order eight over **every field of admissible characteristic**, without ordering, completeness, or square-root hypotheses: for characteristic zero or characteristic not dividing \(D\), use the Lean-certified rational array. For a prime characteristic dividing \(D\), use the corresponding replayed modular array by coefficient transfer. These latter certificates also transfer to nontrivial commutative rings of the same prime characteristic. The portfolio is **independently replayed arithmetic, not yet a collection of Lean modules**. It does not cover general prime powers, composite characteristics, or characteristic-zero rings not inverting \(D\).

## Compact chart behind the witness

For the derivation only, scale clocks so the first nonzero pure-stage clock is \(1\), and write \(s\) for the scaled physical terminal. Thus the target scalar quadrature represents the mean \(s^{-1}\int_0^s\). In stage chronology use
\[
 \boldsymbol c=(0,a,\tfrac12,1,1,x,g,u,v,r,s)^{\mathsf T}.
\]
The canonical pure clocks are \(0,1,g,u,v,s\), and \(r\in\{0,1,g,u,v\}\) is the repeated pure clock. The four potentially defective physical rows are \(2,3,4,6\). The low defects have the three directions \(\boldsymbol q,\boldsymbol f,C\boldsymbol f\), where \(C=\operatorname{diag}(\boldsymbol c)\), \(\boldsymbol q=A\boldsymbol c-\boldsymbol c^2/2\) is supported at stage 2, and \(\boldsymbol f=A\boldsymbol e_2\) has the nonzero entries
\[
 f_3=1/(8a),\qquad f_4=-1/(2a),\qquad f_6=x^2(1-x)/a.
\]
The first five rows use the scaled \(T=2N\) prefix from the single-quadratic-defect chart; row 6 is determined by the first two primitive moments and \((A\boldsymbol f)_6=(1/2-x)f_6\). Output weights live only on the pure rows. Split the canonical weight \(W(r)\) between the earlier pure row and its later copy number 10.

A row difference \(\boldsymbol\delta\) between the repeated physical rows must kill degree-four clock powers and the three directions. Take \(\delta_2=0\), take dirty entries proportional to
\[
 \delta_3: \delta_4: \delta_6
   =8(1-x): (1-2x): -1/(2x^2(1-x)),
\]
and cancel their polynomial reads on the five canonical nonterminal pure clocks by Lagrange interpolation. If \(L_z\) is the canonical Lagrange polynomial at pure predecessor \(z\), the unscaled coefficient for \(z=u,v\) is
\[
  \delta_z=-8(1-x)L_z(1/2)+\frac{L_z(x)}{2x^2(1-x)} .
\]
Put \(y_z=s-z\). The second and third reflected reverse balances at the last two distinct nonterminal pure clocks require
\[
 \delta_u=R\delta_v,\qquad
 R=\frac{W(u)y_u^2}{W(v)y_v^2}
       \left(1-\frac{2(v-u)}{y_v}\right).
\]
Eliminating the common scale of the row difference leaves
\[
 L_u(x)-R L_v(x)
 -16x^2(1-x)^2\bigl(L_u(1/2)-R L_v(1/2)\bigr)=0 .
\]
This polynomial has degree at most four and the three trivial roots \(0,1/2,1\). Provided its degree-four coefficient is nonzero, the remaining root is a rational expression in the pure clocks and weights. The chart discards it if it collides with any of these three roots or if \(\delta_v=0\); both exclusions are literal division/normalization guards. For the frozen rational table it is \(-499165205/1714218151\) in head-normalized units.

All later unknown taps are linear systems. At the channel \(g\), the two reverse balances solve for the taps from \(u,v\) into it. At the channel \(u\), the first determines its tap from \(v\) and the second is exactly the scalar condition above. Each of those three pure receiver rows then uses four ordinary primitive moments and one \(\boldsymbol f\)-annihilation test to fix its reads from the origin, the earlier pure clock \(1\), and the three dirty rows other than stage 2. The five-column system is nonsingular: four distinct scalar clocks give the ordinary four-dimensional Vandermonde space, and the two physical columns at clock 1 are distinguished by \(\boldsymbol f\). The remaining reverse tests follow by pairing their residual row with the four clock powers and the two directions \(\boldsymbol q,\boldsymbol f\); those six tests separate the six remaining physical positions. Row 10 is the indicated row difference added to its earlier pure row, and the first reverse identity determines row 11. Rescale \(A\) by \(s^{-1}\) to return to terminal-one order conditions.

The proof of the supplied tableau is the literal rooted-tree replay and kernel check, not an assumed reduction to these scalar design equations. The construction does not imply a single eleven-stage tableau over the universal factorial ring.
