# Asymmetric nine-site ERK11: the half-at-10 dormant edge is impossible

**Scope.** Continue the genuinely distinct nine-site six-pair chart
with four distinct calibration labels. The asymmetric extras are
left \(\{e,t\}\), right \(\{t,s\}\), and the actual central physical
order is \(c_8=z,c_9=s,c_{10}=h\), with \(z\) dormant. This
excludes that entire physical-8 orientation and its actual
reflected physical-10 orientation over characteristic zero.
The [zero affine slope](ERK11-NINE-SITE-ASYMMETRIC-EDGE-DROPOUT.md)
was handled separately; the proof here is for the live slope.
It does not exclude the swapped physical-9/10 order, the other
asymmetric edge geometry, or the [opposite central remainder](ERK11-NINE-SITE-ASYMMETRIC-CENTER-ATLAS.md).

## 1. Actual affine and shifted square-root-free data

The [middle four paid products](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md)
give \(B(z,h)=0\), since those products isolate the physical-9
row, which is active here. In the live-slope case set
\[
 E=A_0h+B_0,\quad N=-(C_0h+D_0),\quad E\ne0,\quad z=N/E .
\]
No amplitude other than the earned affine pivot is divided by.

From \(P_4=(X-a)(X-h)(X-d)(X-e)\), let
\(m_j=\int X(1-X)P_4X^j\), \(0\le j\le4\).
The true signed sites \(z,t,s\) and live modified weights
give \(\Omega=\det(m_{i+j})_{0\le i,j\le2}\ne0\).
With \(E_j=m_{j+1}-zm_j\) put
\[
 \Delta=E_0E_2-E_1^2,\quad
 \Sigma=E_0E_3-E_1E_2,\quad
 \Pi=E_1E_3-E_2^2 .
\]
The true shifted two-site pivot is live, and
\(\Delta(t+s)=\Sigma,\ \Delta ts=\Pi\).
Let \(q_0=\int X(1-X)H_6\) with the actual monic six-active-node hull.
Then \(\Delta q_0=m_0\Pi-m_1\Sigma+m_2\Delta=\Omega\).
None of these relations needs positive pooled weights.

The right derivative row, multiplied by the independently
live \(\Delta\), has coefficients
\(R_0=d^2\Delta-d\Sigma+\Pi,\ R_1=-\Delta+\Sigma-\Pi\).
The left derivative row has \(L_0=(a-e)(a-t), L_1=-et\).
Thus the first mixed contact
\[
 g_1t+g_0
   =L_0R_0+T_4(a)L_1R_0+T_4(b)L_0R_1+U_{4,4}(a,b)L_1R_1=0
\]
is affine in the chosen *shared* left/right free label \(t\).
Let
\[
                        F=\Delta g_0^2+\Sigma g_0g_1+\Pi g_1^2 .
\]
The true scaled quadratic of the two remaining roots gives
\(F=0\) without any division by \(g_1\).

## 2. Two literal edge contacts and the lifted support

At dormant physical 8, the early square-clock primitive
is literally zero. Thus the left anchored row pairs to zero
with \(\Phi_R\) (physical 11), and the normal left evaluation
quotient gives the exact port
\[
                          G=K_0(z)R_0+K_1(z)R_1=0.
\]
The removed factor \(az(a-z)\) is a live clock factor.
The inverse Gram and the cubic \(K_j\) are in the replay.

The physical-10 half label \(h\) is left-only, repeating
the actual left half calibration. The early row has zero
left square-clock primitive and nonzero response, and its
paired response at physical 10 is distinct. The repeated
row identity therefore yields the left weighted mark
\[
 a\,I(z,s)\bigl(K_0(h)R_0+K_1(h)R_1\bigr)
 +30h(a-h)(h-z)(C_1-sH)\langle\ell_a,\Phi_R\rangle_N=0 .
\]
To see the literal payment, multiply the repeated left
difference by the weighted right \(V_R\) read at physical
10, both clock masks and \(V_a(h)\). The square-clock
product with masks \(z,s\) kills the other two rows;
the primitive product with right clock mask \(s\) does too
because the forward primitive is zero through row 8.
They give \(I(z,s)\) and \(C_1-sH\) at total grade ten.
Removing only \(h(a-h)\) yields the displayed equation.
No individual primitive amplitude is assumed live.
Substitute \(\Delta s=\Sigma-\Delta t\) and clear the
live \(\Delta\); this is a second affine row \(l_1t+l_0=0\).
Its compatibility with the first row and its norm give
\[
 R=g_1l_0-l_1g_0=0,\qquad Q=\Delta l_0^2+\Sigma l_0l_1+\Pi l_1^2=0 .
\]

The new [dormant support](ERK11-NINE-SITE-ASYMMETRIC-DORMANT-SUPPORT.md)
adds a test not encoded in those two contacts:
\[
 I(s,h)(z-e)(z-t)=q_0 z(1-z)(z-a)(z-d).
\]
It follows by the actual dormant-only mixed square-clock
test masking \(s,h\), and the true degree-eight Lagrange
weight. It is equivalent to the actual two-crossing
crossover, not an additional gate beyond that crossover.
Put \(p=I_2-hI_1,\ q=hI_0-I_1\); this is the paid affine
condition \(uY+v=0\) at \(Y=\Delta t\), with
\[
 \begin{aligned}
 u&=-(z-e)(p+qz),\\
 v&=(z-e)(pz\Delta+qz\Sigma-q\Pi)-\Omega z(1-z)(z-a)(z-d).
 \end{aligned}
\]
Therefore the two additional width equations are supplied
by \(S=g_1v-u\Delta g_0=0\) and
\(T=v^2+\Sigma uv+\Delta\Pi u^2=0\).
Only in the next section is the live-slope substitution
\(z=N/E\) made in all six polynomial conditions.

## 3. Exact global width projection

The replay first takes the earlier three width equations
\(G,F,R\), with proven-live factors only removed before
and after the homogeneous affine substitution. Their
bidegrees in \((a,b)\) are respectively
\((28,27),(48,44),(55,49)\).
Clear rational denominators and integer contents. The two
\(b\)-resultants of \(G\) with \(F,R\) have exact degrees
\(2440,2757\) in \(a\). The script reconstructs them
by Chinese remaindering over primes at which the input
\(b\)-degrees are preserved. The coefficient bound for each
integer Sylvester determinant is
\((m+n)!\|f\|_1^n\|g\|_1^m\) for \(b\)-degrees \(m,n\);
the prime product exceeds twice this bound before lifting.
The exact common \(a\)-gcd has degree 1667 and factors as
\[
 a^{264}(a-1)^5(a-2)^{98}
 F_3^4F_4^4F_8^4F_6^{30}F_{15}^{30}F_{50}^{\,2}F_{57}^{\,2}F_{132}^{\,3}
\]
up to a rational unit, with the eight indicated exact
irreducible factors of the indexed degrees.
The first three widths force invalid calibration clocks.
No other factor is discarded merely because it is named
by a possible guard.

## 4. Exact factor removal and all local width fields

Each surviving \(F_d(a)\) is treated in the field
\(\mathbf Q[a]/F_d\). In degrees 3 and 8 the exact
specialized \(b\)-degrees of \((G,F,R,S,T,Q)\) drop to
\((26,42,47,38,45,52)\). They are checked **after**
specializing the rational coefficient field, before any
modular test. A field-place reduction modulo 103 preserves
those degrees and gives unit gcd, so these are not actual
finite-degree solutions at the formerly presumed leading term.
The degree-50 and degree-57 fields also give unit gcd
at degree-preserving places modulo 103 with no factor removal.

In degree 4, the exact common factor is supported at \(b=0\):
remove powers \(1,2,2,1,1,2\) of \(b\) respectively from
\((G,F,R,S,T,Q)\), after checking zero remainders over the
rational coefficient field. In degrees 6 and 15, the exact
monic \(b\)-gcd of the independently defined affine \(E,N\)
is linear and its fifth power divides each of the six
equations, also checked over the full rational coefficient
field. Those linear roots violate \(E\ne0\).
After the exact guard divisions, degree-preserving places
modulo 103 give unit gcd in these three width fields.
The proof does not discard a field because one residue
of an unknown width satisfies a guard.

In degree 132 the relevant forbidden factor is a different
one. Take the degree-one \(b\)-subresultant
\(\lambda b+\eta\) of the global width polynomials
\(\Omega\) and the homogenized \(\Delta\).
Its \(\lambda\) is a unit in \(\mathbf Q[a]/F_{132}\).
The exact homogeneous evaluations at \(b_*=-\eta/\lambda\)
of \(\Omega,\Delta,\Pi,\Delta-\Sigma+\Pi\) all vanish.
The proof uses the constant and unit arguments of the
scaled free quadratic for the last two checks. Thus
\(\Omega=\Delta=\Sigma=\Pi=0\) at this exact algebraic width.
The affine \(E\) and \(a,b\) are nonzero there, as certified
by nonzero values at the degree-95 place modulo 107.

Consequently each of \(G,F,R,S,T\) vanishes at \(b_*\)
**over the rational coefficient field**: \(R_0,R_1\)
vanish, so the raw first and weighted second rows vanish;
the two dormant-support row coefficients also vanish.
The exact replay checks that the only factors removed
from these five raw polynomials before affine specialization
are powers of \(a,b\), and after it only powers of \(a\).
The affine denominator \(E\) is live at \(b_*\); hence
every corresponding normalized width gate still vanishes.
We do not use \(Q\) for this factor, since it removed
powers of the now-vanishing \(\Delta\).
Thus each of those five width polynomials has the exact
forbidden factor \(b-b_*\). At the degree-95 place,
this linear factor is defined and monic, division preserves
the measured leading degree, and their remaining reduced
gcd is one. This completes the entire highest-degree
field, not just a single ordered embedding.

For clarity, a one-place lift here is sufficient because
\(F_d\) is irreducible over \(\mathbf Q\). At a good
polynomial place modulo the indicated prime, the coefficient
field is the fraction field of the corresponding localized
integral ring. A retained \(b\)-leading coefficient is a
unit there, so quotienting by that monic polynomial makes
a finite free module. A unit gcd with the other equations
over the residue field gives a spanning matrix with a unit
minor. Thus the same ideal is the unit ideal over the
rational coefficient field, and remains so under every
characteristic-zero embedding. An exact, monic, forbidden
factor may first be divided out, as above.

This closes the live-\(E\) half-at-10 edge. Together with
the [zero-\(E\) proof](ERK11-NINE-SITE-ASYMMETRIC-EDGE-DROPOUT.md)
and reflection of the actual weighted transpose ledger,
it closes the stated orientation without ordinary reverse
order eleven. The large algebraic receipt is exact Python;
existing Lean gates cover the scalar model identities.

The [source replay, factor checkpoint, and independent full replay log](erk11-nine-site-asymmetric-edge-h10-exit/) are included.
