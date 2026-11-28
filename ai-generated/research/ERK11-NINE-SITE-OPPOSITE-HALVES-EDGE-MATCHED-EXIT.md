# Opposite halves, different free labels: no matched dormant edge

**Scope.** Continue the [opposite-halves finite atlas](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md)
and [pivot exclusions](ERK11-NINE-SITE-OPPOSITE-HALVES-PIVOTS.md).
Take left extras \(\{e,t\}\), right extras \(\{h,s\}\), all
nine scalar sites genuinely distinct. At physical 8 dormant,
the matched orientation is \(c_8=z,c_9=t,c_{10}=s\).
This excludes it and its reflected physical-10 counterpart
over characteristic zero. The opposite edge order and
asymmetric crossing geometry are not covered.

## 1. Live edge reconstruction

Keep \(B(u,v)=A_0uv+B_0u+C_0v+D_0\).
The actual grade-ten middle products earn \(B(z,s)=0\).
Consequently
\[
 E=A_0s+B_0,\quad N=-(C_0s+D_0),\quad Ez=N .
\]
The slope \(E\) is live: if it vanished, so would \(N\),
forcing \(A_0D_0-B_0C_0=0\) in contradiction to the
pivot packet's proved-live mixed determinant. This is the
slope for physical-8 \(z\) with fixed actual \(s\), not the
other edge slope from that packet.

For \(m_j=\int X(1-X)P_4 X^j\), let
\(M_j=E m_{j+1}-N m_j,\ 0\le j\le3\).
These are the true moments multiplied by \(E\) and with
the factor \(X-z\); their only sites are \(t,s\), with both
modified weights live by the signed Vandermonde proof.
Multiplication by \(X-s\) leaves the single site \(t\).
Thus
\[
 D_t=M_1-sM_0,\quad N_t=M_2-sM_1,\quad
 D_t\ne0,\quad D_t t=N_t,\quad
 Q=D_t(M_3-sM_2)-N_t^2=0 .
\]
The nonzero \(D_t\) is a product of \(E\), the shifted
weight at \(t\), and \(t-s\); no ordinary positivity is
assumed. The required scalar tests are still of degree at
most ten.

## 2. A low-degree two-contact determinant

The physical-8 dormant left row has \(L_8=D_z^{\rm fun}/a^5\)
by the actual primitive cutoff, where
\(D_z^{\rm fun}=a^5\ell_z-30P(z)\ell_a\).
Write \(K_0,K_1\) for its pairings with the right derivative
basis after removing the live factor \(az(a-z)\). Let \(M_0^R,M_1^R\)
be the corresponding cubics \(K_j^R\) from the central packet.
At actual \(s\) in physical 10 the repeated right primitive
is zero by chronology, so its actual early/later pair
difference earns
\[
 L_0 M_0^R(s)+L_1 M_1^R(s)=0 .
\]
The transfer is identical to the literal right contact in the
[matched central proof](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md):
the right repeat is at its own local 6 or 7 and then
physical 10, with live response difference and both forward
anchor contacts legal.

Put \(F_0=R_0+T_4(b)R_1\) and
\(F_1=T_4(a)R_0+U_{4,4}(a,b)R_1\).
The first derivative contact says \(L_0F_0+L_1F_1=0\),
where \(L_0,L_1\) are individually live as clock products.
The following determinant therefore vanishes, even if both
\(M_j^R(s)\) vanish:
\[
                      K=F_0M_1^R(s)-F_1M_0^R(s)=0 .
\]
This is a compatibility test, not a division by either
contact vector. The separate physical-8/row-11 off-diagonal
gives the true dormant port
\[
 G=R_0 K_0(z)+R_1 K_1(z)=0,\qquad
 R_0=(h-d)(s-d),\quad R_1=-(1-h)(1-s).
\]
Use \(z=N/E\), clearing its live denominator from \(G\).
The same substitution in \(X_c(a,b,z)=0\) gives \(X=0\).
The first contact may additionally be evaluated at the
literal \(t=N_t/D_t\), yielding \(F=0\) (recorded for
consistency; the final two projections do not need it).

## 3. Exact projection and whole forbidden-width lift

Divide only factors of known live expressions: the basic
calibration differences, \(H,J_0,R_{33},U_F,\Omega\), the
two earned slopes \(E,D_t\), and the pairwise distinct
clock expressions after clearing those slopes.
The optional guard \(I(t,s)\ne0\) follows from the true
dormant-only square-clock product, since both model factors
are live at \(z\) and its individual output weight is live.
No reality or sign is assumed for any weight.

Take \(s\)-resultants of \(G\) with \(K,Q,F,X\);
after removing only live width factors their bidegrees in
\((b,a)\) are respectively
\[
                       (32,28),\ (58,60),\ (51,53),\ (52,61).
\]
Write these width polynomials as \(W_K,W_Q,W_F,W_X\).
The two \(b\)-resultants of \(W_K\) with \(W_Q,W_X\)
have characteristic-zero degrees in \(a\) at most
\(3544,3408\) by exact entrywise integer Sylvester row/column
degree bounds. The receipt checks those bounds themselves,
not a heuristic estimate of resultant cancellation.
With primitive integral inputs both degrees and all input
\(b\)-degrees are preserved modulo \(103\), and the
modular common gcd is exactly \((a-2)^{46}\).

To earn that entire common divisor over \(\mathbf Q\),
substitute \(a=2+u\) in both exact Sylvester matrices and
use the [constant-row valuation method](ERK11-NINE-SITE-OPPOSITE-HALVES-CENTER-EXIT.md):
rational row elimination of constant terms, followed by
dividing whole zero-constant rows by \(u\), earns at least
46 powers in each. Truncation above the target power
preserves the determinant-divisibility assertion. The exact
script checks the complete row calculations. This is an
exact monic divisor of both primitive integer resultants,
so division preserves modular leading degrees. The
remaining reductions are coprime and hence the remaining
integer resultant factors are coprime over \(\mathbf Q\).

Any true width therefore has \(a=2\), which forces the
forbidden calibration \(h=1\). This closes the matched edge
without an unexamined degenerate-width or affine fiber.
Exchanging the actual forward and weighted transpose
roles reflects physical 8 to 10 and maps a matched diagram
to the appropriate matched reflected edge. The proof needs
no ordinary reverse order eleven.

The example-free certificate is exact Python arithmetic.
The simultaneous linear compatibility, shift-rank and
repeated-row scalar algebra are already covered by the
existing Lean packets; the higher resultant calculations
are not claimed as Lean kernel computations.
