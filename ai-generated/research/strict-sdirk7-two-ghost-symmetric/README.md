# No fully reflected seven-active rational SDIRK7 clock core

Consider the [seven-distinct-active, two-zero-weight chart](../strict-sdirk7-two-ghost/README.md)
for a nine-stage strict order-seven SDIRK tableau. Here the three
chronological reflected terminal clocks are \(v,u,1\), with either
\(v=4-u\) (reflection suffix) or \(v=2u-1\) (arithmetic suffix).
The reciprocal diagonal \(z\) is nonzero. This packet rules out over
\(\mathbb Q\) the entire case in which the **set of seven active
clocks** is invariant under reflection about \(m=z/2\), including
every fourth-from-last active clock and every placement of the suffix.
It does not rule out partly paired, asymmetric, repeated-clock,
or other zero-weight masks. In particular this abstract reflection
symmetry is distinct from the chronological relation \(v=4-u\).

The exact certificate uses the scalar graded ingress already stated in
the earlier packet. The resultant and gcd checks are exact algebraic
replays, not a new native HasOrder theorem. They are independent of the
Christoffel obstruction in the neighboring packet. The affine
three-radius moment pivot in the previously proved centered arithmetic
case and its even-parity Gram identity were checked in
[the existing native module](../../lean/RKCert/Research/SDIRKSevenTwoGhostScalar.lean).

## Symmetric moments

Every permitted symmetric set has the shape
\(\{m,m\pm r_0,m\pm r_1,m\pm r_2\}\) for nonzero rational \(r_i\)
with distinct squares \(R_i=r_i^2\). Write
\(\mu_j=m^j/(j+1)\) for the even uniform moments after centering,
with \(\mu_j=0\) at odd \(j\).
The divided-difference numerators \(K\), identical at opposite nodes,
are
\[
 \begin{aligned}
 K_m&=\mu_6-(\textstyle\sum R_i)\mu_4+
             (\textstyle\sum_{i<j}R_iR_j)\mu_2-R_0R_1R_2,\\
 K_{m\pm r_i}&=\mu_6-(R_j+R_k)\mu_4+R_jR_k\mu_2
 \quad(\{i,j,k\}=\{0,1,2\}).
 \end{aligned}
\]
Indeed the centered node polynomial is \(X\prod_i(X^2-R_i)\);
removing \(X-r_i\) leaves even part \(X^2\prod_{k\ne i}(X^2-R_k)\).
Its derivatives at the center and at either end of pair \(i\) are
\(-R_0R_1R_2\) and \(2R_i\prod_{j\ne i}(R_i-R_j)\), respectively.

Let \(M=u^2-4u+2\). In the reflection suffix take \(T=J=1\); in the
arithmetic suffix take \(T=u^3-7u^2+10u-2\) and
\(J=4u^3-24u^2+39u-17\). (All rational nonzero, with
projective rootlessness checks for the nonconstant factors.)
If \(L_1=-TK_1,\ L_u=MTK_u,\ L_v=MJK_v\), the common scaled
terminal graph is
\[
 \widetilde W(y)=(u-y)L_1+(y-1)L_u,\qquad
 \widetilde W(v)=(u-1)L_v.
\]
The actual affine adjoint numerator is
\(W(y)=\widetilde W(y)/(2T(u-1))\).
For the fourth read \(G(c)K_c+E(c)W(c)=0\),
let \(q_i\) be the coefficients interpolating the three
terminal \(D/b\) ratios. The integer scaling in the script uses
\[
 \begin{aligned}
 \widehat q&=2Tq,\\
 \widehat G(c)&=6\widehat q_0(c-1)+3\widehat q_1(c^2-2c)
                   +2\widehat q_2(c^3-3c^2)=12TG(c),\\
 \widehat E(c)&=-6M\widehat q_1+
       \widehat q_2[-8M+4(1-M)(c-1)]-12T(1-c)=12TM E(c).
 \end{aligned}
\]
Thus the exact cleared condition is
\(2T(u-1)M\widehat G(c)K_c+\widehat E(c)\widetilde W(c)=0\).
No extra \(E(c)\) division is made.

Odd weighted reciprocal moments vanish. If
\(\widetilde W(m+X)=A+BX\), use \(M_j=\sum_i (y_i-m)^j/(K_iP'(y_i))\)
for \(j=0,2,4\). The necessary Gram equation is
\[
 (A^2M_0+B^2M_2)(A^2M_2+B^2M_4)-4A^2B^2M_2^2=0 .
\]
The implementation clears common weight products and rational pivots;
it divides only by factors shown to be nonzero on the stated chart.
It keeps \(A=0\) and \(B=0\) cases in the main branches. In the
previously checked centered arithmetic branch, the additional stripped
factor \(MJ-T\) is now explicitly checked projectively rootless mod 3
after primitive scaling.

## Exhaustive placements and their certificates

Number the ordered list of labels \((1,u,v)\) by \(0,1,2\).
Every terminal label is either at the center or in one of the three
pairs. At most one full pair can be occupied by three labels.

1. **One label from each pair, none at center.** The suffix and \(m\)
   specify all seven clocks. The fourth read can be at \(m,2m-1,2m-u,2m-v\).
   Saturate by the physical distinctness and mass factors, then take
   the exact resultant of the terminal affinity and fourth read in
   \(m\). The following list gives each primitive factor degree and
   a prime with no projective root; multiplicity \(4\) occurs for the
   quadratic in reflection row \(2m-1\). The leading degree is
   unchanged at the stated prime, so rational points with denominators
   divisible by it are not lost.

   | Fourth site | Reflection \((\deg,\ell)\) | Arithmetic \((\deg,\ell)\) |
   | --- | --- | --- |
   | \(m\) | \((4,19),(16,13)\) | \((7,19),(40,11)\) |
   | \(2m-1\) | \((2,13),(4,11)\) | \((7,19),(28,17)\) |
   | \(2m-u\) | \((2,5),(10,11)\) | \((7,11),(28,17)\) |
   | \(2m-v\) | \((4,19),(10,11)\) | \((7,19),(28,13)\) |

2. **One center label and two distinct occupied pairs, or one full
   pair and a third noncentral label.** The center is then one known
   label or the average of its two occupied pair labels. There are
   six ordinary reflection patterns and four ordinary arithmetic
   patterns. Use \(u=2q+1\) so those affine centers have integral
   coefficients. The terminal affinity is linear in the third
   squared radius \(R\), giving \(D(q)R=N(q)\). In each of the ten
   patterns the saturated gcd of \(D,N\) is constant, so no
   allowed pivot is lost. Substitute the fraction-free radius and
   reduce the fourth read at each unused site. At the free pair,
   choose its signed representative \(s\) as the fourth site
   \(m+s\), then project via \(D(q)s^2-N(q)=0\).
   Each of the thirty allowed fourth-read projections has constant
   saturated gcd with its Gram projection. This eliminates every
   chronological choice, not just increasing or decreasing clocks.

3. **Full pair and center.** In the reflection suffix the only
   patterns are \(u=5/3\) (center \(u\), pair \(1,v\)) and \(u=7/3\)
   (center \(v\), pair \(1,u\)). Then \(m=5/3\). In both cases solve
   one free squared radius affinely in the other \(s^2\), checking
   the pivot-exception gcd is constant. The fourth read is at either
   free pair; label that one \(m\pm s\) with \(m+s\) the fourth.
   The resulting cubic fourth polynomial and quartic Gram polynomial
   have constant gcd. The arithmetic suffix has only its already
   proved centered case \(m=u\), pair \(1,v\). Its included standalone
   replay gives the old degree-114 resultant with rational roots
   only \(0,3\), both forbidden; its nonlinears are projectively
   rootless. Colliding-label cases are excluded from the chart throughout.

Run the following in this directory with SymPy 1.14 and python-flint 0.8:

    python check-symmetric.py
    python check-centered-arithmetic.py

Both checks regenerate their input polynomials directly from the moment
formulas. The earlier exact \(\mathbb F_{19}\) centered tableau is
consistent with the conclusion: the rational projective exclusions can
use other primes, and no symmetry exclusion over finite fields or arbitrary
ordered fields is asserted.
