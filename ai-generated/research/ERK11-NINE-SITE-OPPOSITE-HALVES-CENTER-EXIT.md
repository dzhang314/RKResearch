# Opposite halves with different free labels: both central orders are impossible

**Scope.** Continue the [opposite-halves finite atlas](ERK11-NINE-SITE-OPPOSITE-HALVES-FINITE.md)
and its [pivot exclusions](ERK11-NINE-SITE-OPPOSITE-HALVES-PIVOTS.md).
The four distinct calibrations have left extras \(\{e,t\}\), right
extras \(\{h,s\}\) with \(t\ne s\), the dormant clock \(z\) is
physical 9, and the inner active clocks are either \(c_8=t,c_{10}=s\)
(matched) or \(c_8=s,c_{10}=t\) (opposite).
This closes **both central orientations** over characteristic zero
given the inherited genuine nine sites and paid mixed model ledger.
Physical-edge dormant charts and other crossing diagrams are separate.

## 1. Two more literal paid marks

In the matched orientation, for the left-only free label \(t\), the early occurrence
is physical 6 or 7 and the later one is at physical 8.
Use the repeated-exclusive identity from the
[earlier literal two-row gate](ERK11-NINE-SITE-HALF-DIFFERENT-CENTER-MATCHED-EXIT.md).
Specifically its early primitive is zero, and the later primitive
\(AV_L\) is also zero at physical 8 by strictness and the
grade-four cut. If \(F_i,F_8\) are the two forward response
values, the calibrated first \(F_i\ne0\) and the ordinary
pair has distinct responses, so \(1-F_8/F_i\ne0\). The
difference of the two anchored rows after eliminating their
response direction is
\[
 a^5\bigl(L_8-(F_8/F_i)L_i\bigr)
   =(1-F_8/F_i)D_t,\qquad
 D_t=a^5\ell_t-30P(t)\ell_a .
\]
It pairs to zero with actual anchored right row 11
\(\Phi_R\): row 8 is off-diagonal, and the early row is
either off-diagonal row 7 or the zero anchored row 6.
The reflected proof at the right-only \(s\) uses the true
zero reversed primitive at physical 10 and the nonzero
front response scale. This yields two exact relations
\[
 \langle D_t,\Phi_R\rangle_N=0,\qquad
 \langle\Phi_L,D^R_s\rangle_N=0,\qquad
 D^R_s=b^5 r_s-30Q(s)r_d .
\]
Only the already-paid mixed grade-five inverse Gram is
used. The true repeated sites are active, not substitutions
of the dormant response.

Write \(K_j(t)\) for the pairings of \(D_t\) with
the right derivative basis, divided by \(at(a-t)\);
write \(K^R_j(s)\) for the pairings of the left derivative
basis with \(D^R_s\) divided by \(b(1-s)(s-d)\).
These quotients are polynomials of degree at most three
and the canceled factors are live. The exact inverse
Gram coefficient matrix and the bases are in the receipt.
The new equations are therefore
\[
 R_0K_0(t)+R_1K_1(t)=0,\qquad
 L_0K^R_0(s)+L_1K^R_1(s)=0,
\]
where the \(L_i,R_i\) are the four derivative row
coefficients in the finite atlas.

For the opposite orientation write \(x=c_8=s,\ y=c_{10}=t\).
At the repeated left \(t\) the same actual-row difference now reads
\[
 \sigma_t\langle D_t,\Phi_R\rangle_N+
  30(AV_L)_{10}\langle\ell_a,\Phi_R\rangle_N=0,
 \qquad (V_L)_{10}=\sigma_t V_a(t),\quad \sigma_t=1-F_{10}/F_i .
\]
The degree-ten paid pairings from the finite ledger give
\(I(x,z)=\int (X-x)(X-z)V_aV_b\) and \(C_1-zH\).
They are the literal products with
\((C-x)V_L,(C-z)V_R\), and with \(AV_L,(C-z)V_R\),
respectively. Both isolate physical 10: the clock masks
delete rows 8 and 9 where needed. Thus multiply the
actual difference by \(b_{10}(t-x)(t-z)(V_R)_{10}V_a(t)\),
and cancel only \(t(a-t)\) from the resulting model equation.
The reflected statement at physical 8 uses \(I(y,z)\),
\(C_2-zH\) and actual \(A^\star V_R\). The two necessary
weighted marks are exactly
\[
 \begin{split}
 &a\,I(x,z)\bigl(R_0K_0(t)+R_1K_1(t)\bigr)
   +30t(a-t)(t-x)(C_1-zH)\langle\ell_a,\Phi_R\rangle_N=0,\\
 &b\,I(y,z)\bigl(L_0K^R_0(s)+L_1K^R_1(s)\bigr)
   +30(1-s)(s-d)(s-y)(C_2-zH)\langle\Phi_L,r_d\rangle_N=0.
 \end{split}
\]
No individual square-clock or primitive amplitude is
divided out in either proof. The nonzero factors
\(t(a-t),(1-s)(s-d)\) are literal free-clock guards.

Use its \(Y=\Delta t\), \(\Delta s=\Sigma-Y\),
and clear a power of the independently live \(\Delta\).
Reduction modulo the monic \(Y^2-\Sigma Y+\Delta\Pi\)
gives two linear remainders \(U_LY+V_L,\ U_RY+V_R\),
with the remainder variable \(Y\) still the actual free root.
The preexisting first contact \(U_FY+V_F=0\) gives
\[
 M_L=U_F V_L-U_L V_F=0,\qquad
 M_R=U_F V_R-U_R V_F=0 .
\]
This step divides by neither mark coefficient.

## 2. Width projection and reflection symmetry

Use the preexisting compatibility \(D_c=0\) and take
its dormant resultants against \(X_c,N_F,M_L,M_R\).
Remove only exact factors covered by the earlier live
guards, now including the separately proved-live \(U_F\).
Call the four necessary width polynomials \(W_X,W_F,W_L,W_R\).
The bidegrees in \((b,a)\) are
\[
 \begin{array}{c|cccc}
     &W_X&W_F&W_L&W_R\\ \hline
 \text{matched}&(50,50)&(38,38)&(64,70)&(70,64)\\
 \text{opposite}&(50,50)&(40,40)&(82,88)&(88,82)
 \end{array}
\]
in the two actual orientations.
The replay checks exactly that \(W_X,W_F\) are
symmetric and that \(W_L(b,a)\) is a nonzero rational
multiple of \(W_R(a,b)\). In particular
\(W_M=W_L(a,b)+W_L(b,a)=0\) at the actual widths;
this uses **both** literal contact gates, not an ordinary
reverse-order-eleven assertion or a numerical symmetry
assumption about the tableau.

Set \(S=a+b,\ T=ab\). Each of \(W_X,W_F,W_M\)
is now expressed exactly as a polynomial in \(T,S\)
using the symmetric recurrence for \(a^j+b^j\).
Clear only nonzero rational contents to construct primitive
integer coefficient polynomials. Take the two \(T\)-resultants
\(\mathcal R_X,\mathcal R_M\) anchored at \(W_F\).
A true width pair makes both vanish at its \(S\),
even at specialized degree drops.

## 3. Exact degree and common-factor certificate

The modular arithmetic retains all input \(T\)-degrees, and
checks the following resultant sizes and gcds in \(S\).
The last two columns are earned independently over the rationals:
\[
 \begin{array}{c|r|c|c|c|c}
   &p&(\deg \mathcal R_X,\deg\mathcal R_M)&
      \text{modular gcd}&\text{exponent totals}&
      \text{exact infinity valuations at least}\\ \hline
 \text{matched}&107&(1820,2544)&(S-2)^8&(1900,2660)&(80,116)\\
 \text{opposite}&103&(1960,3384)&1&(2000,3520)&(40,136)
 \end{array}
\]
To prove the exact **degree preservation**, use the
increasing-coefficient Sylvester matrices. Choose integral
row/column exponents \(\rho_i,\gamma_j\) whose sums bound
every entry's \(S\)-degree. The receipt checks each inequality
and the recorded exponent totals. With \(u=1/S\) multiply entry
\((i,j)\) by \(u^{\rho_i+\gamma_j}\). The result is a polynomial
matrix whose determinant is the original resultant evaluated
at \(1/u\) times the required power of \(u\), up to a nonzero
rational constant and harmless Sylvester orientation sign.
The exact valuations in the table give upper bounds matching
the retained modular leading terms, so the degrees are
indeed preserved. In the matched chart there is also an
exact finite check: substitute \(S=2+u\) in each original
Sylvester matrix. The same elimination earns eight powers of
\(u\) in each determinant, with nullity totals \(4+2+2\).
Thus the monic integral divisor \((S-2)^8\) genuinely
divides both matched characteristic-zero projections.

For clarity the determinant valuation calculation works over
\(\mathbf Q[u]\): perform ordinary rational row operations
using only coefficients at \(u^0\), apply those same operations
to the polynomial rows, and put the zero constant rows last.
Each of those whole rows is divisible by \(u\); divide it
and earn a power of \(u\) in the original determinant. Repeat
until the bound is reached. Terms above the target valuation
may initially be discarded because replacing matrix entries
modulo that power does not affect determinant divisibility.
The replay uses exact rational operations, not a floating-point
rank, a numerical root sample, or a modular evaluation of a
hypothetical tableau. An integer assignment routine only
proposes the degree exponents; their entrywise inequalities
and total degrees are checked as part of the receipt.

In the matched orientation, divide by the exact monic
\((S-2)^8\). The integer resultants still have their degrees
preserved modulo \(107\); their reductions are coprime,
hence they are coprime over \(\mathbf Q\).
Thus the only possible matched common value is \(S=2\),
which forces \(h=e\), contrary to four distinct calibrations.
In the opposite orientation the original degree-preserving
reductions modulo \(103\) are already coprime, so there is
no characteristic-zero \(S\) at all. No retained finite
\(T\) fiber or real-ordering assumption is needed.

The new computation is a standalone rational and modular
certificate. The earlier Lean gates check the actual row
algebra and the scaled linear compatibility; no claim is
made that the numerical resultant run was executed inside
the Lean kernel.
