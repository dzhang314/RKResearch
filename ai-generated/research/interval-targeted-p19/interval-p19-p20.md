# Exact signed interval rules at orders 19 and 20 by two targeted points

There is a rational rule for \(\mathcal I(f)=\int_0^1 f(X)\,dX\)
with **17 distinct contributing sites in \([0,1]\) at exact order
19**, and another with **18 at exact order 20**, both retaining
the endpoints. The two rules are specified by fixed rational
straight-line operations. No large rational fraction is expanded,
no positivity is claimed, and no conclusion about the 17-site
order-20 case or RK stage minima follows.

## Fixed route from the checked interval seed

Start with the [verified interval order-18 rule](../interval-component-continuation/component-continuation.md)
on 16 sites, using its frozen labels. The failed canonical negative
pair there has no real window. Instead the exact sorted-buffer
rule selects \((u,v)=(7b,6a)\) with greatest additive margin,
in \([460256,460257]10^{-6}\). Both residues are negative. Its
window width is \([848781,848782]10^{-6}\), the zero-defect
parameter lies at \([546976,546977]10^{-6}\), and its marked
infinity point \(D\) is nontorsion by the exact mod-\(q\) test.
Here and throughout \(q=2147483647\).

On this curve the prescribed rank-free triple is exterior.
Select the single point **\([168]D\)** in the identity component
and pull it back to the ordered-root chart. The target was planned
with an approximate real phase of \([2]D\), about \(0.9416062160\);
using \(129/137\), the congruence \(129k\equiv13\bmod137\) gives
\(k=84\). The approximation is only planning, not a proof of
membership. The exact chord-and-tangent straight-line chain for
\([168]D\) (7 doublings and 2 additions) and its direct certified
physical enclosures prove membership:
\[
 10^6\tau\in[536565,536566],\qquad
 10^6(x_a,x_b,x_c)\in
 ([677437,677438],[448480,448481],[31682,31683]).
\]
These are the right, middle and left branches, respectively.
Remove the original pair and append these as \(9a,9b,9c\).
All 17 resulting sites have distinct residues and all cofactors
have nonzero residues. The first defect is \(1698450493\bmod q\).

The new defect ratio is positive in \([10411,10412]10^{-6}\),
so choose the next negative pair \((9b,9a)\) (middle, right).
Its exact arithmetic test is nontorsion, and its real window
contains \((1/2,7/10)\). Its rank-free triple is also exterior.
Select the single point **\([-42]D_{\rm new}\)**. The planning
phase of \([2]D_{\rm new}\) is about \(0.9929706688\).
The proxy \(141/142\) and index \(j=21\) give
\(141k\equiv21\bmod142\), with signed representative \(k=-21\).
The actual rational chain (5 doublings and 2 additions starting
from \(-D_{\rm new}\)) gives exact direct enclosures
\[
 10^6\tau\in[592044,592045],\qquad
 10^6(x_a,x_b,x_c)\in
 ([704484,704485],[581636,581637],[431841,431842]).
\]
Remove \((9b,9a)\) and append this second new triple. All 18
resulting sites have distinct residues and nonzero cofactors,
with first defect \(240109312\bmod q\).
No other group points were tested. Negative residues on both
tested pencils make the whole real parameter circle split;
the targeted multiples are even, hence in the identity
component. The proof does not use a density heuristic to
infer a rational or interval result.

## Exact identities behind the verifier

For any chosen pair \(u<v\), use \(\ell=v-u\), \(B=(X-u)(X-v)\),
\(h=\mathcal I(X^2P)\), \(C_i=\mathcal I(P/(X-i))\),
\(a=h/(C_u\ell^3)\) and \(b=-h/(C_v\ell^3)\).
The two physical pole residues are \(\ell^2 a,\ell^2 b\).
For two negative residues \(F'(X)>0\) on each of the three
pole-free real intervals, and the poles' one-sided limits make
each image all of \(\mathbb R\). Its full inside-root window is
\(F(0)<\tau<F(1)\). As proved in the
[buffer test](../interval-component-continuation/component-continuation.md),
the width is \(1-(\rho_u+\rho_v)/\ell\) when
\(\rho_i=|h/C_i|/[i(1-i)]\).

For the [normalized split curve](../two-shift-elliptic-transfer/elliptic-transfer.md)
write \(f(x)=x+a/x+b/(x-1)\),
\(L=x^2+(a+b-1)x-a\),
\(g=x^2+\alpha x+\beta\) with
\(\alpha=b-a-1,\ \beta=a(2b+1)\), and
\(\eta=4ab(a-b),\ \theta=-4a^2b(b+1)\). Direct expansion gives
\[
   \mathcal D=L^2-4ax(x-1)^2,\qquad
   \mathcal D-g^2=\eta x+\theta .
\]
The identity \(U=2x(x-1)y-L\) makes \(U^2=\mathcal D\)
equivalent to the divided difference equation
\(xy(x-1)(y-1)-a(x-1)(y-1)-bxy=0\).
For distinct nonpoles this implies \(f(x)=f(y)=s\).
Thus \(x,y,z=1+s-x-y\) split
\(X^3-(1+s)X^2+(s+a+b)X-a\).

The change of variables
\[
 X_E=2(U+g),\quad Y_E=(2x+\alpha)X_E+\eta
\]
gives \(Y_E^2=X_E^3+A_E X_E^2+B_E X_E+C_E\) with
\(A_E=\alpha^2-4\beta,\ B_E=2\alpha\eta-4\theta,\ C_E=\eta^2\).
For \(X_E\ne0\), use \(x=(Y_E-\alpha X_E-\eta)/(2X_E)\)
and \(U=X_E/2-g\) to invert. The other denominators in this
chart are nonzero by the modular unit checks. The marked
point is \(D=(0,-\eta)\), and the curve has the known
rational 3-torsion \(T=(4ab,4ab)\) from the earlier formula.
For each marked pair the checked smooth model and its
affine \([6]D,[9]D,[12]D\ne O\) certify nontorsion by the
rational torsion classification. The constructive witness
uses the standard affine chord and tangent law: for slope
\(m\), \(X_{\rm sum}=m^2-A_E-X_1-X_2\) and
\(Y_{\rm sum}=m(X_1-X_{\rm sum})-Y_1\); the doubling slope
is \((3X_1^2+2A_E X_1+B_E)/(2Y_1)\).
The exact script uses this law in left-to-right binary order.

Mapping the split roots back by \(X=u+\ell x,\ \tau=u+\ell s\)
gives the physical residual monic cubic
\[
  G=(X-\tau)B+\frac h{C_u\ell}(X-v)-\frac h{C_v\ell}(X-u).
\]
This follows from the normalized polynomial or from the root
sum and the products at the two poles. For \(Q=PG/B\), the
old two paid shifts combined with
\(\mathcal I(XP/(X-i))=iC_i\) show
\(\mathcal I(Q)=\mathcal I(XQ)=0\) over **\(\mathbb Q\)**:
the two residue contributions are \(0,-h\) in those two
rows, cancelling the contributions \(0,h\) of \((X-\tau)P\).
The update for the first unpaid moment is
\(h_Q=\mathcal I(X^3P)-h(\tau+u+v)\); each fresh root has
cofactor \(h/B(x)\).
The actual rational weights on each final squarefree rule are
\(w_x=C_x/Q'(x)\). Polynomial division then proves the
order from the two paid shifts and the nonzero \(h_Q\).

## Exact enclosures and replay admission

The initial same-candidate attempt at 288-bit dyadics stopped
on an unresolved doubling denominator; the
[stop](288-bit-stop.txt) and [partial stdout](288-bit-stop-stdout.txt)
are retained. Tightening only the identical provider's precision
to 768 bits, with all operations still outward-rounded, proves
the strict physical inequalities. The separate finite-field
evaluation checks every required divisor is a unit in
\(\mathbb Z_{(q)}\), so all normalized coordinates and weights
are exact rational straight-line expressions. Distinct or
nonzero residues imply the corresponding rational property.
Zero residue moments are only cross-checks; the rational
moment equalities use the identities above.

The two checked receipts are [order 19](exact-check.txt) and
[order 20](p20-exact-check.txt); the corresponding scripts
compare the literal first defects to \(1698450493\) and
\(240109312\). The 768-bit provider is an exact copy of the
earlier checker except for the one precision constant. See the
packet README for standalone commands using explicit provider
paths. This is exact mathematical evidence, not a Lean
certificate, positivity claim or stage-endpoint result.
