# An explicit signed rational 18-site rule of exact uniform order 20

The rule below is an exact **rational straight-line certificate** for
\(\mathcal I(f)=\int_0^1f(X)\,dX\). It gives 18 distinct contributing
sites, pays degrees \(0,\ldots,19\), and fails degree 20.
It allows signed rational weights and unrestricted rational sites.
In particular the retained site \(-3/32\) is outside \([0,1]\).
The certificate does not assert positivity, give a Runge–Kutta
stage upper bound, or add a Lean certificate.

The [uniform support existence theorem](../uniform-same-gap-seed/uniform-seed.md)
already gives a rule on \(p-2\) sites for each \(p\ge12\) in this
setting; here is a fixed explicit recipe at order 20. Together with
the [four-shift lower bound](../rational-quadrature-four-shift/proof.md),
the bracket remains 17–18. A 17-site rule is still open.

All final coordinates and weights are specified by rational expressions
with no parameter search or expanded large-integer coefficient table.
The certificate uses algebraic identities to pay the moments over
\(\mathbb Q\) and one exact finite-field trace to prove the rational
nonzero/unit conditions. A residue equality is not used to infer a
rational equality.

## Literal rational program

Use ordered root labels
\[
       (z,e_1,e_2,e_3,e_4,s,t)=(0,1,1,1,1,1/6,1/2).
\]
Their nodal polynomial is \(P=X(X-1)^4(X-1/6)(X-1/2)\).
It satisfies \(\mathcal I(P)=\mathcal I(XP)=0\), as shown by the
[uniform seed's Jacobi factor](../uniform-same-gap-seed/uniform-seed.md)
or by direct polynomial integration. The repeated entries here
are occurrences of a polynomial factor, not scalar quadrature sites.

In any row \(j\), let \(u,v\) be the two indicated root values,
\(P\) the current monic nodal polynomial, and set
\[
 C_u=\mathcal I(P/(X-u)),\quad C_v=\mathcal I(P/(X-v)),
 \quad h=\mathcal I(X^2P),\quad \ell=v-u,\quad
 a=\frac{h}{C_u\ell^3},\quad b=-\frac{h}{C_v\ell^3}.
\]
Remove the two labeled occurrences, and append the three distinct
root labels \(ja,jb,jc\) in the order
\[
 u+\ell\frac{a(b+1)}{a-b},\qquad
 u+\ell\frac{a-b}{a+1},\qquad
 u+\ell\frac{a+1}{b+1}.
\]
Here \(ja\) is a label (not multiplication), and all integrations
are exact rational coefficient sums with
\(\mathcal I(X^k)=1/(k+1)\).

| Row \(j\) | Pair to remove |
|---:|:---|
| 1 | \(t,e_1\) |
| 2 | \(s,e_2\) |
| 3 | \(z,e_3\) |
| 4 | \(1a,1c\) |
| 5 | \(4a,4b\) |
| 6 | \(5a,5b\) |
| 7 | \(6a,6b\) |
| 8 | \(7a,7b\) |
| 9 | \(8a,8b\) |
| 10 | \(9a,9b\) |
| 11 | \(10a,10b\) |

Rows 1–3 are the exact order-12 seed. Row 4 uses the seed's
marked pair \((25/57,51/70)\). The seven remaining rows use the
first two roots just inserted. This is one prescribed path of the
[uniform same-gap ladder](../same-gap-seed-ladder/seed-ladder.md)
using its rank-free move; no arithmetic on elliptic points is
needed on this branch. The numerator identities below hold for
the rank-free formula even at a singular elliptic parameter, so
later curve rank or smoothness is not needed for this certificate.

For the final polynomial \(P_{11}\) and its 18 root values \(x\),
the actual weights are the following rational expressions:
\[
                w_x=\mathcal I(P_{11}/(X-x))/P_{11}'(x).
\]
These definitions, not the residues in the replay, specify the
coordinates and weights over \(\mathbb Q\).

## Why the two rows pay exactly over the rationals

Write \(t_1,t_2,t_3\) for the three normalized coordinates of
one move, and \(x_1,x_2,x_3\) for their physical coordinates.
The displayed formulas give
\[
             \prod_i t_i=a,\qquad \prod_i(t_i-1)=-b.
\]
For the second identity the three factors are
\(b(a+1)/(a-b),-(b+1)/(a+1),(a-b)/(b+1)\).
Write \(B=(X-u)(X-v)\) and
\(\tau=x_1+x_2+x_3-u-v\).
The monic product of the three new factors equals
\[
 G=(X-\tau)B+\frac h{C_u\ell}(X-v)-\frac h{C_v\ell}(X-u).
\]
Indeed they agree in the degree-two coefficient by the root
sum. At \(u,v\) they agree by the two product identities.
Their difference has degree at most one and vanishes at two
distinct points, so it is zero over \(\mathbb Q\).

The next nodal polynomial is \(P_{\rm next}=PG/B\), even when
another copy of a removed value is retained. In
\(\mathcal I(P_{\rm next})\), the \((X-\tau)P\) term pays zero
by the old two rows, and the remaining contributions are
\(h/\ell\) and \(-h/\ell\).
In \(\mathcal I(XP_{\rm next})\), the first term contributes
\(h\); the other terms contribute \((u-v)h/\ell=-h\)
because \(\mathcal I(XP/(X-i))=i C_i\).
This proves the two exact paid rows at every step, starting
from the confluent \(P\).

At the final squarefree polynomial, the Lagrange weights integrate
every polynomial of degree at most 17. Dividing a polynomial of
degree at most 19 by \(P_{11}\) produces a quotient of degree at
most one, and the paid rows integrate that term to zero. For
degree 20, the first residual is
\(h=\mathcal I(X^2P_{11})\), which equals integral minus rule at
\(X^{20}\) by division and the two exact paid rows.

## Why the bounded trace proves the required inequalities over Q

The [exact checker](verify-order20-slp.py) works in the certified
prime field \(q=2147483647\). Each rational expression in the
fixed program is evaluated in the local ring \(\mathbb Z_{(q)}\):
the input denominators are units, and the checker verifies a
nonzero residue **before every inverse**. Inductively the
rational evaluation is well-defined and reduces to the computed
residue. Polynomial products, cofactors and the moment values
use only this arithmetic. Uniform moment denominators in the
degrees used here are at most 21. Distinct residues certify
distinct rational sites, and nonzero cofactor residues certify
nonzero rational weights once the final sites are distinct.
In the first three rows the only repeated rational values are
the known surviving labeled endpoint copies.

At row 11 there are 18 distinct residues and all weights have
nonzero residue. The first residual has
\[
                 h\equiv570922002\ne0\pmod q .
\]
Thus the previously paid uniform rule has **exact order 20**.
The checker also evaluates all 21 scalar moments modulo \(q\)
as an independent arithmetic cross-check, not as the proof
of their rational equalities. The final label order and every
residue are in [the frozen output](exact-check.txt).

## Bit-growth forecast and observed replay

The verified order-12 seed has node numerator/denominator maximum
bit-lengths \(1,6,6,7,27,40,40,123,240,240\), summing to 730.
The next-defect bit-length is 739; each normalized initial
marked parameter has bit-length 741. These are exact
preflight measurements, not estimates at later orders.

For an expansion forecast, take \(H_i=\log_2\max(|p_i|,q_i)\)
for each reduced node \(p_i/q_i\) with \(q_i>0\), \(S=\sum H_i\),
and \(K=H_u+H_v\). A primitive factor product
\(P_*=\prod(q_i X-p_i)\) has coefficient one-norm at most
\(2^{S+n}\) for current width \(n\). With
\(M=\mathrm{lcm}(1,\ldots,n+3)\), use
\(H_*=M\mathcal I(X^2P_*)\) and
\(J_i=M\mathcal I(P_*/(q_iX-p_i))\), which are integers.
Then \(h/C_i=H_*/(q_iJ_i)\). Write
\(d=p_vq_u-p_uq_v\), \(Q_*=q_uq_v\), and
\[
 a=N/U,\quad b=N/V,\quad N=H_*Q_*^3,\quad
 U=q_uJ_u d^3,\quad V=-q_vJ_v d^3 .
\]
All three integer heights are at most
\(Z=S+3K+n+\log_2 M+3\): the signed pair difference numerator
has height at most \(K+1\), and its cube supplies the extra
\(3K+3\). In these variables the normalized triple is
\[
 \frac{V+N}{V-U},\qquad
 \frac{N(V-U)}{V(U+N)},\qquad
 \frac{V(U+N)}{U(V+N)} .
\]
Its aggregate height is at most \(5Z+3\).
Changing back to physical coordinates adds at most \(K+2\)
per root, and the removed pair subtracts \(K\). Thus a
conservative recurrence for expanded node height is
\[
       S_{\rm next}\le 6S+17K+5(n+\log_2 M)+24 .
\]
This is an upper envelope, not a lower bound on reduced heights;
cancellation can be substantial. Even the low-pair \(6S\)
component iterated eight times from the measured seed scale
is about \(1.23\times10^9\) bits before cancellation.
A full expansion was therefore not attempted or characterized
as small. The rational straight-line specification certifies
all steps without incurring those heights.

The deterministic checker has a 2-second per-step and 15-second
total wall stop, 40,000/350,000 per-step/total modular fold limits,
and a 63-bit cap on folded temporaries. The trace uses 41,658
folds with a 62-bit maximum and no group-law increments.
No giant rational coefficients are expanded.

Run `python3 verify-order20-slp.py` in this directory for
standard-library replay. The referenced published inputs are
pinned in [the repo-root-relative manifest](proof-inputs.sha256).
