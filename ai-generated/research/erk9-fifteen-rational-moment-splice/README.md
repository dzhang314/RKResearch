# Exact rational ERK order nine in fifteen stages

**Current rational upper bound:** the [14-stage rational method](../erk9-fourteen-rational-triple/README.md) supersedes this 15-stage rational construction. The separate factorial-unit ring question is covered by the [universal 15-stage method](../erk9-fifteen-ten-clock/README.md).

The [literal tableau](tableau.json) has **exact order nine in fifteen
physical explicit stages over \(\mathbb Q\)**, hence over every
characteristic-zero field. This reduces the previous rational
sixteen-stage upper bound. It is not a claim of a minimum. The
previous sixteen-stage **factorial-localized** upper bound remains
separate: the common denominator of this particular witness is
\[
\begin{split}
D&=167647010724053278598487250944000\\
 &= 2^{14}3^6 5^3 7\,11^2 13^5 19\cdot43\cdot47\cdot59\cdot83\cdot241\cdot7879.
\end{split}
\]
The coefficient identity also transports to any nontrivial commutative
ring in which \(D\) is a unit; no field or order is needed for that
conditional statement.

## The new one-row rational chart

Use the [nine-stage rational prefix and decoder](../../upper-bounds/real-algebraic/erk14-order9-seven-clock/prefix.json)
of the previous seven-clock real-algebraic control. Scale its
matrix by \(\xi=2/3\), and decoder coefficient in degree \(j\)
by \(\xi^{-j}\). The three literal reusable ports are the origin,
\(\xi\), and \(\xi/2\).

Order nine needs scalar precision eight, not nine: a source
polynomial from a tree of size \(n\) has degree at most \(n-1\);
a reverse word has length \(\ell\le8-n\); either primitive in
the payment raises the degree by one, so its products have
degree at most \(n+\ell\le8\).

Choose fresh clocks \(v=1/4,\ w=3/4,\ z=-1/2\). With \(P\)
the monic hull of \(0,1,\xi,\xi/2,v,w,z\), the one missing
eight-node moment fixes the fourth fresh clock \(t\) by
\[
   t=\frac{\int_0^1 XP(X)\,dX}{\int_0^1 P(X)\,dX}
     =\frac{-11/40320}{-13/30240}
     =\frac{33}{52}.
\]
This makes the eight distinct-site interpolatory quadrature
exact through degree eight. Its signed masses are all nonzero.
Split the mass at \(\xi\) equally between two reverse labels,
at \(\xi_{\rm donor}\) and \(\xi_{\rm old}\).

The reverse chronology is
\[
 (1,\xi_{\rm donor},v,w,z,t,\xi/2,\xi_{\rm old},0).
\]
Writing \(\boldsymbol y=1-\boldsymbol x\), set
\(\boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2\),
\(\boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3\),
and \(\boldsymbol h=L\boldsymbol u\). Require
\(L\boldsymbol 1=\boldsymbol y\) and give \(\boldsymbol u\)
opposite entries on the two copies of \(\xi\), zero elsewhere.
The row at \(v\) determines \(g_v,h_v\); the row at \(w\)
chooses \(h_w=0\) and computes \(g_w\) from its actual three
donors. The new two rows at \(z,t\) each have four independent
donor vectors. They therefore solve the two exact moment
payments separately for \(\boldsymbol g\) and \(\boldsymbol h\),
with no compatibility equation on the geometry. The determinant
uses the two distinct values \(s(s-\xi)\) at \(s=z,t\).

The source space for the two-letter payments is
\(X(X-\xi)(X-\xi/2)\langle1,X(X-\xi)\rangle\), unchanged
from the [earlier control](../../upper-bounds/real-algebraic/erk14-order9-seven-clock/EXACT-PROOF.md).
The paired \(\boldsymbol u\) has zero aggregate. The suffix is
the reverse weighted transpose with the literal prefix cross
feed. Its three initial forward virtual rows evaluate the whole
old incoming rows, so they contract exactly into the three
prefix ports. This leaves \(9+9-3=15\) distinct physical rows.

## Exact replay and next-order failure

The constructor checks all quadrature and reverse-profile
conditions and then tests every ordinary rooted condition
through nine. Independently, the second script reads only the
literal JSON and replays every order condition with a
denominator-cleared integer matrix. Both cover all 486 ordinary
rooted trees, with no floating-point tolerances.

The cleared tenth-order tall and bush defects are
\(-29627/5184\) and \(5/9984\), respectively. They give the
integer Bézout identity \(2(-29627)+11851(5)=1\) after their
respective denominator clearings. Thus they cannot both vanish
over a nontrivial ring in which \(D\) is a unit.

Replay:

    python3 check.py
    python3 audit_tableau.py
    sha256sum -c source-sha256.txt

The existing prefix input has SHA-256
49e854cdda01628174223f46ba8bc9da03e1b8706b774380f7a4db9820a4f370.
This exact arithmetic packet does not yet claim a closed native Lean
theorem for the concrete tableau.
