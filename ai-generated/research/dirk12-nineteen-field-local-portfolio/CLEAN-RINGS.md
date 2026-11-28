# Nineteen DIRK12 stages over clean rings

The [four rational tableaux](README.md) give exact order twelve in
nineteen stages over every nonzero **commutative clean ring** in which
\(12!\) is a unit. A ring is clean if each element is the sum of an
idempotent and a unit. This includes arbitrary products of local rings,
and includes commutative rings of Krull dimension zero. The proof uses
the same four literal tableaux, not new rooted computations.

## Partition by denominator units

The four literal denominators \(D_i\) generate the unit ideal, because
their integer gcd divides \((12!)^3\). Write \(1=\sum_i r_i D_i\).
Set \(a=r_1D_1\) and decompose \(a=h+u\) with \(h^2=h\) and
\(u\) a unit. On \((1-h)R\), \(a\) is a unit and therefore
\(D_1\) is a unit. On \(hR\), \(1-a\) is a unit and is a
combination of the remaining denominators. The factor \(hR\) is clean,
as it is a quotient of a clean ring. Induct on the remaining
denominators to obtain a partition of unity by orthogonal idempotents
\(e_i\), with \(D_i\) a unit on each nonzero \(e_iR\).

Use tableau \(i\) over \(e_iR\) and assemble the entries through
\(R\cong\prod_i e_iR\). Every order condition holds on every factor.
The two fixed scaled order-thirteen defects generate the unit ideal on
every factor, hence they do so in \(R\); thus they cannot both vanish.
The two distinguished diagonals likewise remain zero and a unit.

For the dimension-zero case, there is also a direct argument. If
\(d\) lies in a prime \(\mathfrak m\), then \(R_{\mathfrak m}\)
has only one prime and \(d/1\) is nilpotent. Some \(s\) outside
\(\mathfrak m\) satisfies \(s d^k=0\), so the basic open \(D(s)\)
is a neighborhood contained in \(V(d)\). Thus all \(D(D_i)\)
are clopen. Removing earlier opens from successive opens gives the
same partition of unity by their corresponding idempotents. A product
of local rings is clean because each local factor is clean and both
idempotency and invertibility are componentwise.

## Faithfully flat extension, not descent

For any nonzero commutative \(R\) inverting \(12!\), the algebra
\(B=\prod_i R[1/D_i]\) is faithfully flat and of finite
presentation over \(R\). Flatness follows from the finite product
of localizations, and faithfulness follows from their covering
\(\operatorname{Spec} R\). An explicit presentation adjoins
orthogonal idempotents \(e_i\) summing to one and elements \(z_i\)
with \(e_i z_i=z_i\) and \(D_i z_i=e_i\). Over \(B\), form the
same nineteen-stage tableau componentwise.

The extension does not descend that tableau to an arbitrary base ring.
The [single twenty-stage tableau](../dirk12-twenty-factorial-two-ports/README.md)
remains the best universal upper bound over the original ring. These
are mathematical corollaries of the exact literals, not new
kernel-checked Lean results.
