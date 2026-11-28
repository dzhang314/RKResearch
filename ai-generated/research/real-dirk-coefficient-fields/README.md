# Exact coefficient-field degrees of two real DIRK witnesses

The literal real DIRK tableaux already in the repository generate fields
of **degree 18 over the rationals at order ten, width 11**, and **degree
16 at order eleven, width 14**. These are not lower bounds on the
coefficient field of any other tableau. Neither the stage bounds nor the
rooted-order certificates change.

## DIRK10, eleven stages

In the [literal construction](../causal-profile-reduction/dirk-order10-eleven-real-algebraic.md),
the front cubic for \(k\) is \(125k^3-100k^2-87k+1314\). It is irreducible
modulo 13: its leading coefficient is nonzero and no residue is a root.
Thus \(K=\mathbb Q(k)\) is cubic.

The exact replay reconstructs the monic suffix cubic \(S\) from the
published interpolation and verifies that it equals the first suffix
relation in the coefficient export. The front polynomial has a simple
root \(k=18\bmod 23\) and a simple root \(k=9\bmod 11\). Each simple
root lifts to its respective \(p\)-adic field by Hensel's lemma and gives
an embedding of \(K\) there. The reconstruction denominators and leading
coefficient of the unnormalized suffix are units at these embeddings.

| Place | Monic suffix modulo the prime | Test |
| --- | --- | --- |
| \(23\), \(k=18\) | \(X^3+3X^2+6X+21\) | No root |
| \(11\), \(k=9\) | \(X^3+9X^2+X+1\) | Discriminant \(2\), nonsquare |

A root in \(K\) would be integral at the first place because the cubic
is monic with integral coefficients. A square discriminant in \(K\)
would have a square nonzero reduction at the second. Thus the cubic is
irreducible with nonsquare discriminant; its splitting field over \(K\)
has degree six.

The row sums of the literal export recover \(y=c_6\) and its three suffix
roots \(c_8,c_9,c_{10}\). The displayed Möbius formula for \(y\) has
determinant \(-32965170\), so \(y\) determines \(k\). The literal
coefficient field is therefore the full splitting field over \(K\),
of degree \(3\cdot 6=18\) over \(\mathbb Q\).

## DIRK11, fourteen stages

In the [literal construction](../dirk11-width14-real-reflected-shell/README.md),
put \(r=\sqrt{15}\), \(u^2=(15+2r)/33\), and \(v^2=(15-2r)/33\).
Over \(\mathbb Q(r)\), each radicand has nonsquare rational norm
\(5/33\). Their product is \(5/33\), which is itself nonsquare in
\(\mathbb Q(r)\): a rational number is a square in this quadratic field
only if it is a rational square or \(15\) times a rational square,
and neither applies. Thus their two square classes are independent,
giving an eight-dimensional grid field.

The residue chain \((r,u,v)=(12,40,17)\bmod 43\) consists of simple roots
of the three monic relations. It lifts successively into \(\mathbb Q_{43}\).
The fourth monic relation of the exact export has integral coefficients
at this place and reduces to \(X^2+5X+28\), with discriminant
\(42=-1\bmod43\), a nonsquare. Consequently the fourth relation
doubles the degree.

The row sums recover the two grid radicals through
\(u=2(1-c_{12})-1\), \(v=2(1-c_{11})-1\); either grid formula then recovers
\(r\). Write \(Y_i=1-c_i\), and let \(b_i\) be the output weights. The
fourth generator \(g_b\) is recovered from the literal weighted
transpose at the first physical reverse \(b\)-row:
\[
 g_b=\frac{\sum_{j=12}^{14}b_j A_{j,12}Y_j^2}{b_{12}}-Y_{12}^3/3.
\]
These three rows were not merged in the forward construction, and
\(b_{12}\ne0\). The replay verifies the cleared identity directly
from the exact exported entries. Thus the literal field is the full
four-layer tower of degree \(16\).

Run **python3 -B check.py** from this directory. It reconstructs the
small-prime polynomials, tests the actual residue and triangular
generator relations, and checks both recoveries against the published
exact exports. It uses only standard-library arithmetic and the
existing exact quotient-ring implementation. The field-degree
deductions above are mathematical, not new Lean theorems.
