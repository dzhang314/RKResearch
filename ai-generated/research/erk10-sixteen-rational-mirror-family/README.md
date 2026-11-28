# A deterministic rational family of 16-stage ERK10 tableaux

The [first rational witness](../erk10-sixteen-rational-mirror/tableau.json)
can be rebuilt without a search. The same construction gives the
two shorter-denominator literals here. Their 1,205 ordinary
rooted-tree conditions were independently checked with denominator-cleared
integers. Two order-eleven defects have coprime numerators in each
literal, so exactness holds in every nonzero commutative ring inverting
its literal common denominator.

| Horizon | Raw reverse clocks | Common denominator |
| ---: | --- | ---: |
| \(4\) | \(1,2/3,1/3,2/3,-26,3/4,27,1/4,1/2\) | 421382472598873671046748625598560000 |
| \(5/4\) | \(1,2/3,1/3,2/3,5/7,1/5,2/7,4/5,1/2\) | 1320541052251127574067200000 |

The defects, in order on the eleven-vertex bush and the root with
four leaf children and one six-vertex bush child, are respectively
\[
 \left(-\frac{46337}{103680},\frac{723883}{48384000}\right),\quad
 \left(\frac{1691}{27783000},-\frac{50329}{357210000}\right).
\]
A nonzero rational numerator has an integral Bézout combination with
its companion giving 1. If both normalized discrepancies vanish
after any specialization inverting \(D\), so do both numerators,
which is impossible in a nonzero ring.

## Why fixing one evaluation makes the pressure linear

The raw reverse chronology is
\((1,A,B,A,C,D,R,E,\xi)\) with \(A=2/3\), \(B=1/3\),
\(C=1-R\), and \(\{D,E,\xi\}\) the center and a reflected pair.
Together with the old zero-clock mass the nine distinct clock sites
are symmetric, hence their cardinal-integral weights pay degree nine.
Split the mass at \(A\) evenly between its two physical rows.
Let \(p=1-A,\ q=1-B\), \(y=1-x\).
The second raw read defect \(\boldsymbol U\) is opposite at the
two copies of \(A\), zero elsewhere. The cofactor vector
\(\boldsymbol V\) annihilates \(X,\ldots,X^6\), split at the
copies of \(A\) in proportion to their weights.
The first three strict rows are compatible exactly when
\(\mu_A p(3q-2p)=\mu_Bq^2\), where the \(\mu\)'s are
cardinal integrals before dividing by the nodal derivatives.
This holds because \(\mu_A=\mu_B\) and \(q=2p\).
The next rows pay the same four reverse reads using the first
four donors. The two remaining profiles are
\(K\boldsymbol M_3-\boldsymbol M_4/4\) and \(K\boldsymbol V\),
with \(M_{j,i}=w_i y_i^j\).

On the four base donors, the first terminal profile, tested
against the degree-six source space, integrates
\(L(y)=-y^2(y-2/3)^2/4\). The cofactor action integrates
\(\alpha y^2/2\), where \(V_i=\alpha M_{1,i}\) on those donors.
The first adjustable donor is \(C\). Taking the linear combination
of the two terminal profiles that is unchanged by a compensated
tap into \(C\) replaces the two weights by
\[
 L(y)-m y^2,\qquad
 m=\frac{1/9-J/I}{8},\quad
 I=\frac{2V}{15}-\frac{2}{35},\quad J=\frac{2V}{35}-\frac{2}{63}.
\]
Here the scalar \(V\) in \(I,J\) is the *squared normalized radius*
of the reflected pair in \(\{D,E,\xi\}\), not the cofactor vector.
The radius of \(C,R\) disappears: its difference from the early
squared radius \(1/9\) is a factor of both the two-donor
response difference and the corresponding cardinal-integral
difference.

On \(f_4=X(X-\xi)(X-R)(X-E)\), \(f_5=Xf_4\), only this combined
terminal pressure can constrain the geometry. The two values of
the dense-prefix functional \(\ell\) are from evaluations at
\(\xi v/\theta,\,2\xi/\theta\), where
\(v=\theta(12\theta^2-45\theta+40)/(15(\theta-2)^2)\).
Choose either evaluation site to equal \(E\). On the two blind
tests only evaluation at the other site \(r\) remains, up to a
nonzero scalar. Their pressure reduces to
\[
 \int_0^1 (X-R)X(X-\xi)(X-E)(X-r)
              \bigl[L(1-X)-m(1-X)^2\bigr]\,dX=0.
\]
Hence \(R\) is a ratio of integrations of rational polynomial
coefficients. The code does not infer order solely from this
singular-ray condition: it solves every literal terminal test
and checks the four reverse reads and exact physical endpoint
merge. It rejects collisions, singular dimensions, and zero
pivots. Independent replay certifies the listed outputs.

In the command line, case 0 fixes \(\xi=1/2\);
case 1 fixes \(E=1/2\); case 2 takes \(D=1/2\)
and \(E=1-\xi\). Anchor b identifies \(E=2\xi/\theta\)
and anchor a identifies \(E=\xi v/\theta\).
The original witness is case 2, anchor b, \(\theta=-1/2\).
Both shorter witnesses are case 0, anchor b.

## Coefficient domains covered

The unpaid prime intersection for the two displayed denominators
is \(\{11,13,19\}\). Those primes have certified mathematical
[all-power families](../erk10-sixteen-small-prime-portfolio/README.md).
Thus every characteristic-admissible field, every \(\mathbb Z_p\)
and \(\mathbb Q_p\) at paid primes, and every nonzero finite-characteristic
commutative ring in which \(10!\) is a unit has a sixteen-stage exact
ERK10 upper bound. For finite characteristic, select the available
tableau separately on each prime-power component and use the integer
Chinese remainder theorem in the same sixteen slots. This also covers
unequal exponents and mixed characteristic. Neither literal is a
single tableau over the full factorial localization.

The first rational witness removes 19 from the denominator
intersection of the three. For a general local ring with \(10!\)
a unit, the three rational tableaux alone therefore suffice whenever
the residue characteristic is not 11 or 13. No arbitrary local
conclusion for those two characteristic-zero residue cases is
made here; the finite-characteristic proof applies regardless.

## Replay

    python3 -B family.py --emit /tmp/rebuilt-first-rational.json
    cmp /tmp/rebuilt-first-rational.json ../erk10-sixteen-rational-mirror/tableau.json
    python3 -B family.py --theta 4 --case 0 --anchor b --emit /tmp/rebuilt-theta4.json
    cmp /tmp/rebuilt-theta4.json theta4-tableau.json
    python3 -B family.py --theta 5/4 --case 0 --anchor b --emit /tmp/rebuilt-theta5-over-4.json
    cmp /tmp/rebuilt-theta5-over-4.json theta5-over-4-tableau.json
    python3 -B verify.py theta4-tableau.json theta5-over-4-tableau.json
    python3 -B denominator-audit.py
    sha256sum -c sha256.txt

The deterministic builder uses standard-library rational arithmetic
and the already reviewed dense-prefix helper. The check is independent
of the construction and reads only the literal coefficients.
