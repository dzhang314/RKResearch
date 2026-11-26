# An exact 64-stage explicit method of order 19

This tableau has exact order 19 over \(U\coloneqq\mathbb Z[1/19!]\)
and after every base change to a nonzero commutative ring. The
earlier 65-stage tableau is unchanged. The saving is one reverse
donor, with no new scalar stages and no extra denominator prime.

## The asymmetric scalar rule and the missing read

Keep the unchanged 27-row forward chart through tree size nine.
Keep only the first 20 rows of the 21-row reverse chart, dropping
the last primitive at centered reverse clock 2. Write
\(v\coloneqq2y-1=1-2x\), with \(y\) the reverse clock and \(x\) the
physical clock. On polynomials in \(v\), define
\[
 (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^{v}f(z)\,dz,
 \qquad
 \mu(f)\coloneqq\tfrac12\int_{-1}^{1} f(v)\,dv.
\]
The seven retained old reads are the true origin, five actual
grade-eight point reads, and the promoted high-seven contrast
from the prior 15-row bank. The ambiguity through polynomial
degree seven is the span of
\[
 Q(v)\coloneqq v(v+1)(v+2)(v^2-1/4)(v-1/3)(v-52/51).
\]
The retained reads invert paidly on degree at most six.
Their decoder \(D_0\) gives every ideal derivative through size
eight modulo \(Q\). The receipt verifies the corresponding 200
small rooted reads of sizes one through eight on the actual
unchanged rows.

The original centered grid used labels \(0,\pm1,\pm2,\pm3,\pm4,
\pm5,\pm6,\pm7,\pm8,\pm12\), all divided by six. Remove
labels \(+8,-7\) and insert \(+9,-10\).
Every old pure clock stays present. All site differences are
paid units. Write \(\lambda_a\coloneqq\mu(\operatorname{card}_a)\)
for the cardinal weights at the new sites. Nineteen distinct
sites give degree-18 scalar exactness, which is all that order
19 requires. No extra nodal-hull moment is imposed.

The pure sites are
\[
 \{-1,1\}\cup S,\qquad
 S\coloneqq\{-2,-1/2,-1/3,0,1/3,1/2,2\}.
\]
The ten remaining sites are live, with negative sites earlier
and positive sites later in the reverse chronology. In increasing
clock order their stripped mass numerators are
```
13163989 339843953 19015120457 1011113 2373593
138920867 1496962133 860332399 130380079 1419181
```
They are pairwise coprime. Thus at most one live mass vanishes
modulo any unpaid prime. This is the relevant distinction from
the symmetric grid, on which a whole pair can vanish. Moving
just one member of a pair does not in general remove the problem.
The replaced site's new mass is a paid unit times its old mass,
and its remaining mirror's mass changes by a multiple of that
same old mass.

The early live receiver at site \(a\) uses \(\mathcal I_aD_0\).
It is exact through reverse word length seven. The early
weighted differences from \(D_0\) recover the missing coefficient
of \(Q\) by a paid one-column left inverse. In particular two
of the stripped factors of the measurements \(\lambda_aQ(a)\)
are \(2373593\) and \(43477859\), with gcd one. Denote
the resulting paid linear read of old and early data by
\(\eta\). Set \(D\coloneqq D_0+Q\eta\) and
\(K\coloneqq\mathcal I Q\). The decoder \(D\) returns the exact
model through reverse word length seven.

## A monic mask for the additional reverse degree

At word length eight, write \(\sigma\) for the difference
between the exact model and \(D\) on the actual data.
It vanishes at the reverse origin and lies in
\((1+v)\mathcal P_7\), where \(\mathcal P_d\) consists of
polynomials of degree at most \(d\). A receiver has discrepancy
from the ideal model equal to a common scalar \(\kappa\) times
its mask value \(\delta(a)\). On the early tier this value
must be \(-K(a)\); on the later tier it is chosen by adding
\(\delta(a)\eta\) to the incoming row \(\mathcal I_aD\).
For a word ending in an application of \(L\), the scalar
\(\kappa\) is \(\eta\) on the preceding word. It is zero for a
clock multiplication. The measured weighted difference at
site \(a\) from \(D\) is therefore
\[
  \lambda_a\bigl(\sigma(a)+\delta(a)\kappa\bigr).
\]

The two-tier construction permits a useful choice of the mask:
take it in the form
\[
 \delta(v)\coloneqq (1+v)(v^8+P(v)),\qquad P\in\mathcal P_7.
\]
The five required early values and two linear compensation
equations, given below, have a simultaneous paid solution for
the eight coefficients of \(P\). The literal coefficients
and these seven equations are independently checked.
After subtracting the lower polynomial columns from the
augmented measurement matrix, the mask column is just
\((1+v)v^8\). Every nine-site determinant is then a weighted
Vandermonde. Its only unpaid factors can come from the
nine site masses, because the differences and factors
\(1+a\) are units. The ten masses have pairwise coprime
unpaid parts. Consequently the ten nine-site determinants
generate the unit ideal. This proves the needed paid left
inverse without dividing by any single mass.

The same argument applies whenever the right polynomial
space is \(G_0\mathcal P_{d-1}\) and the mask constraints admit
\(G_0(v)(v^d+P(v))\) with \(P\in\mathcal P_{d-1}\).
A maximal minor from \(d+1\) good sites is a Vandermonde
times the site masses and \(G_0\) factors. Thus the arithmetic
question is whether \(d+1\) sites survive at every unpaid
prime, separately from how the mask is paid.

## Compensating the two left source levels

For the intermediate source budget take
\(S_1\coloneqq S\cup\{-1\}\) and
\[
 F(v)\coloneqq(1-v)\prod_{a\in S_1}(v-a).
\]
Forward residuals at source sizes ten and eleven and the
primitives of the size-ten ones all lie in \((1-v)\mathcal P_9\),
because the physical origin is exact. The kernel of evaluation
at \(S_1\) on this space is spanned by \(F,vF\).
The two verified compensation constraints on the monic mask are
\[
   \sum_{a\,\mathrm{live}} \lambda_a\delta(a)F(a)a^j=0,
   \qquad j=0,1 .
\]
They allow the defect on the live sites to be canceled by a
paid functional on the existing pure sites in \(S_1\).

The highest pairing only uses the actual size-ten residuals.
Those have both boundary factors and obey the pin on the
quotient by \(1-v^2\) with coefficient row
\[
  (-2487,-6632,1473,3928,5433,14488,9393,25048).
\]
On the monic hull of \(S\) this pin has value \(-31616\),
a paid unit for order 19. Thus the seven-site pin-zero
interpolation represents the actual highest pairing.
There is no highest correction at the extra pure site \(-1\).

The virtual reverse order lists 20 old donors, five early
and five later live rows, the 20 negative old copies, nine
pure scalar rows, and the 16 signed late correction rows at
\(S_1\). The latter apply the compensated functional to
\(\eta\) and add the paired primitive of the recovered
\(\sigma\). Every tap into a live receiver factors its
actual mass, as does the paid normalization of the reverse
transpose. The cross block is the forward primitive minus
the transposed suffix acting on the forward chart's point
values, exactly as in the preceding weighted construction.

A rooted source error begins with a child of size at least
ten, so two erroneous primitive factors cannot occur through
order 19. Move the remaining error path to the reverse side.
A source of size \(k\) sees a word of length at most \(18-k\)
and then one extra \(L\). Only lengths seven and eight are
affected by the new mask. At length seven the source is at
most size eleven, so the compensation on \(S_1\) suffices.
At length eight the source is size ten. Both the source and
its physical primitive are in the compensated space, and
the highest correction on \(S\) supplies the missing reverse
primitive. All ideal pairings agree by triangular polynomial
integration through degree 18. This proves every rooted
condition through order 19. Independently the finite receipt
verifies all actual source pairings at both affected word
lengths, by normalized rooted attachments through size eleven.

The same-clock pure rows fold as full numerical predecessor
rows. The pure physical origin and clock-one rows again agree
literally with existing forward rows 0 and 16, with indices
starting at zero. No active donor is counted as an alias.
The final count is
\[
  27+20+19-2=64.
\]

## Exactness at the next order

The independent checker evaluates eight actual size-20 rooted
outputs in two formal-zero grafts. Use the same size-seven
combination \(\mathcal V\) as in the order-17 construction:
the four words `ACCACC`, `ACCAAC`, `ACCCCC`, `CCCCCC`
with coefficients \(136080,-272160,204120,-34020\).
Here \(C\) multiplies by the stage clock and \(A\) extends
the rooted weight. Set \(w\coloneqq C A C^2\mathcal V\).
The actual raw outputs of \(C^8Aw\) and \(C^7A^2w\) are
\[
 -1552399572022214961505/55515199094784,qquad
 21660214453692068872891429459/174406549476173414400 .
\]
Their paid combination equals one. Independently, the first
two individual trees of the first graft have cleared defects
\[
 1123774196317537919294796223/3021803317127282688,qquad
 3204088976399915389469032543/3021803317127282688 .
\]
The exact integer blend is
\((-1138061711829972260047482753030323321845579776,
399153829681869843924535683499004879466135552)\).
It equals one, so no nonzero factorial-unit base change can
kill every order-20 defect.

The literal denominator
`14465776924504728356573570347154257920000000000` divides
\((19!)^5\), and the weight denominator
`2127745531711800000` divides \((19!)^2\).
The grid itself is not an order-20 scalar rule: its centered
monic hull has mean \(-213309881/576762288480\).
The exact order-19 claim uses neither a higher-version Lean
certificate nor an assumption that the same grid passes that
extra moment.

## Reproduction

From this directory, run:

~~~sh
python -B design19.py ..
python -B check19.py .. tableau-19-factorial-64.json receipt-19-factorial-64.json \
  ../order-19-factorial-65/receipt-19-factorial-65.json
out=$(mktemp -d)
python -B build19.py .. "$out"
cmp tableau-19-factorial-64.json "$out/tableau-19-factorial-64.json"
cmp receipt-19-factorial-64.json "$out/receipt-19-factorial-64.json"
~~~

The independent checker uses exact rational arithmetic and imports neither the design nor the builder. The [previous 65-stage construction](../order-19-factorial-65/README.md) remains available. This is not a Lean certificate.
