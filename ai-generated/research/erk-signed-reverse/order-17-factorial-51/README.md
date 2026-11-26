# An exact 51-stage explicit method of order 17

The tableau has exact order 17 over \(\mathbb Z[1/17!]\) and after
every base change to a nonzero commutative ring. It drops one
reverse donor from the earlier 52-stage method. The old tableau
is unchanged. This is an upper bound, not a claim of minimality
or a Lean certificate.

## The one missing donor read

Keep the forward chart unchanged, with 22 rows and exact rooted
derivative polynomials through size eight. Use the first 14 rows
of the retuned grade-seven chart as the reverse bank, dropping
the last primitive at centered reverse clock \(1/2\). Write
\(v\coloneqq2y-1=1-2x\), where \(x\) and \(y\) are the forward
and reverse clocks. Define the polynomial integral and mean by
\[
  (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^{v}f(z)\,dz,
  \qquad \mu(f)\coloneqq\tfrac12\int_{-1}^{1} f(v)\,dv.
\]
The two endpoints, three retained new reads and the old contrast
are six exact reads through tree size seven. Their remaining
monic degree-six ambiguity is
\[
 Q(v)\coloneqq(v^2-1)(v+1/2)(v^2-1/9)(v-4/5).
\]
In particular the retained reads determine a paid decoder
\(D_0\) of degree at most five; it agrees with every ideal size-seven
derivative polynomial modulo \(Q\). The checker verifies all 85 local
rooted reads of sizes one through seven on the unchanged reverse
rows, including the exact projected response at size seven.

The scalar grid is the prior 17-site rule with zero and both signs
of \(1/5,1/3,1/2,2/3,1,3/2,2,5\). The pure sites are the actual
reverse donor clocks, including the endpoints. The five pure
interior sites used for corrections are
\[
 S\coloneqq\{0,\pm1/3,\pm1/2\}.
\]
The other ten sites are live: the negative signs form the early
tier and the positive signs the later tier. All pairwise site
differences are paid units, and the same cardinal weights
\(\lambda_a\) still integrate through degree 16.

An early row uses \(\mathcal I_aD_0\). These rows therefore
give exact reverse word values through length six. Taking the
weighted difference of an early reading and the old prediction
at its clock extracts the missing coefficient of \(Q\): the
five numbers \(\lambda_aQ(a)\) generate the unit ideal. Two of
the stripped numerators, at \(-2\) and \(-1/5\), are 3307 and
792809, with integer blend \(170213\cdot3307-710\cdot792809=1\).
Write \(\eta\) for that paid linear read and set
\[
 D\coloneqq D_0+Q\eta,qquad K\coloneqq\mathcal I Q.
\]
Here \(D\) returns the exact model through reverse word length six.

## The compensated left and weighted right tests

Let \(H(v)\coloneqq1-v^2\) and \(Q_S(v)\coloneqq\prod_{a\in S}(v-a)\).
On the forward side the first-excess residuals, from size-nine
children, vanish at both endpoints and have zero mean. The
size-ten child residuals vanish at both endpoints as well.
Thus these residuals and the physical primitives of the size-nine
ones all belong to \(H\mathcal P_7\), where \(\mathcal P_j\)
consists of polynomials of degree at most \(j\).
Evaluation on \(S\) has kernel \(H Q_S\mathcal P_2\) in this space.

At an early live site set \(\delta_a\coloneqq-K(a)\).
At a later live site use an incoming row
\(\mathcal I_aD+\delta_a\eta\). Its parameter is chosen so that the
three masked moments vanish:
\[
 \sum_{a\,\mathrm{live}}\lambda_a\delta_a H(a)Q_S(a)a^j=0,
 \qquad 0\leq j\leq2.
\]
These equations have a paid solution. For example, give the positive
sites the row matrix
\[
 B_{aj}\coloneqq\lambda_a H(a)Q_S(a)a^j
 \qquad(0\leq j\leq2).
\]
Its maximal minors have a paid left inverse \(J\); the point and
hull factors are units, and there are five mass groups of which at
most one can vanish modulo any unpaid prime. The actual choice is
\(J^{\mathsf T}t+(I-J^{\mathsf T}B^{\mathsf T})e\), where \(t\)
is the negative of the early masked moments, and \(e\) selects the
later coordinate \(2/3\). The second term is in the kernel of
\(B^{\mathsf T}\). This is the exact adjustment needed by the high
test, not a change to the required left equations.

At reverse word length seven, let \(\sigma\) be the exact model
polynomial minus the decoder \(D\) on the actual old and early data.
It vanishes at the reverse origin, so it belongs to
\((1+v)\mathcal P_6\). The measured differences from \(D\) at all
ten live sites are
\[
  \lambda_a\bigl(\sigma(a)+\delta_a\kappa\bigr),
\]
with one extra scalar \(\kappa\). If the last applied letter is
\(L\), this scalar is \(\eta\) on the preceding word, and otherwise
it is zero. The ten-by-eight matrix on the seven polynomial
coordinates and the mask has a paid left inverse. Its five
eight-site minors, each omitting the two signs of one radius,
generate the unit ideal. The five respective unpaid parts of the
masses are 792809, 1579243, 482561, 3307 and 616087. The omitted
radius minors include the case of the prime 37 killing the pair
\(\pm5\); the unadjusted choice of mask failed at that prime.
The receipt gives all five tested determinants and their exact
Bézout identity. No individual mass is divided out.

For the highest left pairing, the actual size-nine source quotient
by \(H\) satisfies the two previously verified pin rows
\[
 (-1200,5,-192,5,-48,5,0),\qquad
 (105,0,21,0,9,0,5)
\]
in ascending coefficient order. Their values on \(Q_S,vQ_S\) are
the columns \((10/3,0)\) and \((12,7/3)\). The determinant \(70/9\)
is a unit, so the five pure sites recover the exact paired source.
This uses the two pins only on the actual first-excess source.
The larger test at source size ten uses the three masked moments
instead.

## Chronology and rooted order

The virtual reverse order lists the 14 old rows of mass one,
the five early live and five later live rows, the 14 negative
copies of the old rows, the seven pure scalar rows and two
signed late rows at each of the five sites in \(S\).
Each late positive row adds to \(\mathcal I_aD\) two terms:
the compensation functional on \(\eta\), and the missing
paired primitive from the high decoder. Its negative companion
takes the unmodified primitive. On the first term, the three
masked moment equations ensure that the functional
\(f\mapsto-\sum_{a\,\mathrm{live}}\lambda_a\delta_a f(a)\)
is represented on \(S\) throughout \(H\mathcal P_7\).
On the second, the pin-zero interpolation of the top forward
source uses the same five sites. All late taps into either live
tier factor their respective masses; the normalized weighted
transpose is strict in the forward physical chronology.

The single primitive error in a rooted product has a source
child of size at least nine. Two such errors require at least
19 vertices and cannot occur through order 17. Move a
propagated error path to the weighted adjoint side. A source
child of size \(k\) then sees a reverse word of length
\(d\leq16-k\) and an extra application of \(L\) on that word.
Only lengths \(d=6,7\) can incur a masked error. At \(d=6\)
the source has size at most ten, so the three masked moments
cancel the discrepancy. At \(d=7\) the source has size nine:
the mask cancels on it and its physical primitive, and the
top pairing corrects the extra reverse primitive. The ideal
scalar pairings cancel by polynomial triangular integration.
Their degrees are at most 16. The scalar quadrature supplies
the exact remaining coefficients for all rooted trees.

Untapped reverse columns have the same full pure primal row
at a given clock. Their masses and taps are merged at that
clock. The pure physical origin and clock-one rows also
agree literally with existing forward rows, with zero-based
indices 0 and 16. The finite check tests these equalities
before folding and verifies all 3,927 owner-fold equations.
The distinct physical count is
\[
  22+14+17-2=51.
\]

## The next rooted conditions

The independent receipt evaluates eight actual size-18 rooted
coefficients in two formal-zero grafts. Let \(C\) multiply
by the stage clock and let \(A\) act by the full stage
matrix, so that on rooted weights these operations adjoin a
leaf at the root and extend the root. Define \(\mathcal V\)
by the four words `ACCACC`, `ACCAAC`, `ACCCCC`, and
`CCCCCC` on the one-vertex tree with coefficients
\(136080,-272160,204120,-34020\), respectively. Thus
\(w\coloneqq C^3\mathcal V\) is a formal-zero size-ten
combination. The actual raw outputs of \(C^7Aw\) and
\(C^6A^2w\) are
\[
 -179319239772371/735134400,qquad
 60424725514970393/189464184000.
\]
They give a paid unit blend, verified using the actual tree
factorials and weights. No inference about the next order is
made from the scalar quadrature alone.

The first two actual size-18 trees of \(C^7Aw\) already give
cleared defects
\[
 3832634919835806431/12350257920000,qquad
 10575038335276956031/12350257920000.
\]
Their integer blend with coefficients
\(-27896137847745847884819014400000\) and
\(10110196167059467558021662720000\) equals one. The next
bush is exact and is not used. The literal denominator
`177799875435900972564710400000000000000` divides
\((17!)^5\), and the weight denominator
`10170998716342464000` divides \((17!)^4\).
Thus no nonzero paid base change can kill every order-18
defect.

## Reproduction

From this directory, run:

~~~sh
python -B design17.py ..
python -B check17.py .. tableau-17-factorial-51.json receipt-17-factorial-51.json \
  ../order-17-factorial-52/receipt-17-factorial-52.json
out=$(mktemp -d)
python -B build17.py .. "$out"
cmp tableau-17-factorial-51.json "$out/tableau-17-factorial-51.json"
cmp receipt-17-factorial-51.json "$out/receipt-17-factorial-51.json"
~~~

The independent checker uses exact rational arithmetic and does not import the design or builder. The [52-stage construction](../order-17-factorial-52/README.md) remains available. This is not a Lean certificate.
