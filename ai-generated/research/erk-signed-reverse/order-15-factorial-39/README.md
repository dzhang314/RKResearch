# An exact 39-stage explicit method of order 15

This tableau has exact order 15 over \(U\coloneqq\mathbb Z[1/15!]\)
and after every base change to a nonzero commutative ring. The
earlier 40-stage tableau is unchanged. The saving is a reverse
donor row. Four ordinary scalar receivers supply its one missing
read using their existing physical stages. This is an upper
bound, not a claim of minimality or a Lean certificate.

## Two tiers of weighted reverse receivers

Write \(v\coloneqq2y-1=1-2x\), where \(x\) is the physical clock
and \(y\) the reverse clock. On polynomials in \(v\), define
\[
  (\mathcal I f)(v)\coloneqq\tfrac12\int_{-1}^v f(z)\,dz,
  \qquad
  \mu(f)\coloneqq\tfrac12\int_{-1}^1 f(z)\,dz.
\]
The letter \(C\) multiplies by the physical clock \(x\); the
letter \(L\) acts by the reverse matrix. Their model operations
are multiplication by \((1-v)/2\) and application of
\(\mathcal I\). The length of a reverse word is its number of
letters, and its model is the polynomial obtained by applying
these model operations to the constant one.

Suppose a reverse chart through tree size \(g\) lacks only one
of its exact polynomial reads after an actual last donor is
omitted. Let its remaining paid decoder \(D_0\) take values
in polynomials of degree at most \(g-2\), and let the missing
polynomial be monic \(Q\) of degree \(g-1\). Through word
length \(g-1\), the old reads determine the model polynomial
modulo \(Q\), which is enough to give the exact model through
length \(g-2\).

At an early scalar receiver of clock \(a\), use the incoming
row \(\mathcal I_a D_0\) on the old donor data. It gives the
exact value of every word through length \(g-1\), since an
outer \(L\) uses an old word of shorter length. For such words
the differences between these exact samples and \(D_0\) are
their missing coefficients times \(Q(a)\). If the weighted
numbers \(\lambda_a Q(a)\) on the early sites generate the
unit ideal, there is a paid linear read \(\eta\) of the old
and early data extracting that coefficient. Each tap of
\(\eta\) on an early receiver is explicitly a multiple of
its mass \(\lambda_a\). The decoder
\[
 D\coloneqq D_0+Q\eta
\]
now gives the full model through length \(g-1\).

Put \(K\coloneqq\mathcal I Q\). Let later live receivers
have incoming rows \(\mathcal I_a D+\gamma_a\eta\),
using the early layer before them. Let all other ordinary
scalar receivers use \(\mathcal I_a D\). At length \(g\),
the discrepancy of an early receiver from the exact
model is \(-K(a)\kappa\), and that of a later live receiver
is \(\gamma_a\kappa\). Here \(\kappa\) is \(\eta\) applied
to the shorter word when the last applied letter is \(L\);
it is zero when that letter is \(C\). Write
\[
 \delta_a\coloneqq
 \begin{cases}
  -K(a),&a\text{ is early},\\
  \gamma_a,&a\text{ is later live}.
 \end{cases}
\]
For a length-\(g\) word with model \(p_W\), the old and early
data give an as yet incomplete polynomial \(D W\). Set
\(\sigma_W\coloneqq p_W-DW\). The weighted live differences
from \(DW\) are exactly
\(\lambda_a(\sigma_W(a)+\delta_a\kappa)\). Thus the early
sites still supply high readings. Only one extra unknown
\(\kappa\) is needed, even when there are several early sites.
A paid left inverse for this augmented matrix recovers
\(\sigma_W\) without any mass division. On all shorter
words this recovery reads zero.

## The two left tests

Use a set \(S\) of pure sites, where late signed pairs require
no additional physical stage. Let \(X_0\) be a polynomial
space containing the reflected first-excess forward residuals.
Let \(X_1\) contain those residuals, the one-degree-later
forward residuals, and the physical primitives of the
first-excess residuals. Choose paid numbers \(j_a\), for
\(a\in S\), with
\[
 \sum_{a\in S}j_a f(a)
  =-\sum_{b\,\mathrm{live}}\lambda_b\delta_b f(b)
 \qquad(f\in X_1).
\]
It suffices that the right-hand side vanish on the kernel of
evaluation on \(S\) in \(X_1\), and that evaluation admit a
paid right inverse onto its image. This is a test of the
masked moments, not a requirement to reconstruct every
polynomial of \(X_1\). Separately choose paid cardinal
polynomials \(e_a\) that recover the needed forward pairing
on \(X_0\).

At each \(a\in S\), use a late positive row with incoming
row \(\mathcal I_a D\) plus the functionals
\[
  j_a\eta
  \quad\text{and}\quad
  \sigma\longmapsto\mu(e_a\mathcal I\sigma).
\]
The latter uses the augmented recovery. A late negative row
at the same clock keeps just the baseline \(\mathcal I_a D\).
Their masses are \(+1,-1\). The ordinary live discrepancies
at length \(g\) now cancel against \(j_a\eta\) in every
pairing with a polynomial of \(X_1\). For the extra
application of \(L\) to a length-\(g\) word the deficit
has two terms, the same live mask times \(\eta(W)\) and
\(-\mathcal I\sigma_W\) across the scalar receivers.
The compensation equation cancels the first term. The other
late functional cancels the second against every
\(f\in X_0\), since the cardinal interpolation recovers
\(f\) from \(S\).

To see which order conditions use these tests, let \(m\) be the
forward chart's exact tree size, and take
\(p=m+g+2\leq2m+2\). The forward derivative model for tree
\(t\) is \(g_t(x)\coloneqq |t|x^{|t|-1}/t!\).
Through order \(p\) there is at most one erroneous primitive
at a root, because its source child has size at least \(m+1\).
Moving each outer propagation to the reverse side of the
weighted pairing yields a reverse word of length \(d\) with
\(d\leq p-1-|t|\) for source child \(t\). An adjoint
pairing contains that word tested against the physical
primitive of the source, and one extra \(L\) on that word
tested against the source. Only \(d=g-1,g\) can use the
first correction. For \(d=g-1\), the source is at most
size \(m+2\). For \(d=g\), the source is of size \(m+1\),
and its reflected polynomial lies in \(X_0\); its physical
primitive lies in \(X_1\). All shorter reverse pairings are
ordinary scalar polynomial integrals. The two ideal integrals
agree by triangular integration and their degrees are at most
\(p-1\). Hence this argument proves the conditions of every
rooted tree, not only the reverse words.

The old positive donors and their literal negative copies
cancel in the weighted reverse pairings. Every nonzero tap
on a live receiver has its mass factored from the coefficient,
so the normalized transpose is the same paid transpose as
in the single-tier construction. The pure receiver's primal
incoming row depends only on its physical clock and the forward
chart. The signed late pairs therefore fold into existing
pure scalar rows. The augmented rule does not create a
backward tap into either live tier.

## Order 15 and the physical rows

Keep the 15-row grade-seven forward chart of the 40-stage
construction. On the reverse side keep the first ten rows of
its eleven-row reverse chart. The last remaining new read is
at \(v=1/3\); the omitted read was at \(v=1/2\).
The five retained scalar functions are the two endpoints,
the exact mean through size six, the midpoint and the genuine
point read at \(1/3\). On degree-at-most-four polynomials their
matrix in the physical reverse clock has determinant
\(-1/12960\). On degree-at-most-five polynomials their gap is
\[
 Q(v)\coloneqq v(v^2-1)(v^2-1/9),
 \qquad
 K(v)=\frac{(1-v^2)^2(1+3v^2)}{36}.
\]
The old endpoints remain exact through size seven. Therefore
the missing length-six polynomial \(\sigma_W\) has both
endpoint factors and lies in \((1-v^2)\mathcal P_4\), with
\(\mathcal P_d\) the polynomials of degree at most \(d\).

Use the same 15 scalar sites: zero and both signs of
\(1/12,1/6,1/4,1/3,1/2,2/3,1\), with their cardinal masses.
They integrate through degree 14, and also degree 15 by
symmetry. Use the following roles:
\[
 \begin{aligned}
 S&\coloneqq\{-1,0,\pm1/3,\pm1/4\},\\
 E&\coloneqq\{-2/3,-1/2,-1/6,-1/12\},\\
 B&\coloneqq\{1/12,1/6,1/2,2/3\}.
 \end{aligned}
\]
The remaining site \(v=1\) is pure and is not used for a
late correction. The actual old donor clocks are pure.
The set \(E\) is the early tier and \(B\) the later live tier.
The paid correction values in the displayed order of \(B\) are
\[
 \begin{aligned}
 \gamma_{1/12}&\coloneqq1861466503234151225967864868997375/253034496,\\
 \gamma_{1/6}&\coloneqq4366027551468749673012329114405/279936,\\
 \gamma_{1/2}&\coloneqq15273860333554473556291840344989/419904,\\
 \gamma_{2/3}&\coloneqq0.
 \end{aligned}
\]
These coefficients solve a two-moment equation with weighted
columns at the four sites of \(B\).

For that equation put
\[
  F_S(v)\coloneqq(1-v)\prod_{a\in S}(v-a).
\]
The forward origin is exact for every tree, so the two higher
source sizes and the required primitives all lie in
\(X_1\coloneqq(1-v)\mathcal P_7\). Evaluation on \(S\)
has kernel spanned by \(F_S,vF_S\) in this space. The two
verified equations are
\[
   \sum_{a\in E\cup B}\lambda_a\delta_a F_S(a)a^j=0,
   \qquad j=0,1.
\]
Consequently the paid interpolation of the masked functional
produces the six coefficients \(j_a\). For the top pairing
the actual reflected size-eight sources are in
\((1-v)\mathcal P_6\) and have zero reflected high-seven read.
That read on \(F_S\) is \(4/3\), a paid unit, so the
pin-zero cardinal fit on \(S\) recovers these sources exactly.

The receipt contains maximal-minor certificates for the
four-by-one promotion and the eight-by-six augmented recovery
on \((1-v^2)\mathcal P_4\) and the mask column. The latter
rank is over \(U\), not just over the rationals. An early tier made of whole reflected pairs needs at least
two pairs to pass the first paid test, since each pair
mass is a nonunit. It leaves at most two later pairs.
Modulo a prime killing one later mass pair, only three
pairs survive; the constant masked moment forces the
remaining later mask, if any, to be even. Every even mask
on the three surviving pairs is already represented by
\((1-v^2)\operatorname{span}(1,v^2,v^4)\). Splitting opposite
signs between tiers avoids that forced dependence.

The virtual chronological rows are ten old donors, four early
and then four later live scalar receivers, ten negative old
copies, seven ordinary pure scalar receivers, and twelve
late signed correction rows. All rows without an outgoing
reverse tap are pure in the primal tableau. Their literal
same-clock rows fold, including the physical origin into
the existing first forward stage. The 39 distinct rows are
\[
  15+10+15-1=39.
\]

## The actual next-order defect

Write \(C\) for multiplication by the physical clock and
\(A\) for the actual stage matrix. Acting on the leaf, these
add a root leaf and extend the root, respectively. Define the
formal-zero size-nine expression by
\[
 w\coloneqq C A C^3 A(C^2-2AC)\boldsymbol\Phi_\bullet(A).
\]
Its suffix values are zero, since its core of size eight is
already locally exact there. Its reflected forward residual
has high-seven read \(7/1200\). The top projector minus the
identity on that residual is therefore \(-7F_S/1600\).

The highest reverse pairings against the model differences
of \(C^6\) and \(L^6\) give
\(931/40030848000\) and \(-64411/1601233920000\).
They are the raw outputs of the actual formal size-16
expressions \(C^6Aw\) and \(A^7w\). Later sources of these
formal-zero expressions have degree at most six. They still
fall within the compensated and scalar degree budgets, so
do not contribute any extra term. The independent checker
evaluates all four individual rooted outputs of these two
grafts directly. Their exact integer combination
\((21571823370240000,12472011002880000)\) gives one.

Independently, the two individual trees of the first graft
have cleared defects
\[
  -9505446555931/435891456000,
  \qquad
  -9505477211899/435891456000.
\]
Their integer combination with coefficients
\((-1782603464985484517376000,1782597715938533894400000)\)
is one. The next bush is exact and is not used. The matrix
and output denominators are respectively
`14264352208141030195200000` and `945945000`, dividing
\((15!)^3\) and \((15!)^2\). Thus all stated conclusions
hold after every nonzero factorial-unit base change.

The finite receipt checks every normalized adjoint transition,
forward rooted attachment through size nine, and actual source
test at both affected word lengths. It also checks all 2,418
individual owner-fold equations and the unit witness directly.

## Reproduction

From this directory, run:

~~~sh
python -B check.py .. tableau-15-factorial-39.json receipt-15-factorial-39.json \
  ../order-15-certificate/receipt-15.json
out=$(mktemp -d)
python -B build.py .. "$out"
cmp tableau-15-factorial-39.json "$out/tableau-15-factorial-39.json"
cmp receipt-15-factorial-39.json "$out/receipt-15-factorial-39.json"
~~~

The exact structural checker uses only Python's standard library and does not import the builder. The [earlier 40-stage method](../order-15-certificate/README.md) is unchanged. This is not a Lean certificate.
