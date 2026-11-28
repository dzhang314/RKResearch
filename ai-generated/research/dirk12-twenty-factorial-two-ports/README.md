# A single factorial-localized twenty-stage DIRK12

This ordinary lower-triangular tableau has **twenty physical
stages and exact rooted order twelve over every nonzero
commutative ring inverting \(12!\)**. Its common literal
denominator is
\[
 D=830216051280000=2^7 3^6 5^4 7^6 11^2\mid(12!)^6 .
\]
The two named diagonals are \(0\) and \(1/16\). A completely
independent integer replay checks all **7,813** rooted shapes
through twelve and the two first-unpaid defects. The scaled
thirteenth bush is \(97351/161663040\); its numerator is
coprime to the reduced numerator of the scaled thirteenth tall.
Both defect denominators divide powers of \(D\). Integer Bézout
therefore gives genuine exactness, not just order at least twelve,
in every such nonzero ring.

This lowers the single factorial-unit upper from 21 to **20**.
It is not the earlier 20-stage rational-only witness, not a
gluing of the four nonlinear tableaux from the
[19-stage local and finite-characteristic portfolio](../dirk12-nineteen-field-local-portfolio/README.md),
and not a claim about the unrestricted rational or real minimum.
The rational upper from that separate work remains 19, and
the real minimum is fifteen. This packet's full proof is exact
arithmetic; a separate native Lean certificate would be needed.

## Literal opening and scalar weights

Use ten old stages with clocks
\[
  (0,1/8,1/4,1/2,3/20,3/4,5/12,1/12,5/6,1/6).
\]
Rows are the same donor pattern as the rational two-port
splice, with old normalized precursor ratio \(a=2/3\),
its second ratio \(1/5\), and first three size-six port
clocks in ratios \(1,5/9,1/9\). Every literal denominator
is paid, including those in the degree-five decoder on
indices \(0,5,6,7,8,9\). Those six coordinates are pure
through actual size six, and the last two are pure through
size seven (a symmetric five-node rule followed by the
full six-node primitive). The builder checks these
assertions against the actual old stage vectors. The
size-seven projected residual space has exact rank three;
all its members vanish at the two merge sites and at zero.

The scalar sites are \(\{j/6:-4\le j\le8\}\). Keep
the weight at clock one fixed at \(3/40\), and solve
the remaining twelve weights by the corresponding
degree-eleven Lagrange rule. The zero-site weight is
used on the old origin. All weights are nonzero and in
\(\mathbb Z[1/12!]\). The twelve scored suffix clocks
in reverse physical order are
\[
 \mathbf x=(1,-1/2,-1/3,-2/3,4/3,1/3,1/2,2/3,
             7/6,-1/6,1/6,5/6), \qquad \mathbf y=\mathbf1-\mathbf x.
\]
In particular the first four reverse weights, at the
first four displayed clocks, are
\(3/40,-343/145200,11/840,343/1742400\), all units in the
same localization. Divisions by arbitrary output weights
are not part of the construction.

## Raw reverse payment and one global linear fit

Write \(W_j=\mathbf w\odot\mathbf y^j\) in the reverse order,
where the origin is omitted. Use the **raw** lower triangular
reverse transpose \(K\), so the forward suffix matrix is the
ordinary transpose of \(K\) with both indices reversed.
With \(P\) the nodal polynomial of the eleven proper \(x\)
sites, construct a raw vector \(\mathbf G\), zero at \(x=1\),
elsewhere the value of one quadratic numerator divided by
\(x_i P'(x_i)\). Its three scalar coefficients make
\(G_i=w_i y_i^3/6\) at the first three nonzero reverse times
\(i=1,2,3\); the numerator is found by quadratic interpolation,
not a fitted root. It annihilates all positive powers of
\(\mathbf x\) through degree eight by the ordinary cofactor
identity. The first three nonzero rows are exactly reverse
trapezoids, with no divided nonunit weights.

The enforced raw actions are
\[
 \begin{split}
 K W_0&=W_1,\qquad K W_1=W_2/2,\\
 K W_2&=W_3/3+\mathbf G,\qquad
 K W_3=W_4/4+(3/2)\mathbf y\odot\mathbf G,\\
 K\mathbf G&=(1/2)\mathbf y\odot\mathbf G.
 \end{split}
\]
To see a paid causal solve of these equations from physical
row four onward, put \(\boldsymbol\Delta=\mathbf G-W_3/6\).
It is zero on the first four donor coordinates, and the
last two equations say \(K\boldsymbol\Delta=
\mathbf y\odot\boldsymbol\Delta/4\).
Set the row diagonal provisionally to \(y_i/4\); satisfy
the four remaining power reads by the four unit-weight
donors. The resulting residual degrees of freedom are
ordinary null directions of the scalar row
\(\Delta_4,\ldots,\Delta_i\). Integer extended-gcd column
operations give a basis after paid denominator clearing.
Lift each direction back through the same four unit donors
to preserve the four other actions. Thus the base and all
28 free directions have only paid denominators.

The two final pairings are those of \(K W_4-W_5/5\) and
\(K(\mathbf x\odot\mathbf G)\) against the actual
three-dimensional old size-seven residual space. They are
six affine linear equations of exact rank six in those
28 directions. The stored coefficient vector solves the
whole system with denominator dividing 117600. It was
obtained by combining distinct exact linear pivot solutions:
if \(M z_i=d_i b\), an integer Bézout combination of the
\(d_i\) produces *one* exact solution \(z/\gcd(d_i)\).
This works for these fixed linear equations because the
old bank, scalar mesh, and reverse profiles are held fixed.
It is not gluing or combining RK tableaux by a nonlinear
order argument. The builder checks the recorded small
system and its reconstructed literal matrix exactly.

## Full rooted order and the genuine two merges

The forward cross block is \((EJ-TE)\Pi\), where \(T\)
is the literal suffix in chronological order, \(E\)
evaluates at its sites, \(J\) is the scalar primitive, and
\(\Pi\) is the decoder. A projected old error is first
seen on size seven, injecting at derivative grade seven.
Since two such errors cannot multiply through grade eleven,
all rooted defects in the suffix are linear words in \(T\)
and clock multiplication on such primitive injections.
In the reversed pairing, each word \(W\) of length at most
four reads from \(W^*(K,\mathbf x)\mathbf w\) and its next
\(K\) action. The ideal scalar portions cancel by
integration by parts on the exact degree-eleven grid.
Actual errors first enter on \(\mathbf G\) at grade three,
then in the span of \(\mathbf G,\mathbf x\odot\mathbf G\)
at grade four. Their paid power moments are as above.
At grade five only the actual size-seven old residual
space is seen, and the two final pairings pay it. This is
the same linear error budget as the rational two-port
splice, now using raw rather than divided weights.

The first two forward suffix clocks \(5/6,1/6\) are the
last two old decoder ports. Old row 8 has the complete
degree-five integrated cardinal row with literally zero
future tap by symmetry; old row 9 has it by definition.
The two new rows differ from their respective old rows by
\[
 (1/24)(e_{10}-e_8),\qquad
 (5/24)(e_{11}-e_9)
\]
in zero-based raw indices. There is no cross-copy
coefficient. These are **actual** shifts between the two
copies' self-coordinate columns, not equality of scalar
clocks asserted to be equality of stages. Induct on a
rooted tree: the two copies agree for a leaf, and at each
attachment the literal row difference reads a constant
times equal components of the strictly smaller child.
The base factor also agrees by induction. Redirecting
all columns and adding the weights therefore preserves
the exact rooted outputs. Both shifts are checked on
the full raw rows before contraction. Width is
\(10+12-2=20\), and the final width-20 independent replay
does not rely on the contraction lemma.

## Reproduce

All code here uses Python's standard library:

    python3 -B build.py --emit /tmp/dirk12-twenty-factorial-rebuilt.json
    cmp tableau20.json /tmp/dirk12-twenty-factorial-rebuilt.json
    python3 -B verify.py
    python3 -B independent.py
    sha256sum -c sha256.txt

The replay never imports the construction or the flag data.
It uses the literal numerator matrices and independently
enumerates the canonical balanced-bracket rooted shapes.

The second independent replay uses nested rooted tuples, with child-size
partitions and multisets formed independently of the bracket catalog.
