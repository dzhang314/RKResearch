# A five-row opening with a nonphysical cubic model kernel

This is a literal opening ingredient for a possible 15-stage ERK10
method, not a full upper bound. Unlike interpolation at three
physically pure donor clocks, the cubic model kernel can be nonsplit
over \(\mathbb Q\). The exact input test for a ten-high continuation
is one forward integration identity plus a short weighted reverse
word budget.

## The literal family and its true rank ledger

Work over a field in which \(10!\ne0\). Choose \(e,s,p,q\ne0\),
with \(s,p,q\) pairwise distinct. Take
\[
 P(X)=X^3+uX^2+vX,\qquad P(s)\ne0,\qquad
 p(3s^2+2su+2v)=sv.
\]
The regular moving-parameter version solves for \(p\) by
a nonzero coefficient on the left. Put
\(\alpha=p^2(3s-2p)/s^3=P(p)/P(s)\), and
\(\beta=P(q)/P(s)\). The five clocks are \(0,e,s,p,q\).
The \(e\) row reads only the origin; the \(s\) row pays its
first moment with \(e\)-tap \(s^2/(2e)\).
The \(p,q\) rows put \(\alpha,\beta\) times this tap onto
\(e\). In each row the origin tap fills its own clock sum.
The \(p\) row has only one additional tap, on \(s\), fixed
by \((A\boldsymbol c)_p=p^2/2\).
The \(q\) row has two additional taps on \(s,p\), determined
by its first moment and the modified second moment
\[
 (A\boldsymbol c^{\odot2})_q-q^3/3
                    =(e^2-2es/3)A_{q,e}.
\]
The same modified second moment holds at \(s,p\) by direct
substitution. No stage purity at \(p,q\) is required.

Normalize the true stage derivative of each tree so its model
is \(\boldsymbol c^{\odot(|t|-1)}\). Set
\(\boldsymbol d=A\boldsymbol c-\boldsymbol c^{\odot2}/2\).
It is supported at \(e\), with value \(-e^2/2\).
The supported later entries of \(A\boldsymbol d\) are
proportional to \(\boldsymbol V=(1,\alpha,\beta)\) on
the three clocks \(s,p,q\). Through tree size four the
model deviations are exactly the span of
\(\boldsymbol d,A\boldsymbol d\):
the only new operations are a clock mark of
\(\boldsymbol d\), a unary transport of it, and the
actual quadratic-primitive error, whose later entries are
a multiple of \(\boldsymbol V\). The two vectors are
independent by their \(e,s\) pivots.

On the resulting quotient of actual opening coordinates use
\(E_0,E_p-\alpha E_s,E_q-\beta E_s\). On monomials
\(1,X,X^2\) their determinant is
\[
         \frac{spq (p-s)(q-s)(q-p)}{P(s)}\ne0 .
\]
This is the three-node Vandermonde determinant using columns
\(X,X^2,P\), then subtracting multiples of the \(s\) row.
The model kernel through degree three is consequently
exactly the line spanned by \(P\). Define \(\Pi\) as the
unique quadratic (degree at most two) decoder from those
three linear readouts. It sends every true old profile
through size four to its model reduced modulo \(P\).
The actual numerical opening rank through size four is five;
the rank with formal model coordinates adjoined is six.

At size five there are already four independent pure directions.
In addition to the \(e\) pivot, the vectors on \(s,p,q\)
to try are \(\boldsymbol V,C_0\boldsymbol V,A\boldsymbol V\),
where \(C_0=\operatorname{diag}(s,p,q)\) and \(A\) here reads
the zero extension of \(\boldsymbol V\) on the five opening
rows. These are supplied by actual \(A\boldsymbol d\),
\(C A\boldsymbol d\), and \(A^2\boldsymbol d\) (all sizes
at most five). Their determinant, up to the common scalar
in \(A\boldsymbol d\), is
\[
 \frac{2p^3q(p-q)(p-s)(q-s)\big[(2p-s)v-3qs^2\big]}
        {3s^6(ps-v)}.
\]
Here \(ps-v\ne0\) follows from
\(P(s)=-s^2(ps-v)/(2p)\).
On the possible zero branch \((2p-s)v=3qs^2\), the
alternate third vector is the actual cubic primitive
defect \(A\boldsymbol c^{\odot3}-\boldsymbol c^{\odot4}/4\).
After subtracting a multiple of \(\boldsymbol V\), its
entries are
\[
            -x^4/4+(s+p)x^3/3-spx^2/2
            \quad (x=s,p,q).
\]
The [exact alternate pivot](symbolic-audit.txt) is nonzero
unless \(p=3s/2\), since all other factors are guarded
clock differences, \(ps-v\), \(2p-s\) (nonzero on this
branch), and nonzero clocks. If \(P/X\) is nonsplit there
is no such exception, as \(p=3s/2\) implies \(P(p)=0\).
Even when \(P\) splits, that branch has
\(\alpha=\beta=0\), \(s=2p/3\). The \(p,q\) restriction
of the last two pure directions has the old canonical
nonzero donor minor \(3pq^2(p-q)^2/16\), apart from the
known common factor in \(A^2\boldsymbol d\).
Thus the four pure directions always span the nonorigin
opening coordinates in the stated regular chart.
The numerical rank stays five and the joint rank is nine.

## Exact physical high gate

Let \(B\) be the strict high-to-high block, \(E\) evaluate
at the high clocks, and \(J\) be integration from zero.
Use the literal high-to-old block \((EJ-BE)\Pi\).
Every high true stage profile through size four is then
pure by causal induction, since the old decoder is exact
on models of degree at most two. At size five all other
needed model primitives still agree except for the possible
cubic discrepancy, always a multiple of \(P\). Thus
**purity through derivative size five holds exactly when**
\[
                            BEP=EJP.
\]
Necessity is given by a unary root above the size-four bush,
whose child model is \(X^3\) and whose decoded difference
is \(-P\). This is a literal equality of high vectors.

If the first actual nonzero high clock is \(h\) and no earlier
nonzero high clock is available, then \(JP(h)=0\).
One can choose
\(v=-h^2/2-2uh/3\) and hence freely move the kernel with \(u\).
For instance \(u=0\) gives nonsplit \(P=X(X^2-h^2/2)\)
over \(\mathbb Q\). At the next distinct high clock \(z\)
the required total tap onto clock \(h\) is \(JP(z)/P(h)\)
when \(P(h)\ne0\); it is generally nonzero. If all high
weights are nonzero, the weighted reverse formulation is
\(\sum_{i>j} w_i P(x_i)L_{ij}=w_j JP(x_j)\), with indices
in reverse causal order. This is linear in the weighted
tap entries at fixed kernel and high mesh.

## Necessary and sufficient short reverse budget

Assume the physical gate above, and only the opening origin
carries old output mass. The true scalar quadrature (origin
plus all high rows) must have precision nine. Every model
in \(U=X\mathcal P_3\) is a true combination through size
five with zero old profile: start with bushes and subtract
its four nonorigin entries using the independent pure columns
above. Its high profile is \(E f\). Clock marks preserve
this zero opening profile, so with \(5-m\) extra marks
one obtains every polynomial in \(X\mathcal P_{8-m}\)
as a source for a word with length \(m\le5\).

An outer word \(W\) is a product of high \(B\) (unary
primitive) and high clock diagonal \(C\) (same-root leaf
mark). Write \(W_s\) for its nominal polynomial operator
with \(B\) replaced by \(J\), \(C\) by multiplication by
\(X\). The required reverse tests, equivalently via the
weighted transpose, are
\[
          \sum_i w_i (W E f)_i=\int_0^1 W_s f(X)\,dX
          \quad (|W|=m,\quad f=X,\ldots,X^{9-m},
                       \quad 0\le m\le5).
\]
Necessity follows from the actual early-null combinations
and at most ten tree vertices. The apparent extra
length-six test on \(P\) from a size-four early-null source
is redundant: remove the rightmost letter (a clock mark
or \(B\)); on \(P\) its result is the nominal degree-four
profile because of the exact forward gate.

For sufficiency let \(f_s=\Pi\boldsymbol\Phi_s^{old}-X^{|s|-1}\)
for each normalized true source tree \(s\).
For \(|s|\le3\) it vanishes, and for \(|s|=4\) it is
a multiple of \(P\), already paid by the literal gate.
Through order ten there is at most one child of size
five or more at any node. Expand the high discrepancy
along that child's unique path. Each resulting term is
a scalar multiple of \(W(EJ-BE)f_s\) for some \(|s|\ge5\),
with \(|W|\le 9-|s|\).
The two nominal output integrals of this difference agree.
The test on \(Jf_s\) uses word length \(|W|\), and that
on \(f_s\) uses \(|W|+1\); both have total scalar degree
at most nine and zero constant source. Thus all such
outputs are zero, leaving only exact scalar quadrature
through tree size ten. The opening origin contributes
no larger-tree defect. No separate assumed stage order
or higher reverse co-order is being substituted for
the actual rooted equations.

## Paid literal copy and replay

The [literal seed](seed.json) has
\(e=1/8,s=1/3,p=1/4,q=1/2\),
\(P=X^3-X/2\), and decoder
\[
 \Pi=\begin{pmatrix}
 1&0&0&0&0\\
 -21&0&-135&128&28\\
 26&0&162&-160&-28
 \end{pmatrix}
\]
in ascending polynomial coordinates.
The common opening row denominator is \(4032=2^6 3^2 7\);
the literal quotient determinant is \(1/896\).
For the four pure columns the exact determinant is
\(-1/541165879296=-1/(2^{33}3^2 7)\).
All these ratios, and the native integer-scaled minor, are
units after paying \(10!\). Thus the literal decoder and
early-null rank arguments specialize to every nonzero
commutative \(10!\)-unit ring, independently of whether
\(P\) remains nonsplit there.

The replay also adds two **actual** paid high rows at
\(1,2/3\). The second taps the first by \(-10/81\);
each has all 17 pure rooted profiles through size five.
At the first high row the normalized size-six value of
the unary root above the size-five bush is \(5/6\), not 1.
This shows exactly the local grade achieved, with no
ordinary order-ten or remaining-row claim.

    python3 -B replay.py
    python3 -B symbolic.py
    sha256sum -c sha256.txt

The first script enumerates and evaluates the actual rooted
trees independently of the symbolic argument and checks the
literal input byte for byte. The second uses exact SymPy.
The native Core file ERK10FiveOpeningNonsplitKernelSeed.lean
checks the integer-scaled seed arithmetic on all four
tested Lean releases. The generic rank and order-payments
bridge above is mathematical, not a native HasOrder theorem.
