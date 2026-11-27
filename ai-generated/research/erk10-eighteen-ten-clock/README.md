# Universal exact order ten in eighteen explicit stages

The [literal tableau](tableau.json) has **exact order ten in 18
strictly explicit stages over \(\mathbb Z[1/210]\)**. It works over
every nontrivial commutative ring in which \(10!\) is a unit.
This improves the previous
[19-stage general-ring construction](../erk10-nineteen-compressed-reverse/README.md).
It is an upper bound, not an assertion of minimum width.

The common denominator is \(800150400=2^7 3^6 5^2 7^3\), which
divides \((10!)^3\). Let \(t\) be a root with a leaf child and
a nine-vertex bush child. The tree has size eleven and
factorial \(11\cdot9=99\). Its raw output is \(7069/699840\), so
its factorial-scaled residual from one is \(-1/77760\), a unit
in the same coefficient ring. No extra prime is required to
exclude order eleven.

## Different prefix and distinct ten-clock quadrature

Use the archived
[nine-row prefix and degree-four decoder](../../upper-bounds/real-algebraic/erk14-order9-seven-clock/prefix.json)
at scale \(1\), much shorter than the order-seven prefix of
the 19-stage chart. These rows come from a paid order-six seed,
its literal endpoint, and its literal half-port.
Let \(\Pi\) be the decoder and
\(\rho_t(X)=|t|X^{|t|-1}/t!-\Pi\boldsymbol\Phi_t(A_{\rm old})\).
The constructor checks the actual prefix tree values:
- \(\rho_t=0\) through size five;
- \(\rho_t(0)=0\) at sizes six, seven and eight, with
  \(\rho_t(1)=0\) also at sizes six and seven;
- for size six, \(\rho_t\) lies in
  \(d(X)\langle1,X(X-1)\rangle\), where
  \(d(X)=X(X-1)(X-1/2)\). These are odd about \(1/2\), so
  the primitive \(J\rho_t\) vanishes at both endpoints.

Use all ten distinct sites \(j/6\) for \(-3\le j\le6\).
Interpolate their weights by integration on \([0,1]\).
They lie in the factorial localization and give precision nine.
The weight at \(1\) is the unit \(7/150\). The old origin takes
the zero-clock mass; the other nine sites have the reverse
chronology
\[
  (1,-1/2,-1/3,-1/6,1/3,1/2,5/6,1/6,2/3).
\]
No reverse labels repeat and no physical merges are used.

As in the [20-stage precursor](../erk10-twenty-compressed-reverse/README.md),
use the raw weighted reverse matrix \(K\), which is the transpose
of the forward high block after reversing both indices. Write
\(\boldsymbol x,\boldsymbol w\) for the reverse clocks and masses
and \(\boldsymbol y=\boldsymbol1-\boldsymbol x\).
On the eight interior (nonzero and non-one) sites, choose
\(\boldsymbol U\) as the Lagrange leading cofactor divided by
the corresponding \(x_i\), with common scale normalized
by the first interior row. At the reverse clock one set \(U_i=0\).
This kills every power \(X,\ldots,X^7\). Define
\(\boldsymbol Z=\boldsymbol U/\boldsymbol y\) entrywise
on those eight sites and zero at \(1\). Unlike the
interior-mass compression in the 19-stage chart, this division
is by scalar clock differences, all paid.

Use the basic actions
\[
 \begin{split}
 K\boldsymbol w&=\boldsymbol w\odot\boldsymbol y,\\
 K(\boldsymbol w\odot\boldsymbol y)&=
        \boldsymbol w\odot\boldsymbol y^{\odot2}/2+\boldsymbol U,\\
 K(\boldsymbol w\odot\boldsymbol y^{\odot2})&=
        \boldsymbol w\odot\boldsymbol y^{\odot3}/3+\boldsymbol G,\\
 K\boldsymbol U&=\boldsymbol H .
 \end{split}
\]
The first three actual interior rows determine
\[
 \boldsymbol G=-\tfrac{281}{243}\boldsymbol U
        +\tfrac{256}{243}\boldsymbol y\odot\boldsymbol U
        +\tfrac{70}{81}\boldsymbol Z,\qquad
 \boldsymbol H=\tfrac{55}{54}\boldsymbol U
        -\tfrac13\boldsymbol y\odot\boldsymbol U
        -\tfrac79\boldsymbol Z.
\]
At the last two reverse sites impose the terminal moments:
\[
 \boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
               -\boldsymbol w\odot\boldsymbol y^{\odot4}/4,\qquad
 \boldsymbol l=K(\boldsymbol y\odot\boldsymbol U),\qquad
 \boldsymbol r=K\boldsymbol Z
\]
all annihilate the two actual size-six source tests.
The relevant four-donor, seven-donor, and terminal-moment
determinants are respectively
\(-3/22400000000,\ -59049/17210368000000000000,\ 5/34992\).
These are units. The forward cross block is
\((EJ-BE)\Pi\), where \(Jf(X)=\int_0^X f\) and \(E\) evaluates
at the high clocks.

The same weighted integration-by-parts identity as in the
precursor handles words of lengths zero through three.
The single-source recurrence starts with size six, so two
first-source errors cannot occur in one tree through order ten.
The length-one tests use the seven power moments of
\(\boldsymbol U\), including for size eight when the right
endpoint can be nonzero. At length two, \(\rho_t\) vanishes
at both endpoints and has degree at most six, so
\(\boldsymbol G,\boldsymbol H\) annihilate it: the term
\(\boldsymbol Z\) cancels its factor \(1-X\) and uses a
lower power test of \(\boldsymbol U\).
The paired primitive term is paid directly by
\(\boldsymbol U\), including the size-seven source.
At length three, the source is of size six, the primitive
source again vanishes at both endpoints, and the next actions of
\(\boldsymbol G,\boldsymbol H\) lie in the span of
\(\boldsymbol H,\boldsymbol l,\boldsymbol r\).
The only new tests are on \(\boldsymbol k,\boldsymbol l,\boldsymbol r\),
which were prescribed exactly. These supply the complete order
payment through ten.

## Exact independent checks

The regeneration checks the real prefix identities, every literal
matrix entry and all 1,205 rooted equations. The separate integer
replay reads only the literal coefficients to check the same tree
family, the factorization of the denominator, all 18 strict distinct
rows, and the unit size-eleven defect. No approximate computation
or generator assumption is used in either verification.

    python3 -B audit_tableau.py
    python3 -B build18new.py --emit /tmp/erk10-eighteen-rebuilt.json
    cmp tableau.json /tmp/erk10-eighteen-rebuilt.json
    sha256sum -c arithmetic-sha256.txt

The bundled prefix copy has the same SHA-256 as the referenced
repository file, checked before constructing the matrix.
