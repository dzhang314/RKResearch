# General-ring order ten in twenty explicit stages

The [literal tableau](tableau.json) is a strictly explicit 20-stage
method of exact order ten over \(\mathbb Z[1/210]\), and over every
nontrivial commutative ring where \(10!\) is a unit. This is a
one-stage improvement over the [21-stage general-ring splice](../erk-ten-moment-splice/README.md).
It is not a minimum or an improvement to the unrestricted real bound.

The coefficient denominator is \(987614208000=2^{13}3^9 5^3 7^2\).
For the tree with three leaf children and a seven-vertex bush child
at its root, the order is eleven and the tree factorial is \(77\).
Its raw output is \(157/12096\), so its cleared condition minus
one is \(-1/1728\), a unit. This is a single exactness receipt;
it remains nonzero under every stated unital base change, even
in characteristic \(11\).

## A shorter prefix and a compressed weighted transpose

Keep the ten-stage paid order-seven seed of the previous splice and
its actual endpoint, for eleven opening rows. Delete the two old
primitive-read rows. Use the degree-four decoder \(\Pi\) defined by
the five literal functions \(E_0,E_1,I_1,I_1^x,I_1^{x^2}\) on
polynomials; the integrals are realized by the seed weights
times the appropriate clock powers. Write
\[
  \rho_t(X)=\frac{|t|X^{|t|-1}}{t!}
                      -\Pi\boldsymbol\Phi_t(A_{\mathrm{old}}).
\]
It is zero for \(|t|\le5\). For \(|t|=6,7,8\) it is an
endpoint-vanishing polynomial of degree at most \(|t|-1\).
At sizes six and seven its integral is zero, and at size six
its first moment is also zero. These facts are the order-seven
seed conditions, including attachment of up to two leaves,
and the endpoint's elementary stage values through size eight.

Keep the same nine-site symmetric quadrature of precision nine.
Assign its clock-zero weight to the old origin. Use reverse
chronology
\[
   (1,1/3,2/3,3/2,1/4,3/4,1/2,1/2,-1/2,1).
\]
The clock-one mass splits into \(1\) and its remainder. The
clock-half mass splits into \(23\) and its remainder. Work directly
with the **weighted** reverse matrix \(K\), the literal transpose
of the chronological forward high block after reversing both labels.
No nonunit individual mass is inverted. Write \(\boldsymbol x\)
for these ten labels, \(\boldsymbol y=\boldsymbol 1-\boldsymbol x\),
\(\boldsymbol w\) for their weights, and \(\boldsymbol v\) for the
same vector with both endpoint-one entries zero.
Assign the density \(\boldsymbol U\) by the seven-site cofactor
rule: its group aggregate multiplied by \(X(1-X)\) is proportional
to the node's Lagrange leading coefficient. Normalize by the first
interior row, which reads the reverse clock-one row alone.
Split the half-site aggregate so that its early value is \(-7\).
Thus \(\boldsymbol U\) kills \(X(1-X)\) times polynomials through
degree five.

Make the actual four basic row equations
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
The new compression is
\[
 \boldsymbol G=\tfrac{37}{60}\boldsymbol U
 -\tfrac13\boldsymbol y\odot\boldsymbol U-\tfrac1{90}\boldsymbol v,\qquad
 \boldsymbol H=-\tfrac3{40}\boldsymbol U
 +\tfrac34\boldsymbol y\odot\boldsymbol U+\tfrac{17}{180}\boldsymbol v .
\]
These coefficients are fixed by the first three actual interior
rows, not an approximate fit. The three interpolation determinants
used for coefficients, four-input rows and seven-input rows are
\(81/35000000,\ 243/350000000,\ 16/452197265625\),
all units.

For \(|t|=6\), write \(z=2X-1\) and \(d(X)=X(1-X)\). The whole
possible source space is spanned by
\(d(X)(5z^2-1)\) and \(d(X)z(7z^2-3)\).
On the last two interior rows, choose three further responses
so that
\[
 \boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
                -\boldsymbol w\odot\boldsymbol y^{\odot4}/4,\qquad
 \boldsymbol l=K(\boldsymbol y\odot\boldsymbol U),\qquad
 \boldsymbol r=K\boldsymbol e_{\rm first}
\]
annihilate these two tests. Here the first reverse weight is \(1\).
The determinant of that terminal moment solve is \(75/8\),
up to ordering of the two rows, also a unit.

The forward high block \(B\) is obtained from \(K\) as stated;
use \((EJ-BE)\Pi\) as its cross block, with
\(Jf(X)=\int_0^X f\) and \(E\) evaluation at the high clocks.
All corrections through order ten come from one source and
words of length at most \(9-|t|\) in high primitives and clock
multiplication: two size-six source trees cannot enter two
different branches through order ten. Polynomial integration by
parts transfers those words to \(K\) and \(J^*f=\int_X^1 f\).
For length one, the relevant density is \(\boldsymbol U\).
For length two, \(\boldsymbol G,\boldsymbol H\) kill every
required source: the \(\boldsymbol y\odot\boldsymbol U\) term
is a lower-degree cofactor payment, and the \(\boldsymbol v\)
term is an integral-zero payment. For length three, the exact
reversed-word defect lies in the span of
\(\boldsymbol y\odot\boldsymbol U,\boldsymbol G,\boldsymbol H\).
Their primitive-source payments vanish by the displayed moments.
In the next reverse action, use
\(K\boldsymbol v=\boldsymbol w\odot\boldsymbol y-\boldsymbol r\).
The first term integrates to zero on every size-six source,
and all remaining terms are paid by \(\boldsymbol k,\boldsymbol l,\boldsymbol r\).
Precision nine is enough for every integration-by-parts identity.

The last reverse clock-one row is zero and never a donor. Its
forward row is precisely \(I_1\Pi\), the literal old endpoint,
and its weight is redirected there. Thus the full explicit
tableau has \(11+10-1=20\) physical rows.

## Exact independent replay

The constructor regenerates the tableau from these small paid
systems. Separately, the integer verifier reads only A and b from
the fixture for the rooted calculation. It checks every one of
the 1,205 rooted conditions through order ten and the single
selected unit eleventh defect, and confirms 20 distinct strict
rows. No floating-point decision enters either replay.

    python3 -B audit_tableau.py
    python3 -B build20.py /tmp/erk10-twenty-rebuilt.json
    cmp tableau.json /tmp/erk10-twenty-rebuilt.json
    sha256sum -c arithmetic-sha256.txt
