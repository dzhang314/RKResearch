# One universal fifteen-stage explicit method of exact order nine

The [literal tableau](tableau.json) is strictly explicit and has exact
order nine in **15 stages over \(\mathbb Z[1/210]\)**, hence over every
nontrivial commutative ring in which \(9!\) is a unit. It improves the
previous [16-stage universal upper bound](../erk-nine-moment-splice/README.md).
No field, positivity, locality, finite characteristic, or choice between
different tableaux is needed.

The common coefficient denominator is
\(2116800=2^6 3^3 5^2 7^2\), which divides \((9!)^2\).
The tenth bush has cleared rooted-condition residual \(-7/23328\),
a unit over the same ring, so order ten fails after every nonzero
unital base change. This is an upper bound, not a claim of a minimum.

## Construction: six opening stages and ten scalar sites

Use opening clocks \(0,1/12,1/9,p,q,r\) with
\((p,q,r)=(1/6,1/2,5/6)\). The opening rows at \(0,p,q,r\)
have the exact scalar tree values through size four. The decoder
\(\Pi\) interpolates their literal derivative values by a cubic.
For a tree \(t\), let \(g_t(X)=|t|X^{|t|-1}/t!\) and
\(\rho_t=g_t-\Pi\boldsymbol\Phi_t(A_{\mathrm{old}})\).
It is zero through size four; at sizes \(5,6,7\) it has degree at
most \(|t|-1\) and vanishes at zero. At size five it satisfies one
more linear constraint: for
\(\rho_5=\sum_{j=1}^4 v_j X^j\), the coefficient vector
\(\boldsymbol v\) is killed by the row
\[
 \boldsymbol\lambda^\top
 =(-115/5184,-25/5184,-25/20736,-25/93312).
\]
This row comes from the cross product of the two opening error
vectors. Equivalently these facts can be checked directly on the nine
order-five tree profiles.

Use the ten equally spaced scalar clocks \(j/6\), \(0\le j\le9\).
Fix the mass at \(1\) to be \(-1/840\) and interpolate on the
other nine sites; the resulting rational masses pay all monomials
through degree eight and lie in \(\mathbb Z[1/210]\). Assign the
origin to the old origin and the other nine clocks to new physical
rows. Their **reverse** chronology is
\[
 (1,3/2,1/3,4/3,5/6,7/6,1/6,1/2,2/3).
\]
Unlike the earlier splices, no reverse clock repeats, no new row
must contract into a prior pure port, and no nonunit mass is divided
out. There are six opening and nine high physical rows.

Write \(\boldsymbol x,\boldsymbol w\) for these nine clocks and
masses and \(\boldsymbol y=\boldsymbol1-\boldsymbol x\).
Work directly with the weighted reverse matrix \(K\), which is
the transpose of the forward high block \(B\) after both indices
are reversed. Choose a density \(\boldsymbol U\) annihilating
\(X,\ldots,X^6\). It uses the nine-site cofactor array times a
quadratic in \(X\), divided pointwise by \(X\). The three
interpolation values are the forced zero at \(1\) and the values
at \(3/2,1/3\) for the first two interior reverse rows.
The latter are \(w_{3/2}(-1/8)=-1/33600\) and
\(w_{1/3}(4/3)=-3/350\). The exact fourth-row relation allows
the two next densities to be compressed to
\[
 \boldsymbol G=(-17/36-5\boldsymbol y/18)\odot\boldsymbol U,
 \qquad
 \boldsymbol H=(1/8+\boldsymbol y/4)\odot\boldsymbol U .
\]
Here scalar terms in an entrywise expression act on every entry.
The actual row equations are
\[
 \begin{split}
 K\boldsymbol w&=\boldsymbol w\odot\boldsymbol y,\\
 K(\boldsymbol w\odot\boldsymbol y)
    &=\boldsymbol w\odot\boldsymbol y^{\odot2}/2+\boldsymbol U,\\
 K(\boldsymbol w\odot\boldsymbol y^{\odot2})
    &=\boldsymbol w\odot\boldsymbol y^{\odot3}/3+\boldsymbol G,\\
 K\boldsymbol U&=\boldsymbol H .
 \end{split}
\]
On the final three rows add controls for
\(\boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
-\boldsymbol w\odot\boldsymbol y^{\odot4}/4\) and
\(\boldsymbol l=K(\boldsymbol y\odot\boldsymbol U)\).
Make both densities annihilate every size-five source by forcing
their four power moments to lie along \(\boldsymbol\lambda\).
The four- and six-donor determinants used here are
\(1/6146560000000\) and \(-1/16866160640000000000\);
the terminal power-moment determinant is \(-5/120932352\).
All three are units.

The forward cross block is \((EJ-BE)\Pi\), with \(E\) evaluation
at the high clocks and \(Jf(X)=\int_0^X f\). For one primitive
source the forward error is \(B\) times the existing error plus
\((BE-EJ)\rho_t\). Two first errors cannot meet through order
nine, so every effect is propagated by a word of at most
\(8-|t|\) high primitives or clock multiplications. For the
reversed word starting from \(\boldsymbol w\), let
\(\boldsymbol a\) be its weighted value, and \(q\) its scalar value
with adjoint primitive \(J^*q(X)=\int_X^1q\). The payment is
\[
 \bigl(K\boldsymbol a-\boldsymbol w\odot EJ^*q\bigr)^\top E\rho_t
 -\bigl(\boldsymbol a-\boldsymbol w\odot Eq\bigr)^\top EJ\rho_t .
\]
This follows from reversing the weighted array and using the
degree-eight quadrature for polynomial integration by parts.

With reverse clock multiplication expressed using \(1-X\), the
defect of the reversed word is zero through length one; at
length two it is either zero or \(\boldsymbol U\);
at length three it is one of zero,
\(\boldsymbol y\odot\boldsymbol U\), \(\boldsymbol G\),
or \(\boldsymbol G/2+\boldsymbol H\).
The first two lengths therefore use the corresponding power
moments of \(\boldsymbol U,\boldsymbol G,\boldsymbol H\).
At length three, \(K\boldsymbol G\) and \(K\boldsymbol H\) lie in
the span of \(\boldsymbol H,\boldsymbol l\). This leaves exactly
the two size-five payments supplied by \(\boldsymbol k,\boldsymbol l\).

## Exact checks

The constructor builds the physical matrix from the paid linear
identities above. An independent program reads only the literal
tableau; it evaluates all **486** rooted conditions using a common
integer scale, checks 15 distinct strict rows, and checks the
tenth bush defect. Neither check uses floating-point arithmetic.

    python3 -B audit_tableau.py
    python3 -B build.py /tmp/erk9-fifteen-rebuilt.json
    cmp tableau.json /tmp/erk9-fifteen-rebuilt.json
    sha256sum -c arithmetic-sha256.txt
