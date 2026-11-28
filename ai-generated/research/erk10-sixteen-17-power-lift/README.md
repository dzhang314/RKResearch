# The sixteen-stage exact ERK10 lift at prime 17

The [literal prime-field method](../erk10-sixteen-f17/README.md)
lifts compatibly to every \(\mathbb Z/17^n\). This yields exact order ten
with sixteen strictly explicit stages over every nontrivial
commutative ring in which the scalar 17 is nilpotent. It also yields
a tableau over \(\mathbb Z_{17}\), hence over \(\mathbb Q_{17}\).
This is an upper bound on those coefficient domains, not a minimum,
rational result, or a bound over the full factorial localization.

The all-power proof below is mathematical with exact arithmetic
receipts. It is not a Lean result for the powers; the prime-field
certificate is separate. The four frozen higher-power fixtures are
[17²](literals/mod17pow2.json), [17³](literals/mod17pow3.json),
[17⁴](literals/mod17pow4.json), and [17⁵](literals/mod17pow5.json).
Each is checked against all 1,205 ordinary rooted conditions.

## Exact prefix and coordinate order

The base coefficient chart is
\(\mathbb Z_{(17)}[\theta]/(3\theta^2-15\theta+20)\).
The first seven rational rows use the dense-family parameters
\(f=1,v=3,r=4,g=0\); the eighth row gives the order-five output at
clock \(\theta\). The [coordinate fixture](prefix-algebraic.json)
stores each number as \(a+b\theta\).
The exact replay reconstructs a dense-order-five decoder \(\Pi\)
from the actual 17 small tree profiles, checks
\(\Pi_0=\boldsymbol e_0^\top\) for the constant coefficient row,
and checks \(J\Pi\) at \(\theta\) is the literal eighth row padded
by zero. Here \(Jf(X)=\int_0^X f\).
That row has exact stage profiles through size six. The
size-six polynomials
\[
 \rho_\tau(X)=|\tau|X^{|\tau|-1}/\tau!-
               \Pi\boldsymbol\Phi_\tau(A_{\rm old})
\]
span the three checked basis rows \(H_6\); the replay eliminates
every size-six residual by these normalized echelon rows, with
no further divisions. The two-coordinate common denominators
for the matrix, decoder and \(H_6\) are respectively
432, 960 and 240, all prime to 17. These are identities in the
stated localized algebra, not rank assertions inferred from a
finite-field calculation. Scaling the prefix by \(\xi/\theta\)
preserves those identities and sends the endpoint to \(\xi\).
For every higher tree used as a source here, \(\rho_\tau(0)=0\)
because the decoder's constant coefficient is the old origin.

The input vector is
\[
       (\theta,x_1,x_2,x_3,x_4,x_5,x_6,x_7,x_8)
       \equiv(10,7,15,10,11,16,2,8,14)\pmod {17}.
\]
Reverse row 0 is separately \(x_0=1\), and the alias is
\(\xi=x_8=14\). The variables are \(\theta,x_3,x_5\) in this
order. All other clocks are kept at the displayed integers.
The ten scalar sites are the old origin zero and these nine
raw reverse sites. Their signed cardinal-integral weights
integrate scalar degree at most nine, since all pairwise
differences are units. The old origin takes the zero-clock mass.

## The three pressure equations and all unit guards

With \(\boldsymbol y=\boldsymbol 1-\boldsymbol x\) and the
raw scalar masses \(\boldsymbol w\), set
\(\boldsymbol M_j=\boldsymbol w\odot\boldsymbol y^{\odot j}\).
Let
\[
 U_0=0,\qquad
 U_i=\frac{\lambda}{x_i\prod_{1\le j\le8,\ j\ne i}(x_i-x_j)}
       \quad(1\le i\le8)
\]
where the common factor \(\lambda\) sets \(U_1=-w_1y_1^2/2\).
Lagrange leading-coefficient identities give
\(\sum_i U_i x_i^j=0\) for \(1\le j\le7\).
The strictly explicit weighted reverse matrix \(K\) pays
\[
 K\boldsymbol w=\boldsymbol M_1,\quad
 K\boldsymbol M_1=\boldsymbol M_2/2+\boldsymbol U,\quad
 K\boldsymbol M_2=\boldsymbol M_3/3+\boldsymbol G,\quad
 K\boldsymbol U=\boldsymbol H.
\]
The vectors \(\boldsymbol G,\boldsymbol H\) lie in the span
of \(\boldsymbol U,\boldsymbol x\odot\boldsymbol U\).
Their two coefficients come from the actual first two
nonorigin rows. The third nonorigin row has three earlier
donors and pays its first three reads by a square solve.
The residual in its fourth read is pressure \(E_1\).
Thus \(E_1=0\) pays all four reads at that row.
Later rows pay four reads by solving on donors 0 through 3.

At a later row a free tap to a new donor is accompanied by
the change on donors 0 through 3 that makes its four read
increments zero. Keep just the five free taps
\[
             (5,4),\ (6,4),\ (6,5),\ (7,4),\ (7,5)
\]
and set all other new taps to zero (indices are zero-based).
The terminal responses are
\[
 \boldsymbol k=K\boldsymbol M_3-\boldsymbol M_4/4,\qquad
 \boldsymbol r=K(\boldsymbol x\odot\boldsymbol U).
\]
Each must annihilate the three \(H_6\) tests rescaled to the
new alias, giving six affine equations in the five taps.
Order the equations first on \(\boldsymbol k\) and then on
\(\boldsymbol r\), with the basis rows in the order written
in the fixture. Solve equations \(0,1,3,4,5\), and denote
the residual in equation 2 by \(E_2\).
This pays all six equations when \(E_2=0\).
The third required equation is \(E_0=3\theta^2-15\theta+20=0\).
This order of equations, variables and affine pivots is fixed.

Every operation is polynomial or division by a unit on the
residue neighborhood of the starting vector. The cardinal
difference products in site order \(0,x_0,\ldots,x_8\) reduce
to \(4,9,10,3,2,10,5,1,6,6\); their masses reduce to
\(6,9,11,12,12,2,10,6,4,14\).
The cofactor denominators also use only unit clock differences
and nonzero \(x_i\); the first explicit tap divides by the
origin mass 9. Other scalar divisions are by \(\theta,\xi\)
(residues 10 and 14), by numbers \(1,\ldots,10\), or by the
algebraic prefix denominators given above. The Gauss
elimination pivots in residue arithmetic are:

| Solve | Pivot residues in order |
| --- | --- |
| First two donors | 9, 2 |
| Compression coefficients for each of \(\boldsymbol G,\boldsymbol H\) | 6, 5 |
| First three donors | 9, 2, 1 |
| First four donors, including compensation directions | 9, 2, 1, 11 |
| Five selected terminal equations | 10, 11, 3, 7, 2 |

The terminal solve uses the row-swap indices \(2,3,2,4,4\)
at its successive pivots; all other solves use their row
order. The arithmetic replay logs and verifies the same guards.

## Why the equations imply the ordinary order conditions

Let \(B\) be the forward high block, the transpose of \(K\)
with the indices reversed. Put \(\mathcal E f=(f(x_i))_i\)
in forward high order. The forward attachment to the prefix
is \((\mathcal E J-B\mathcal E)\Pi\).
In the first high row \(B\) is zero, and
\((\mathcal E J)\Pi\) there is the actual prefix endpoint
row at \(\xi\). Those two fully equal rows can merge, redirecting
every later tap and summing their weights. The resulting width
is \(8+9-1=16\).

Write \(f_\tau(X)=|\tau|X^{|\tau|-1}/\tau!\) for the ideal
stage profile. The actual high action on \(\Phi_\tau\) differs
from \(\mathcal E Jf_\tau\) by the action of \(B\) on the
previous high error, plus \(B\mathcal E\rho_\tau-\mathcal E J\rho_\tau\).
This follows by substituting the cross block. The source
\(\rho_\tau\) vanishes for \(|\tau|\le5\). When forming a rooted
product of size at most ten, at most one factor contains a
source of size six or greater. The other factors are exact
scalar primitives, constant multiples of powers of the clock.
Expanding the recursion therefore propagates each source by
a linear combination of words in matrix action and scalar
clock multiplication. For a source of size \(m\) the words have
at most \(9-m\) letters, since the source first needs a parent.
Thus the longest exterior word has length three.

Move such a word to the raw weighted transpose using the
finite dot products. Its terms give the source payment
\[
 \langle \rho_\tau,KT\boldsymbol w\rangle-
 \langle J\rho_\tau,T\boldsymbol w\rangle
\]
where \(T\) is a reverse word in \(K,Y\) and \(Y\) means
multiplication by \(\boldsymbol y\). Using \(Y=1-X\) instead
of \(X\) merely takes linear combinations of shorter words.
The ideal action of \(K\) on a weighted scalar polynomial
replaces the polynomial \(f(X)\) by \(\int_X^1 f\).
The scalar rule integrates the ideal pieces of the two
terms exactly: their degrees are at most
\(m-1+(9-m)+1=9\). The old origin term vanishes because
\(\rho_\tau(0)=J\rho_\tau(0)=0\). The two ideal integrals
agree by polynomial integration by parts.

The nonideal pieces are exactly those paid by the raw
moments above:

- For exterior length zero there is no discrepancy because
  \(K\boldsymbol w=\boldsymbol M_1\).
- At length one, the next action has only the error
  \(\boldsymbol U\). Here \(\deg\rho_\tau\le7\).
- At length two, the word can already contain
  \(\boldsymbol U\), which kills \(J\rho_\tau\) through
  degree seven. The next action can contain
  \(\boldsymbol G,\boldsymbol H\); they kill all
  powers \(X,\ldots,X^6\), and \(\deg\rho_\tau\le6\).
- At length three the source has size six. The word errors
  are in the span of \(\boldsymbol y\odot\boldsymbol U\),
  \(\boldsymbol G,\boldsymbol H\), which kill the primitive
  test \(\deg J\rho_\tau\le6\). The next action can additionally
  produce \(\boldsymbol k,K(\boldsymbol y\odot\boldsymbol U),
  K\boldsymbol G,K\boldsymbol H\). The last three lie in
  the span of \(\boldsymbol H,\boldsymbol r\); the six
  terminal equations pay \(\boldsymbol k,\boldsymbol r\)
  on all of \(H_6\), and \(\boldsymbol H\) is already paid.
  This follows also by expanding the eight words of length
  three and using the four displayed actions.

Each source payment is therefore zero. The weighted output
of every actual rooted profile through order ten is its
ideal moment, and the ideal moment is \(1/\tau!\) by the
scalar rule. This proof works in the guarded localized
algebra and after any of the coefficient reductions,
not merely at the four frozen higher powers.

## Lifting and exactness

The pressure map \((E_0,E_1,E_2)\) is rational with all the
verified unit denominators above. Its residue Jacobian in
variables \((\theta,x_3,x_5)\) is
\[
                    \begin{pmatrix}
                    11&0&0\\0&11&5\\1&2&13
                    \end{pmatrix}\pmod {17},
\]
of determinant 1 modulo 17. The exact replay computes it
by replacing one variable at a time by its value plus 17,
evaluating modulo \(17^2\), and dividing the differences by
17. For a rational function with unit denominators this is
its ordinary first derivative modulo 17, by the immediate
linear expansion of an inverse.

Inductively, if the pressures vanish modulo \(17^n\), replacing
the three variables by themselves plus \(17^n\) times a
correction changes the pressures by \(17^n\) times that
same Jacobian modulo \(17^{n+1}\). Higher terms are multiples
of \(17^{2n}\). The invertible residue matrix chooses the
correction to kill the remaining errors. The guards keep
their initial unit residues, so the construction works at
each exponent. Every literal coefficient is compatible
with reduction. A nontrivial ring with \(17^n=0\) receives
a unital map from \(\mathbb Z/17^n\); the compatible sequence
also defines a tableau over \(\mathbb Z_{17}\). All order
conditions are polynomial identities and hence hold after
these coefficient transfers or in the inverse limit.

The eleven-bush factorial-scaled defect is 2 at the base
field. Each lifted defect is congruent to 2 and therefore
a unit in \(\mathbb Z/17^n\) or \(\mathbb Z_{17}\).
A unital coefficient map preserves that unit, so the
method remains exact order ten over each nontrivial target.

## Reproduction

    python3 -B verify_prefix.py
    python3 -B build.py
    python3 -B verify_lifts.py
    sha256sum -c literal-sha256.txt
    sha256sum -c source-sha256.txt

The builder regenerates the original prime-field literal and
all four higher powers in their recorded chronology. To test
another exponent or print the literal tables:

    python3 -B build.py --exponent N --emit /tmp/erk10-lifts

The separate literal verifier reads no prefix or pressure
equations.
