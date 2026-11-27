# Universal exact order ten in seventeen explicit stages

This [literal tableau](tableau.json) has **exact order ten in 17
strictly explicit stages over \(\mathbb Z[1/210]\)**, and over
every nontrivial commutative ring in which \(10!\) is a unit.
It improves the [18-stage general-ring result](../erk10-eighteen-ten-clock/README.md).
No minimality claim is made.

The common denominator is again \(800150400=2^7 3^6 5^2 7^3\),
which divides \((10!)^3\). A root with one leaf and one
nine-vertex bush child has order eleven, tree factorial \(99\),
and raw output \(7069/699840\). Its normalized defect is the
unit \(-1/77760\).

## The half-port and the singular terminal moment system

Keep the [nine-row prefix, cubic primitive half-port and
degree-four decoder](../erk10-eighteen-ten-clock/README.md),
the ten scalar quadrature sites \(j/6\), and the same
cofactor density construction. The scalar clock-zero mass
is assigned directly to the old origin. The reverse order
of the other nine sites is now
\[
 (1,-1/2,-1/3,-1/6,1/3,5/6,2/3,1/6,1/2).
\]
In particular the first chronological high row is the half-port,
and its incoming high block is necessarily zero. None of
these nine reverse labels repeats.

Let \(K\) be the raw weighted reverse matrix, the transpose
of the forward high block after reversing both indices.
Use the same four basic reverse actions as in the
18-stage chart, with the same compression of
\(\boldsymbol G,\boldsymbol H\) on the three densities
\(\boldsymbol U,\boldsymbol y\odot\boldsymbol U,\boldsymbol Z\),
where \(\boldsymbol y=\boldsymbol1-\boldsymbol x\) and
\(\boldsymbol Z=\boldsymbol U/\boldsymbol y\) away from clock
one, and zero there. The first three reverse interior rows
fix the coefficients of the compression from their actual
actions. At the third interior row keep the last predecessor
tap free rather than forcing it to zero; recalibrate both
compressed rows using that tap. After this, each later row
pays the four basic actions by a solve on the first four
available donors.

In zero-based reverse indices let \(\boldsymbol p\) denote
the free taps in positions
\[
 (3,2),\ (5,4),\ (6,4),\ (6,5),\
 (7,4),\ (7,5),\ (7,6).
\]
The last reverse row uses just the first four donors.
The six terminal moment equations are the two tests on
each of the three orders of response
\[
 \boldsymbol k=K(\boldsymbol w\odot\boldsymbol y^{\odot3})
      -\boldsymbol w\odot\boldsymbol y^{\odot4}/4,\quad
 \boldsymbol l=K(\boldsymbol y\odot\boldsymbol U),\quad
 \boldsymbol r=K\boldsymbol Z .
\]
The tests are the size-six source polynomials
\(d(X)=X(X-1)(X-1/2)\) and \(d(X)X(X-1)\).
These are linear equations in \(\boldsymbol p\).

The exact matrix and augmented ranks are both **five**.
The full affine solution has particular tap vector
\[
 \boldsymbol p_0=(0,-56/45,-1/9,-5/72,0,16/9,-8/5)
\]
and kernel basis \(\boldsymbol e_0,\ \boldsymbol e_1+\boldsymbol e_4\).
The whole affine matrix has coefficient denominator
\(740880=2^4 3^3 5\,7^3\). In particular setting both free
parameters to zero gives a single paid rational tableau,
not a finite-characteristic or local-ring gluing argument.
The exact singular solve is why a full-rank pivot screen
could miss this chronology.

Use the same forward cross block \((EJ-BE)\Pi\). The first
high row now has clock \(1/2\) and full prefix part
\[
 (193/1920,\ 0,\ 81/640,\ 351/640,\ -7/192,\ -4/15,\
  -7/1920,\ 1/32,\ 0).
\]
Together with its zero high part this is the complete padded
ninth opening row. Redirect every outgoing tap to that old
index and transfer the scalar mass \(199/420\).
This ordinary literal row contraction leaves \(9+9-1=17\)
physical stages, preserving all tree outputs.
The reverse word proof of the 18-stage construction otherwise
applies unchanged because the same six terminal equations
are paid.

## Independent exact verification

The constructor checks the seed source identities and all
reverse equations, the exact affine rank and denominator,
and the complete-row merger. A second program reads the
literal coefficients to check all 1,205 ordinary rooted
conditions through ten, 17 strict distinct rows, and the
unit eleventh-order defect. No floating-point decision enters
either replay.

    python3 -B audit_tableau.py
    python3 -B build17.py --emit /tmp/erk10-seventeen-rebuilt.json
    cmp tableau.json /tmp/erk10-seventeen-rebuilt.json
    sha256sum -c arithmetic-sha256.txt
