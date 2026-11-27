# Exact order eleven in fourteen real-algebraic DIRK stages

A literal **fourteen-stage lower triangular** tableau of exact classical
order eleven is constructed below over a real number field of degree at
most sixteen. The independent uniform lower bound is thirteen stages,
so the verified real and real-algebraic intervals are **13–14**.
This is a new exact reproduction of the previously tabulated upper,
not a claim that thirteen is impossible or that these coefficients
are rational. The [characteristic-43 control](../dirk11-width14-f43-reflected-shell/README.md)
is separate; no inference about a real point is made from reduction
modulo 43.

The [literal coefficient export](tableau.json) uses ascending coordinates
in four nested monic quadratic quotients. The [exact standard-library
replay](replay.py) reconstructs the tableau, independently isolates its
real specialization, and checks all **3,047** rooted conditions through
order eleven in the exact quotient arithmetic. The twelve-vertex tree
consisting of four leaf children and one seven-vertex bush child fails
with a verified **unit** factorial-scaled residual. The export includes
that residual and its inverse. The order proof is mathematical and
exact arithmetic; a reviewed Lean upper theorem is not asserted in
this packet.

## Real coefficients and the one quadratic

Use the reflected seven-point Lobatto grid \(0,a,b,d,e,f,1\), where
\[
 a=\tfrac12,\qquad b=\tfrac12\Big(1+\sqrt{(15+2\sqrt{15})/33}\Big),
 \qquad d=\tfrac12\Big(1+\sqrt{(15-2\sqrt{15})/33}\Big),
 \qquad e=1-d,\quad f=1-b.
\]
Let \(m_y\) be their exact interpolatory quadrature masses.
The physical reverse clock list is
\[
 Y=(0,a,b,d,e,a,b,d,f,1).
\]
The weights \(w\) split \(m_a,m_b,m_d\) equally between their two
physical representatives and retain the other quadrature masses.
The ordinary forward clock is \(x=1-y\). The exact replay checks
the scalar moments through degree eleven.

The forward seven-row prefix uses the fixed five-row rational order-six
seed from the [two-ended overlap](../../upper-bounds/rational/dirk-order-ten-overlap/README.md),
now scaled to the first physical forward anchor \(b\), followed by
the two anchors \(b,e\). A polynomial of degree at most four is
recovered from its values at \(0,b,e\) and the two functionals
\(\int_0^b P,\int_0^b xP\). Write this recovery on actual prefix
vectors as \(\Pi\); its anchored primitive is \(I\Pi\). A basis of
the pure size-six residuals is contained in the span of the two
polynomials
\[
 E_0=x^5-\widehat{x^5},\qquad E_1,
\]
where \(\widehat{x^5}\) uses the five exact scalar readings of \(x^5\),
and \(E_1\) has only the second integral reading equal to one.
The forward seed integrates normalized size-six shapes in its ordinary
weight; only its \(x\)-weighted read can distinguish those shapes from
the scalar. These are exactly the two test polynomials used below.

On the reverse side impose the actual matrix identities
\[
 L1=Y,\quad LY=Y^2/2,\quad LY^2=Y^3/3+g,\quad
 LY^3=Y^4/4+U(Y)g,\quad Lg=V(Y)g.
\]
Here \(g\) has equal and opposite values on each of the three repeated
labels and zero elsewhere. The first three nonzero entries are
\(g_a=a^3/6,\ g_b,\ g_d\). The affine functions \(U,V\) are fixed by
the physical rows at \(a,b\), using the inclusive primitive taps through
degree two at \(b\). In particular \(U(a)=3a/2,\ V(a)=a/2\).
The three final reverse columns must be zero for the three later merges.

Here is the exact reduction of the remaining scalar compatibility.
All row vectors in this paragraph are on the five distinct donors
\((0,a,b,d,e)\). Let \(N\) be their barycentric row annihilating
degrees below four and extracting the leading coefficient in degree
four. Let \(W_e\) be the degree-four primitive row to \(e\), and
\(W_a\) the primitive row to \(a\) corrected by **\(-g_a\) at degree
two and \(-U(a)g_a\) at degree three**. Put \(M_a=3a^5/10\), the
degree-four residual of the first physical \(a\)-row. Determine
\(\alpha,\beta\) from
\[
 (E_0(1-e),E_1(1-e))=
 \alpha(E_0(1-a),E_1(1-a))+\beta(E_0(1-b),E_1(1-b)),
 \qquad \lambda=2m_e\alpha/m_a.
\]
All projected degree-five residual contributions are then on the
first and repeated \(a,b\) rows and the singleton \(e\); the rows
at \(d,f,1\) have zero test values. At \(e\), write its digit row
as \(W_e+M_e N\), its \(g\)-read being zero. Payment of \(LY^4-Y^5/5\)
sets the fourth-degree residual of the repeated \(a\)-row to
\(-M_a-\lambda M_e\). Its \(Yg\)-read then has the required value
precisely when
\[
    (W_a-M_aN+\lambda W_e)\big((Y-a)g\big)=0.
\]
In fact the two \(M_e N\big((Y-a)g\big)\) terms cancel; the read of
the \(a g\) part is already fixed by \(Lg\) and cancels with the
first \(a\)-row. This condition is linear in \(g_b,g_d\), since
\((Y-a)g\) on those five donors is supported only at \(b,d\).
It gives \(g_d=\tau g_b\) with the literal \(\tau\) in the replay.

The row at \(d\) is uniquely determined by its degree-zero through
degree-three reads, hence is affine in \(g_b\) after this substitution.
The condition \(L_dg=V(d)g_d\) is now quadratic in \(g_b\).
The replay constructs all three coefficients by the product of two
affine rows and checks the exact tableau equations after choosing
a root. The signed rational interval test selects the root in
\[
                   0.160057 < g_b < 0.160058 .
\]
The other three monic relations are the positive square roots displayed
above. This proves an actual real place by rational interval arithmetic;
the code does not use floating point or assume an algebraic root has a
real embedding. All inverse calls are proved by multiplication to one
in the exact degree-at-most-sixteen algebra before specialization.

The remaining rows are square linear solves. The repeated \(b\)
row has two free grade-five choices, as its donor set contains
five distinct clocks plus separate \(a,b\) contrasts. The very
last three reverse rows have zero tests, so no additional grade-five
mass condition is needed there. The replay directly checks all five
reverse identities and both weighted grade-five tests in the
quotient tower.

## Forward assembly and rooted checks

Take the weighted reverse transpose \(T\). At the forward suffix,
the action on a stage column \((u,v)\), split into prefix and suffix,
is
\[
                     I(\Pi u)+T(v-\Pi u).
\]
This includes all inclusive implicit diagonal taps. The three leading
suffix rows are literally identical to the origin and the two anchor
rows of the prefix; the replay checks whole rows, then folds columns
and output weights. The final \(14\times14\) matrix is checked
lower triangular before any tree evaluation.

For intuition about the shell, ordinary tail defects first appear
at grade six (rooted order seven). Through order eleven no node can
have two children with such high derivative defects. Expanding a
tail defect therefore gives single-input linear words in \(T\) and
the clock. On the other side of the weighted pairing, reverse words
of degree at most four agree with the exact polynomial primitive
and multiplication actions up to linear clock multiples of \(g\).
Those contrasts are dark against every clock polynomial. The only
new degree-five reads are \(LY^4-Y^5/5\) and \(L(Yg)\) against the
size-six prefix residuals, exactly the two tests above. The scalar
terms cancel by ordinary quadrature and integration by parts.

The exact order certificate does not rely on that explanation or
on an unverified enumeration theorem. It directly rebuilds and
tests the elementary stages for every unordered rooted shape,
using the child-multiset recursion through grade eleven and checking
every normalized weight, with shape counts
\(1,1,2,4,9,20,48,115,286,719,1842\). Any ordering of sibling
branches has the same expression over a commutative coefficient
algebra. The verified unit residual means that the twelfth-order
failure survives the chosen real specialization.

## Reproduction

```sh
python3 -B replay.py --export /tmp/dirk11-tableau.json
cmp /tmp/dirk11-tableau.json tableau.json
```

`--quick` checks the exact scalar intervals and reconstruction without
the all-rooted order replay. It is not a replacement for that replay.
