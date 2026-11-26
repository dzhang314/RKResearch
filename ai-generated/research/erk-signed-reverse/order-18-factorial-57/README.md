# An exact 57-stage explicit method of order 18

The literal tableau in this packet has exact order 18 over
\(U\coloneqq\mathbb Z[1/18!]\), and after base change to any nonzero commutative ring in which \(18!\) is a unit. It uses neither an inverse of 19 nor any of the extra
primes required by the older localized 59-stage tableau. The earlier
59- and 60-stage tableaux are unchanged. This is an upper bound, not a
claim of minimality or a Lean certificate.

## Selecting the donor degrees and sites

Let \(m\) be the forward chart degree in **tree size**, and take the
reverse chart through tree size \(g\), where \(p=m+g+2\leq 2m+2\).
A chart through tree size \(m\) gives the exact derivative polynomial
\(g_t(x)\coloneqq |t|x^{|t|-1}/t!\) through \(|t|=m\), as a linear read
of the actual prefix coordinates. In reverse clock
\(v\coloneqq 2y-1=1-2x\), put \(H(v)\coloneqq 1-v^2\). Polynomial
integration from the reverse origin is denoted \(\mathcal I\):
\[
 (\mathcal I f)(v)\coloneqq \frac12\int_{-1}^v f(z)\,dz,
 \qquad
 \mu(f)\coloneqq\frac12\int_{-1}^1f(v)\,dv.
\]
These are just finite operations with rational coefficients at the
degrees used below.

The only reverse defect for a target order \(p\) arises at word
length \(g\). At that length the forward source comes from tree size
\(m+1\). Suppose the reflected sources are in
\(H\mathcal P_{|S|}\) and satisfy a paid pin \(\ell(f/H)=0\), where
\(S\) is a set of late pure sites and \(\mathcal P_k\) consists of
polynomials of degree at most \(k\). Define its monic hull by
\[
 Q_S(v)\coloneqq\prod_{a\in S}(v-a).
\]
If the point Vandermonde, the factors \(H(a)\), and \(\ell(Q_S)\)
are units, a source is reconstructed from its values on \(S\). In
fact, two quotient fits differ by a scalar multiple of \(Q_S\), and
the pin fixes that scalar. A basis \(e_a\) for this interpolation is
obtained by multiplying each quotient cardinal polynomial by \(H\)
and taking its pin-zero representative. The scalar receiver sites
outside \(S\) and outside the actual reverse donor clocks are
available for live reverse recovery with no new row.

There is a useful separate determinant rule for the live sites. Suppose
the reverse missing polynomials are in
\(G_0\mathcal P_d\cap\ker h\), for a fixed factor \(G_0\) and
one exact high read \(h\) with \(h(G_0)\) a paid unit. The basis
\[
 f_j(v)\coloneqq G_0(v)\left(v^j-\frac{h(G_0v^j)}{h(G_0)}\right),
 \qquad 1\leq j\leq d,
\]
uses no new physical donor. If \(B\) has \(d\) live sites, the
determinant of their weighted evaluations in this basis is
\[
 \det[\lambda_a f_j(a)]_{a\in B,\,1\leq j\leq d}
 =
 \frac{h(G_0Q_B)}{h(G_0)}
 \left(\prod_{a\in B}\lambda_a G_0(a)\right)
 \prod_{a<b\text{ in }B}(b-a).
\]
Indeed, augment the unweighted evaluation rows of
\(1,v,\ldots,v^d\) by the row \(h(G_0v^j)\) at the top. Its
first-row cofactors are the monic hull coefficients multiplied
by the Vandermonde. Elimination using the upper left entry
\(h(G_0)\) gives the stated determinant. Thus the left and right
hull tests need not use the same site geometry. The holes in the
right matrix are paid collectively if the maximal minors generate
the unit ideal. No individual mass \(\lambda_a\) is divided out.

## Applying the two tests

Take \(p=18,m=9,g=7\). Use the unchanged 27-row grade-nine forward
chart from the order-20 factorial construction, and the unchanged
15-row retuned grade-seven chart from the order-15 forward bank as
reverse donor. The latter has clocks \(0,\pm1/3,\pm1/2,\pm1\)
in the centered coordinate. It has the independently checked
higher functional \(h=\ell_7\) through size eight, with
\(h(1+v)=77/8\). The forward source quotients (coefficient order
\(1,v,\ldots,v^7\)) are annihilated by
\[
 \ell\coloneqq(-2487,-6632,1473,3928,5433,14488,9393,25048).
\]
Both boundary vanishing and this pin hold on the actual normalized
size-ten source span. The checker exhibits the closure of that
span under every required rooted attachment, rather than testing
only the bushes or the reverse word trees.

The scalar sites are zero and both signs of
\[
 1/5,\quad 1/3,\quad 1/2,\quad 2/3,\quad
 1,\quad 3/2,\quad 2,\quad 5.
\]
All pairwise differences are units. The cardinal weights
\(\lambda_a\coloneqq \mu(\operatorname{card}_a)\) integrate through
degree 16 by construction and through degree 17 by symmetry. Take
\[
 S\coloneqq\{0,\pm1/3,\pm1/2,\pm3/2\},\qquad
 B_{\mathrm{live}}\coloneqq\{\pm1/5,\pm2/3,\pm2,\pm5\}.
\]
The left pivot is \(\ell(Q_S)=-27200/3\), a unit of \(U\). In
particular this is not the order-twenty choice \(\pm2\) for the
two spare pure sites, whose pivot is divisible by 19.

The reverse missing polynomial has degree at most seven, vanishes
at the reverse origin, and is killed by the actual high read. The
right test therefore uses \(G_0=1+v,d=6,h=\ell_7\). The following
six-site subgrids suffice, each obtained by omitting both signs
of one radius from the eight live sites:
```
omitted absolute radius        1/5        2/3          2           5
h((1+v) Q_B)               8184/5  200232/125  -192984/125  -24746/125
unpaid pivot part              31        103         43       12373
unpaid mass part           792809    1579243       3307      616087
```
The four stripped determinants in omission order are
\(320931314200434881954712022713439\),
\(268736618129740906653049136680783\),
\(25585128923402199779798187216158020723\), and
\(212118460830162656162751824136213013\). Their gcd is one.
The receipt gives the four exact determinants, the integer
Bézout combination and the complete paid six-by-eight inverse.
Both the determinant formula and the independently evaluated
matrix are useful here: full rank over the rationals alone
would not establish factorial-unit coefficients.

## Chronology and the order argument

The virtual reverse chronology is the 15 unchanged old donor rows
of mass one, the eight live scalar rows of mass \(\lambda_a\), the
15 negative copies of the old donor rows, the other nine scalar
rows, and then a signed pair at each of the seven sites in \(S\).
The original, live, negative and ordinary scalar receiver rows use
only earlier eligible coordinates. The ordinary receiver incoming
row is the primitive of the reverse chart at its clock. A late
positive row adds the functional
\(\sigma\mapsto\mu(e_a\mathcal I\sigma)\) of the missing reverse
polynomial recovered from the live readings, and a late negative
row uses only the ordinary incoming row. The recovery input is
\(\lambda_a\) times the difference of the live reading and the
old decoder at the same clock. Hence every reverse tap into a
live coordinate is explicitly a multiple of its scalar mass.

Let \(L\) denote the reverse matrix, with both row and column
labels now in reversed (forward physical) order. Write
\(L_{ij}=\beta_jN_{ij}\) where \(\beta\) is the signed mass
vector and all entries of \(N\) are paid. Then
\[
 T_{ij}\coloneqq \beta_jN_{ji}
\]
is strict lower triangular and satisfies
\(\beta_iT_{ij}=\beta_jL_{ji}\). Thus \(L\) is adjoint to \(T\)
in the signed weighted pairing without an assumption of
nonzero or unit masses. For the forward decoder \(D_F\), use
the prefix-to-suffix block \((J-TE)D_F\), where \(E\) evaluates
at physical clocks and \(J\) integrates from the physical origin
to those clocks. The unfolded tableau has 27 forward and 61
virtual suffix rows.

For a source child \(t\), the primitive discrepancy on the suffix
is the sum of \((TE-J)(g_t-D_F\boldsymbol\Phi_t)\) and propagation
of the preceding suffix error by \(T\). Through order 18 no root
product can contain two such errors: each needs a source child of
size at least ten, so two would require a tree of size at least 21.
A single propagated error along a path pairs its source with an
adjoint word in multiplication by the clock and action by \(L\).
Its length is at most \(p-1-|t|\leq7\). At length less than seven
ordinary reverse receiver words and their extra integration are
exact. At length seven, \(|t|=10\) and only the extra application
of \(L\) has a missing polynomial \(\sigma\). The signed late rows
replace its missing pairing by
\[
 \sum_{a\in S}\rho_t(a)\,\mu(e_a\mathcal I\sigma)
   =\mu(\rho_t\mathcal I\sigma),
\]
where \(\rho_t\) is the reflected forward source. All ideal
pairings are equal by triangular polynomial integration, and their
degrees are at most 17. Literal equal incoming rows on the original
reverse donors and their negative copies cancel every reverse word.
Thus every rooted source contribution is zero and the ordinary
scalar quadrature gives all the order coefficients.

In the primal tableau all untapped reverse columns give exactly
the pure primitive row \(J D_F\) at their physical clock. At every
such clock these whole padded rows fold, not just their masses.
The pure origin and the pure physical clock-one row are the
literal existing forward rows with zero-based indices 0 and 16.
The checker verifies these alias identities before the fold, and
also all 5,016 entries of the owner-fold equation. The 57 distinct
rows are consequently
\[
   27+15+17-2=57.
\]

## Exact order without dividing by 19

Let \(C\) multiply by the physical clock and let \(A\) act by
the full tableau. Applied to the leaf, \(C\) adjoins a root
leaf and \(A\) extends the root. Define the size-seven formal
combination \(\mathcal V\) by the words
`ACCACC`, `ACCAAC`, `ACCCCC`, `CCCCCC`, with coefficients
\(136080,-272160,204120,-34020\), respectively, and set
\[
 w\coloneqq C A C^2\mathcal V.
\]
Its nominal polynomial is zero. On the suffix \(w\) itself
is zero, since the core \(AC^2\mathcal V\) is of size ten, at
which the forward chart already gives pointwise exact suffix
derivative values. Its reflected source has left quotient pin
27,720. Therefore the seven-site projector differs from the
identity on that source by \((2079/680)H Q_S\).

The dual words \(LC^6\) and \(L^7\) pair this difference with
their respective missing reverse primitives to give
\(4793/259683840\) and \(-41/3525120\). They are, respectively,
the actual raw rooted outputs of \(C^6A^2w\) and \(A^8w\).
On each path all subsequent formal-zero sources have degree at
most eight. Their shorter reverse words have no projection error
and the scalar degree remains at most 17. Thus no later term
alters either stated next-order value. The finite checker also
evaluates all eight individual actual rooted coefficients and
verifies the two raw outputs directly. Their integer coefficients
\(-1487988403200,-2361305157120\) give a combination of one.

Each size-19 tree factorial is 19 times its child-factorial
product, a unit in \(U\) after the factor 19 is removed.
The two raw combinations therefore give a paid combination of
cleared order defects equal to 19. The size-19 bush has defect
\(19u-1\), with \(u\) its actual raw output, so combining that
defect with \(u\) times the former obtains one. Independently,
the first two actual trees of \(C^6 A^2w\) have cleared defects
\[
 -1789914517373/628227145728000,
 \qquad -5044197405053/628227145728000.
\]
Their integer coefficients
\(-1336212963783938716729344000,474150155143213440073728000\)
already give precisely one. Thus not all order-19 conditions can
hold after any nonzero factorial-unit base change.

The literal common denominator is
`5989441408276957683731078400000000000000`, dividing
\((18!)^5\). The output weight denominator
10,170,998,716,342,464,000 divides \((18!)^4\). Use the machine
receipt for the unpunctuated literals, actual witnesses, and
numerator scale \(e d^{18}\); no inverse of 19 is used.

## Reproduction

Run these commands from this directory. The checker uses exact rational arithmetic and does not import the builder. It verifies the rooted forward closure, the weighted reverse identities, every literal fold, and two distinct next-order unit identities.

~~~sh
python -B check.py .. tableau-18-factorial-57.json receipt-18-factorial-57.json \
  ../order-20-factorial-71/receipt-20-factorial-71.json \
  ../order-15-certificate/receipt-15.json
out=$(mktemp -d)
python -B build.py .. "$out"
cmp tableau-18-factorial-57.json "$out/tableau-18-factorial-57.json"
cmp receipt-18-factorial-57.json "$out/receipt-18-factorial-57.json"
~~~

The previous [59-stage tableau](../order-18-localized-59/README.md) and [60-stage tableau](../order-18-certificate/README.md) remain available.
