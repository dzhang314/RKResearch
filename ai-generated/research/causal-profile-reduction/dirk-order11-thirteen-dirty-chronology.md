# Chronology and virtual quadrature on two normalized DIRK11/13 faces

Neither face is excluded by this note. The real stage interval is still
**13–14**. The argument uses the same normalization and grade-six surplus
as the [signed cubic census](dirk-order11-thirteen-signed-cubic-census.md):
actual real rooted order eleven, thirteen physical stages, lower
triangular \(A\), forward \(C(2)\), and reflected \(D(1),D(2)\). It
does not assume positive weights, distinct dirty and clean numerical
labels across the two sets, or clocks in the integration interval, nor
that a weighted transpose of a tableau with ghosts attains any order.

Use \(C=\operatorname{diag}(c)\), \(\beta=b^\mathsf T\),
\(g=Ac^2-c^3/3\), \(E_j,F_j\) for true tree columns and zero-profile
columns of grade at most \(j\), and \(r\) for the number of distinct
active dirty labels. We use the paid rules
\[
 \langle u,v\rangle_\beta=\int_0^1 P_uP_v\quad
 (u\in E_m,\;v\in E_n,\;m+n\le10),
 \qquad A(E_j)\subset E_{j+1},\quad P_{Au}=I P_u,
\]
where \(I P(x)=\int_0^x P(t)\,dt\), whenever the relevant scalar
profiles are used. These identities follow from root products and the
normalized unary tree. In particular a genuine \(F_j\) column kills
all ordinary probe degrees \(0,\ldots,10-j\). Write
\(I^\leftarrow P(x)=\int_x^1 P(t)\,dt\).
The lower-grade scalar columns and products used below fit within this
budget. The orthogonal quadrature and residue arguments are over the
reals, not claimed over arbitrary nonordered fields.

## Two active dirty labels

The census gives two active signed pairs, two singleton ghosts, and
seven active clean rows at distinct numerical clocks, including origin
and terminal. The two pair members have the same nonzero value of \(g\)
and opposite nonzero weights; the two ghosts have weight zero.
The four distinct physical dirty labels give
\(F_4=g\mathcal P_1(c)\) and \(F_5=g\mathcal P_2(c)\). The two pair
contrasts span \(\operatorname{Ann}E_6\). Both contrast rows multiplied
by \(A\) have nonzero taps at both ghosts. Recall that both ghosts
precede either pair closure, and the two pair intervals overlap
chronologically.

**First clean row.** The earliest nonorigin clean row \(x\ne0\)
numerically integrates every monomial through degree four, because its
primitive defects through grade five vanish there. It also kills both
\(g\) and \(Cg\), since \(Ag\in F_4\) and \(A(Cg)\in F_5\).
If at most two distinct nonzero-defect labels occur earlier, grouping
the two reads by the distinct dirty labels gives zero aggregate taps
at each: the two clock equations are invertible by elementary
Vandermonde, and within each label the nonzero \(g\) is constant.
This argument still applies if a dirty numerical label equals \(0\)
or \(x\). The surviving clean reads at \(0,x\) then yield the
trapezoid formula by the degrees zero and one, and degree two gives
\(x^3/2=x^3/3\), impossible. Thus at least **three distinct dirty
labels** occur before the first nonorigin clean.

**Last clean row.** Only here introduce the weighted transpose
\(L=B_{\rm act}^{-1}(A_{\rm act})^\mathsf T B_{\rm act}\) on the active
principal submatrix, read chronologically backwards, with \(y=1-c\)
on those stages. This is merely a convenient notation for matrix
identities. The literal \(D(1),D(2)\) imply \(L1=y,\ Ly=y^2/2\).
The genuine reflected cubic \(G=\beta y^2 A-\beta y^3/3\) is a
nonzero multiple of \(\beta g\) by the census, hence
\(Ly^2=y^3/3+\tilde g\) for \(\tilde g=\kappa g\) on the active rows.
The genuine fourth reflected defect \(G_4=\beta y^3 A-\beta y^4/4\)
annihilates \(E_6\) by the grade-four/grade-six paid pairing.
Also \(GA\) annihilates \(E_6\) since \(A(E_6)\subset E_7\).
Both rows lie in the two-pair contrast plane. Hence at every active
clean row in reverse, \(L\) integrates degrees through three and
\(L\tilde g=0\).
At the first nonorigin reverse clean, there can be no more than one
later dirty label in forward chronology only if all taps to that
label aggregate to zero (use the single \(\tilde g\)-read and its
constant nonzero value there). Only the reverse origin and the actual
clean stage remain, so degrees zero through two give the same
trapezoid contradiction. Thus the last nonterminal clean precedes
at least one occurrence of **each** active dirty label. Both pair
closures are after all five interior clean rows. The first clean is
after at least three of the two pair starts and the two ghosts.
At most one of these four rows is not strictly before that clean.

**Late ghost cut.** Suppose a singleton ghost \(\gamma\) lies after
the first clean. By the above cut, both pair starts and the other
ghost are earlier. The census escape guarantees that each closer
has nonzero tap in column \(\gamma\) (the earlier member of either
pair cannot tap that column). In this column
\[
       (\beta C^k A)_\gamma=0\quad (0\le k\le3),
       \qquad (\beta g A)_\gamma=0.
\]
Indeed \(b_\gamma=0\); \(D(1),D(2)\), \(G\), and \(G_4\) yield the four
reflected moment identities first, hence the displayed ones by
binomial conversion. The \(\beta gA\) read is a scalar multiple of
\(GA\) and also has only pair support.

Both pair clocks differ from \(1\). For if one coincided with the
terminal clock, at its earliest reverse occurrence after the terminal
the active donor clocks would be zero and at most one other label
(all five interior clean rows lie later in reverse). At that zero
clock, \(Ly=y^2/2=0\) would kill the aggregate on the only possible
nonzero label. Then \(Ly^2=0\) there, inconsistent with this being a
dirty row. Zero clock on other earlier reverse physical rows causes
no change.

If at most one interior clean followed \(\gamma\), all possible active
donors for its column would have at most four distinct clock labels,
the two closer labels included. The four moments kill all grouped
taps. The terminal cannot collide with a closer, and at most one
closer can collide with the single later interior clean. A noncancelled
closer is impossible. Therefore at least **two** interior clean rows
follow a late ghost.

**Exactly two after the late ghost.** Let \(e,f\) be those two rows in
physical order, and \(u,v\) the two active dirty labels. If the five
labels \(e,f,u,v,1\) are distinct, the four column moments force the
five weighted taps to be proportional to the barycentric row at
these labels. The proportionality is nonzero because of the two
closer taps. If \(R(X)=(X-e)(X-f)(X-1)\), the final read
\((\beta g A)_\gamma=0\) gives
\[
                 \frac{g_u}{R(u)}=\frac{g_v}{R(v)}.
\]
For the reverse first interior clean \(z=1-f\), put
\(\tau=1-u,\ \sigma=1-v\). Its only active donor clocks, including
the diagonal, are \(0,\tau,\sigma,z\), and its degree-three
primitive row is unique. The weights at \(\tau,\sigma\) are
\[
 \frac{z^3(2\sigma-z)}{12\tau(\tau-\sigma)(\tau-z)}, \qquad
 \frac{z^3(2\tau-z)}{12\sigma(\sigma-\tau)(\sigma-z)}.
\]
Pairing with \(\tilde g\) yields
\[
       g_u\,\frac{2\sigma-z}{\tau(\tau-z)}
       =g_v\,\frac{2\tau-z}{\sigma(\sigma-z)}.
\]
Use the previous ratio and cancel the nonzero
\((v-f)(v-1),(u-f)(u-1)\); equivalently cross-multiplying without
dividing by \(2\tau-z\) or \(2\sigma-z\) yields
\((v-u)(1+f-2e)=0\), so \(e=(1+f)/2\).

For collisions the four moments kill each aggregated clock mass.
Neither closer can survive alone, so one collision is impossible and
two collisions must pair the two clean labels bijectively with the
two dirty labels. The reverse first interior clean at \(z=1-f\)
then has only three possible distinct donor clocks, \(0,1-e,z\).
Its actual degree-three primitive kills the nodal cubic
\(t(t-(1-e))(t-z)\) and therefore
\(z^3(2(1-e)-z)/12=0\). Again \(e=(1+f)/2\).
Thus no distinct-across-color assumption is needed for the midpoint.

The seven clean clocks form an anchored degree-ten quadrature
because pair weights cancel and ghosts carry no ordinary weight.
Their five interior-label monic nodal hull is in the shifted
\(x(1-x)\)-Jacobi pencil. Explicitly the two generators, up to
normalization, can be taken as
\[
 P_4=42X^4-84X^3+56X^2-14X+1,\quad
 P_5=(2X-1)(66X^4-132X^3+84X^2-18X+1).
\]
Orthogonality of the interior hull to degrees zero through three
follows by applying \(x(1-x)\) times that hull times the test
polynomial to the exact quadrature. The two displayed polynomials
are directly orthogonal to those tests and independent.
Eliminating the pencil parameter using its two roots \(f,(1+f)/2\)
leaves, after division by \(f-1\ne0\) and a nonzero constant,
\[
 1386 f^8-2772 f^7+1092 f^6+1134 f^5-1077 f^4
                 +252 f^3+22 f^2-14 f+1=0.
\]
This is only a necessary gate on this late-ghost chart. It does not
eliminate all real solutions of the scalar gate, nor all two-label
schedules.

## Nine active dirty labels

There are nine distinct active dirty singletons with physical clocks
\(x_i\), and four active clean rows of distinct clocks \(0,e,f,1\), named
in physical order. Dirty numerical clocks may coincide with a clean
numerical clock. The last section of the census gives a polynomial
\(U\) of degree at most three such that \(g_i=U(x_i)\) on the dirty rows,
\[
       b_i=\frac{\kappa}{U(x_i)V'(x_i)},\qquad
       V=\prod_{\text{dirty }i}(X-x_i),\quad \kappa\ne0.
\]
Write \(Q=(X-e)(X-f)U(X)\). The masked positive-square payment gives
\(\deg U=3\) (otherwise the square test for \(Q\) costs degree at
most ten), and \(Q\) is orthogonal to every degree-three polynomial
for the positive weight \(x(1-x)\,dx\). It has at least four distinct
sign changes in \((0,1)\): otherwise multiply by the at most three
linear factors for its interior sign changes and integrate the
nonzero constant-sign product. Since its degree is five, these
four roots are simple and the fifth is real, simple and distinct.
The three roots \(\rho\) of \(U\) are therefore simple and distinct
from \(e,f\). None is a dirty root of \(V\).

**Seven-site virtual quadrature.** For any polynomial \(F\) of degree
at most ten, the proper rational function \(\kappa F/(UV)\) has zero
residue at infinity. Its sum of residues at the nine dirty labels
can therefore be replaced by masses at the three roots of \(U\), with
\[
                  m_\rho=-\frac{\kappa}{U'(\rho)V(\rho)}\ne0.
\]
This yields a seven-site anchored degree-ten quadrature on
\(0,e,f,1\) and the three \(\rho\)'s. If \(U(0)\) or \(U(1)\) vanished,
there would be at most six distinct sites including the endpoints.
The nonnegative \(x(1-x)\) times the square of the other-node
polynomial would be degree at most ten and integrate positively
while all quadrature taps vanish; impossible. Consequently all seven
virtual sites are distinct and \(U\) is nonzero at each clean
physical row. This proof never divides by \(U\) at a clean row
without the preceding check.

**Exact grade-six mode.** From the census,
\(\operatorname{Ann} E_6=\operatorname{span}(\beta g,\beta Cg)\).
On dirty slots these rows give barycentric tests annihilating
exactly the evaluation image of degree at most six: polynomial
interpolation gives a seven-dimensional kernel, matching the
two independent rows on the nine distinct dirty nodes.
Thus each \(F_6\) column \(v\) has a unique dirty trace polynomial
\(W_v\) of degree at most six. In the five paid moments for \(F_6\),
the dirty sums can be replaced by the same three residues at
\(\rho\), since \(\deg(X^kW_v)\le10\) for \(k\le4\).
The origin entry of \(F_6\) is zero, hence among the six nonorigin
virtual sites, the weighted entries
\[
       \bigl(b_e v_e,b_f v_f,b_T v_T,\
                         (m_\rho W_v(\rho))_\rho\bigr)
\]
form the one-dimensional barycentric annihilator of degrees zero
through four. Every entry of its generating vector is nonzero.
Restriction of \(F_6\) to the dirty profiles is injective: if
\(W_v=0\) the five clean moment reads force all clean entries zero.
In particular the kernel of the virtual read is exactly the
four-dimensional \(g\mathcal P_3(c)\) (actual \(g\) is zero
on the clean sites), and the one new direction is fixed up to
its coefficient by this single explicit barycentric line.

**Two-sided chronology.** Put \(h=U(c)-g\in E_3\) with scalar
profile \(U\), supported exactly on the four clean stages.
All operators below act on this literal vector, not on a
constructed transposed method. The forward vectors \(A(Ch)\) and
\(A(C(C-e)h)\) restrict to dirty polynomials of degrees at most
five and six, since \(E_5=\mathcal P_5(c)+g\mathcal P_2(c)\) and
the \(E_6\) restriction was just proved. They are both nonzero on
the dirty support. To see this for either \(Az\), with
\(z=Ch\) or \(z=C(C-e)h\), suppose \(Az\) is supported on the clean
rows. It is zero at the origin. Choose a nonterminal clean interior
row \(q\) on the support of \(z\) (the former vector has both \(e,f\),
the latter has \(f\)). Choose a polynomial \(\Psi\) of degree at
most five with double zeros at the two other nonorigin clean clocks,
\(\Psi'(q)=0\), and \(\Psi(q)\ne0\). Such a polynomial is \(H\)
times \(1-H'(q)(X-q)/H(q)\) for \(H\) the product of those two
squared linear factors. Then
\[
     0=\langle \Psi'(c),Az\rangle_\beta
       =\int_0^1 \Psi'\, I P_z
       =-\int_0^1 \Psi P_z
       =-b_q\Psi(q)z_q\ne0.
\]
Both scalar integrations and the final virtual-free read are paid
(at most grades four plus six, or five plus five). The boundary
terms vanish by \(\Psi(1)=0\) and \(I P_z(0)=0\). Causality
gives a zero on every dirty stage earlier than the first
nonzero clean entry of \(z\). Thus at most five dirty rows precede
\(e\), and at most six precede \(f\).

For the reverse cut take \(z=(1-C)h\) or \(z=(1-C)(C-f)h\) of
grade four or five, respectively. Write
\[
       \beta\operatorname{diag}(z) A
            = \beta\operatorname{diag}(I^\leftarrow P_z(c)) + R.
\]
Here \(R\) is a row, and \(R\in\operatorname{Ann}E_5\) in the first
case or \(\operatorname{Ann}E_4\) in the second: test against each
actual column in the stated space, use the paid product identity and
Fubini for the scalar integration. Testing these \(R\)'s against
\(g\mathcal P_2(c)\) or \(g\mathcal P_1(c)\), respectively, yields
that their restrictions divided pointwise by the dirty \(b_i\) are
polynomials of degrees at most five or six. In detail, the rows
\(R_i U(x_i)\) are proportional positionwise to barycentric weights
times a numerator polynomial of degree at most \(9-2-2=5\)
or \(9-1-2=6\), by distinct-node interpolation. Dividing by the
literal dirty \(b_i=\kappa/[U(x_i)V'(x_i)]\) gives the assertion.
The scalar primitive \(I^\leftarrow P_z\) has the same degree bound,
so the full backward row divided by \(b_i\) has that bound on dirty
coordinates.

These two backward dirty polynomials cannot vanish identically.
If either row were supported only on the clean sites, its terminal
coordinate would be zero by causality. Isolate a supported interior
clean \(q\) in \(z\) with a degree-five Hermite polynomial \(\Psi\)
as above, now with double zeros at the other two possible clean
reads in \(\{0,e,f\}\), and \(\Psi'(q)=0,\ \Psi(q)\ne0\). The
row applied to \(\Psi'(c)\) must be zero if it is clean-supported;
the paid scalar evaluation is instead
\(\int P_z I(\Psi')=\int P_z\Psi=b_q z_q\Psi(q)\ne0\), since
\(\Psi(0)=0\) and \(z\) is supported only on \(0,e,f\).
No triangle or order claim for a transposed method was used.
By physical causality the first backward row vanishes on every
dirty after \(f\), the second after \(e\). Thus at most five dirty
rows follow \(f\), and at most six follow \(e\).

If \(a,m,d\) count dirty rows before \(e\), between \(e,f\), and
after \(f\), the final chronology is
\[
   3\le a,d\le5,\qquad m=9-a-d\ge0.
\]
There are eight possible triples. These exact restrictions and the
virtual coefficient profile permit smaller elimination problems;
they do not prove that any of the eight schedules admits a tableau.

The [Lean scalar gates](../../lean/RKCert/ReviewedNative/DIRK11DirtyChronologyScalarGates.lean)
verify the midpoint cross subtraction and the exact eighth-degree
pencil elimination over a characteristic-zero field. They were
checked on Lean/Mathlib 4.36.0 with the standard axioms. The tableau
reductions and virtual quadrature are proved mathematically above.
