# At most one visible quadratic-defect clock with zero output weights

Work over a characteristic-zero field with an actual fourteen-stage
strict order-ten RK tableau, in the
[equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md).
At least one \(b_i=0\). Let \(I\) be the literal ordered set of
live (\(b_i\ne0\)) sites and \(Z\) the zero-weight coordinate space.
A **visible dirty clock** is a numerical value \(c_i\) of a live row
where \(d_i=(Ac-c^2/2)_i\ne0\).
**Result:** there is at most one visible dirty clock.
This does not constrain the clocks of invisible defects at the
zero-weight rows, and does not claim the 15-stage unrestricted bound.

The proof uses a genuinely strict matrix on the live sites, and
does not assign a reciprocal to a zero weight. It shares low-degree
profiles in both orientations only to the precise degree earned
below. In particular it does not assert that the live reversed
tableau has order ten.

## Frontier, weighted ghost taps, and exact low-grade reversal

Write \(E_j,F_j\) for the old actual and pure spaces, \(B=\operatorname{diag}(b)\).
Use \(\beta_j=E_{9-j}^{\perp_{\rm ordinary}}\) as row annihilator of \(E_{9-j}\)
for \(j=2,3,4\), of dimensions \(1,2,3\), respectively.
These are the old reverse spaces \(V_1,V_2,V_3\).
If \(k\le3\) distinct visible dirty clocks occur, the \(k\)
rows \(b\,d\,C^a\) (\(0\le a<k\), where \(bd\) denotes the
entrywise weighted row) lie in and span \(E_{8-k}^\perp\):
paid multiplication kills that space, and on the \(k\)
clocks Vandermonde proves independence. In particular each
physical ghost indicator lies in \(E_{\ell}\), \(\ell=8-k\).
No "generic clock" hypothesis is imposed.

More generally if a numerical ghost vector \(e\in Z\cap E_{\ell}\)
has formal model \(P_e\), then
\[
          \int_0^1 X^i P_e(X)\,dX=0\quad(0\le i\le9-\ell),
\]
since its numerical moments are zero. This does **not** require
\(P_e=0\) at a ghost origin. Consequently for an actual
\(f\in E_a\) with \(a\le8-\ell\),
\[
       \langle f,A e\rangle_B
        =\int P_f J P_e=\int (\bar J P_f)P_e=0 .
\]
Everything is paid: \(a+\ell+1\le9\) and
\(\deg\bar J P_f\le a+1\). In particular
\(bY^j A e_i=0\) for \(0\le j\le k\) at every ghost i.
A latest ghost with only later contributing distinct live
clocks would thus require at least \(k+2\) such clocks,
or else its outgoing column would vanish by Vandermonde.
For \(k\ge1\), \(h_2=2bYA-bY^2\) is a nonzero multiple
of the visible \(bd\) row, and \(h_{2,13}=-b_{13}(1-c_{13})^2\ne0\)
by the shifted-nine frontier. Hence \(d_{13}\ne0\).
In particular row 12 cannot be a ghost: its two outgoing
taps to 13 and 14 would be killed by the first two
moments, since \(c_{13}\ne c_{14}=1\).
Then it would be literally removable.

Now let \(\bar A=B_I^{-1}(A_{I,I})^\mathsf T B_I\), oriented
in reverse physical order. It is strict explicit, with
clock \(Y_I\) by \(bA=bY\). Use the original physical clock
coordinate to express reflected polynomials, so its formal
primitive is \(\bar J P(X)=\int_X^1 P\).
For \(0\le j\le k+1\) let
\[
 H_j=(E_{9-j}|_I)^{\perp_{B_I}}\cap\{v:v_{14}=0\}.
\]
Here \(H_0=H_1=0\).
For \(2\le j\le k+1\) its dimension is exactly \(j-1\)
and \(H_j=F_j|_I\): \(E_{9-j}\) includes all ghosts,
so taking restriction does not change its codimension.
The visible \(bdC^a\), \(0\le a\le j-2\), give the full
lower rank. Point exactness at physical 14 through grade
four gives the last-coordinate-zero condition and paid
orthogonality gives inclusion. This argument does not
suppose the old pure spaces inject into the live projection.

The actual reversed stage pure differences through
grade \(k+1\) belong to these \(H_j\)'s.
For an actual old grade \(j-1\) lift \(x\) and old test
\(z\in E_{9-j}\), adjointness on the submatrix gives
\[
  \langle \bar A x_I,z_I\rangle_{B_I}
   =\langle x,A z\rangle_B-
             \sum_{g\notin I}z_g\langle x,A e_g\rangle_B .
\]
The last sum is zero for \(j-1\le k\) by the displayed
ghost-primitive identity for \(\ell=8-k\).
The first term pays the formal reflected primitive by
integration by parts, because the total degree is at most
nine, so the unary pure difference lies in \(H_j\)
and is zero at the reversed origin. This argument applies
to any reversed grade \(j-1\) numerical pair: its pure
part has an old lift in \(F_{j-1}\) by induction, and
its polynomial part is an original clock polynomial after
reflection. Coordinatewise products of lower pure parts
remain restrictions of actual original pure products;
polynomial multiplication likewise respects the budget.
This establishes the actual reverse pair recursion to
grade \(k+1\).

The reversed numerical profiles are polynomially separated
through that grade: a zero profile paired with \(P\) of
degree at most \(j\) implies \(P(c_I)\in F_j|_I\).
Pairing against old clock \(X^a\) (\(0\le a\le j\)) gives
\(\int P X^a=0\) since \(2j\le8\), hence \(P=0\).
Strict pure growth now gives exactly \(F_j|_I=\bar F_j\)
in those grades. Every live row on which old \(F_j\)
vanishes is also point exact in the reversed tableau through
grade \(j\). The ghost-origin case is covered by the same
calculation; for example when \(\ell=5\), the model of
\(e_1\) with zero first five scalar moments and value one
at the origin is
\(1-30X+210X^2-560X^3+630X^4-252X^5\), not zero.

## Excluding at least three visible dirty clocks

Take \(k=3\). The visible pure grade-four space is
\(F_4|_I=d_I\,\mathcal P_{\le2}(c_I)\).
Since \(d^2\) belongs to it after restriction, a polynomial \(G\)
of degree at most two gives \(d_i=G(c_i)\) at every live dirty
row. All live clean rows (\(d_i=0\)) are point exact
through grade four in the old and live reversed charts.
The eight pure moments of \(bd\) imply exact \(G\)-weighted
quadrature on the live clean sites through degree seven.
The last physical row \(14\) is live and clean with clock 1.

If the pooled visible \(bd\) measure is nonzero, it has
at least nine distinct effective dirty clocks by Vandermonde.
There are at least four distinct live clean clocks, even if
the origin weight is zero: if there were at most three,
let \(Q\) vanish at the other at most two clean clocks
besides 1. The tests \((1-X)Q R\) would make the
nonzero polynomial \(GQ\) orthogonal to all polynomials
of its own degree under weight \(1-X\), a paid nonsingular
Beta matrix. Thus exactly one ghost and exactly nine
distinct live dirty and four distinct live clean rows occur.

If the four live clean clocks include zero, the
fixed-four Jacobi contact contradiction of the
[equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md)
applies in the **live reverse chart**.
When \(G\) is at most linear, this four-node weighted
quadrature itself is impossible by the anchored
\(X(1-X)\)-Gram test. For quadratic \(G\), the
weighted moment condition makes \(G\) times the two
interior clean factors the fixed quartic Jacobi polynomial.
The first exact live reverse clean unary with
\((1-C)(G(c)-d_I)\) then gives the forbidden endpoint or
interior contact. No old ghost row contributes, since
this is a true restricted reversed matrix. The vector
\(d_I\) in this probe is genuinely reverse pure grade two
by the low-degree equality just proved.

Otherwise the unique ghost is physical row 1, and
there is no live clean zero clock. The restriction map
on old \(F_4\) is injective (every pure profile vanishes
at the original origin), so \(F_4=d\mathcal P_{\le2}(c)\)
also before projection. Thus the old actual mask
\(T=G(c)-d\) has support only on the five original clean
physical rows (ghost origin and four live clean sites),
and the original forward first-boundary primitive
holds. The reverse last-boundary primitive holds by the
live reverse through grade four. The old \(G\)-weighted read
is exact through degree seven even with zero origin weight.
The old literal middle clean cut pays the mixed grade-nine
unary of \(C(C-u)T\) against \((C-v)(C-1)T\):
the product is zero by the same central-support argument.
These are exactly the five-clean hypotheses of the
[previous scalar closure](ERK10-UNBALANCED-CLEAN-FIVE-EXCLUSION.md);
that scalar proof does not require a nonzero origin quadrature
weight. If \(G\) is linear the separate clean-five linear
closure in the equality ledger applies, and a nonzero constant
is already ruled out by the first-boundary primitive.
Thus no nonzero pooled case survives.

If instead all visible dirty clocks have zero pooled
\(bd\)-mass, they also have zero ordinary mass,
since \(G(c_i)\ne0\) on a dirty clock.
There must be at least six distinct live clean ordinary
support clocks, by the degree-nine quadrature and the
anchored \((1-X)\)-Gram argument. Each visible dirty clock
needs at least two physical rows. With at least one
ghost there are therefore exactly **three** visible dirty
clocks. Now the actual reversed \(\bar F_4=F_4|_I\)
is the direct sum of their three indicator lines, C-invariant
and closed under coordinate multiplication, and
\(\dim \bar F_3=2\). The low-grade part of the
[native rank-three offcore lemma](../lean/RKCert/ReviewedNative/ERKGradeEightOffCore.lean)
says there are at most two offcore clocks: the incoming
reads of the indicator space at an offcore row kill
\(\bar F_3\) and are on one line. The first nonzero
offcore clock calibrates the line using the primitive of
\(X\); a first different nonzero offcore clock is then
impossible using \((X^2(X-u)^2)'\) at the preceding
offcore clocks 0 and \(u\). This argument only uses point
exactness through four there, not reverse order ten.
It contradicts the required six live clean clocks.

## Excluding exactly two visible dirty clocks by a one-row lift

Take \(k=2\). The exact live reverse has pure
\(\bar F_3\) of rank two, equal to \(d_I\mathcal P_{\le1}(c_I)\).
It is **C-invariant** because there are exactly two
numerical values supporting it. The old reverse row space
\(V_2=E_6^\perp\) is fully live, spanned by \(bd,bdC\).
The three-dimensional \(V_3=E_5^\perp\) contains it.
No premise that \(V_3\) is fully live is added.

Consider an arbitrary grade-four unary pair in the live
reverse. Its degree-three input has an old lift \(x\in E_3\)
with the reflected formal model \(P_x\), by the exact
low-grade lift just proved. For old \(z\in E_5\), its
paired unary deviation on \(z_I\) is
\[
    \langle \bar A x_I-(\bar J P_x)(c_I),z_I\rangle_{B_I}
                     =-\sum_{g\notin I}z_g\langle x,Ae_g\rangle_B.
\]
The exact old scalar parts cancel by paid integration by parts.
The right-side ghost functional annihilates \(Z\cap E_5\)
by the ghost-primitive identity with \(\ell=5\) for that
intersection (not with \(\ell=6\) for individual ghosts).
This intersection has codimension at most one in \(Z\),
because \(V_3\) already contains the fully live \(V_2\).

If \(V_3\) has a nonzero ghost restriction, choose \(q\in V_3\)
whose ghost block \(q_Z\) spans it. The ghost functional is
a scalar multiple of \(q_Z\), and \(q(z)=0\) for all
\(z\in E_5\) exchanges its response for the same scalar
multiple of \(q_I(z_I)\) on live coordinates. After subtracting
that live row, the remaining deviation annihilates \(E_5|_I\).
Every row annihilating \(E_5|_I\) extends by zero to a row
in \(V_3\), so its live restriction is in \(V_3|_I\).
The same conclusion with no extra row holds if \(V_3\)
is fully live. Thus **every** true reversed unary degree-four
pure deviation is in \(B_I^{-1}(V_3|_I)\).
Products of lower reverse pure and polynomial parts also
land there: they are restrictions of actual grade-four
old pure vectors, whose weighted rows annihilate \(E_5\).
Therefore \(\dim\bar F_4\le3\).

But by the reviewed
[clock-invariant outgoing Hermite gain](../lean/RKCert/ReviewedNative/ForwardNodalGain.lean),
a strict chart with polynomial separation through grade
three and a C-invariant pure \(F_3\) of rank two must have
\(\dim F_4\ge 2+\lfloor(3+1)/2\rfloor=4\).
This theorem needs separation **only through grade three**,
not reverse order ten or grade-four separation.
The contradiction completes the two-visible-clock exclusion.

## Further literal ghost guards

If there is exactly one ghost, and its coordinate is not
already pure in \(F_4\), then whenever the surviving
\(V_3\) is fully live one gets \(e_g\in E_5\).
If \(g\ne1\), its formal model is zero by anchored
degree-five moments, so it first enters the pure space at
grade five. If instead \(d\) is completely invisible and
there is exactly one ghost, it is physical row 2:
the first nonzero clock is necessarily defective, and
every earlier zero-clock incoming stage has the same
full rooted profile as the origin. Otherwise there would
already be a removable duplicate.

More generally if a ghost indicator \(e_g\) belongs to
\(F_j\), its actual evaluation functional on \(E_{j-1}\)
cannot be represented by a single fixed combination of
other physical evaluations **before its first actual
outgoing read**. Such a combination \(L\) would allow the
strict replacement \(A'=A+(Ae_g)(L-e_g^{\mathsf T})\).
The correction kills every early grade input by hypothesis;
on any higher input it is a multiple of \(Ae_g\), which
is genuinely pure of grade at most that input grade plus one.
Induction in the original stage algebra thus gives all new
pairs with the same formal models. Since \(b_g=0\) and
the altered column vanishes, the physical ghost is removable,
contrary to minimal 14. This uniform replacement does not
require the surrogate coordinates to precede the ghost itself,
only its first actual read.

[ERK10GhostFrontierGate.lean](../lean/RKCert/Research/ERK10GhostFrontierGate.lean)
checks the small exact scalar rank/tap/ghost-origin identities.
The proof reuses the native outgoing Hermite result and the
earlier scalar clock contradictions; the live projection and
rooted degree audit above are mathematical. Cases with no
visible dirty clock or with a single visible one remain.

The [single invisible-stage follow-up](ERK10-SINGLE-INVISIBLE-GHOST.md) studies the case with exactly one zero output weight and no visible quadratic defects. Its [two-clock closure atlas](ERK10-SINGLE-GHOST-TWO-CLOCK-CLOSURES.md) leaves a six-tap case, excluded by the [final crossover](ERK10-GHOST-TWO-CLOCK-CROSSOVER-EXCLUSION.md). Other outgoing clock counts and additional invisible stages remain separate.
