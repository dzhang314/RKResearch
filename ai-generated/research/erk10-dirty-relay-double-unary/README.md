# Double-unary order tests rule out five or more visible late sites of a single dirty relay

This is a mathematical obstruction to a specific rational explicit
order-ten architecture, not a general ERK10 lower bound. It permits
arbitrary rational FSAL and relay clocks \(\xi,w\) with
\(0,\xi,w\) distinct, signed output weights and late zero weights.
It replaces the fixed-horizon resultant tests by actual additional
rooted identities whenever there are at least five distinct visible
late clocks. No assumption of signed reverse co-order is imposed.

## The physical decoder architecture and its actual source space

Use any six rational strict rows giving actual ordinary order five
at horizon \(\xi\ne0\). Append its actual FSAL at \(\xi\), one ghost
at a nonzero clock \(z\) pure through derivative size five but not
six, and a true pure-through-size-six relay at \(w\). Suppose the
nine actual profile coordinates through size five span all nine
physical coordinates and have a literal exact degree-four decoder
\(\Pi\). These are realized by the
[literal dirty relay](../erk10-dirty-sixth-relay/README.md); this
argument uses the stated rank and local purity, not its numbers.

Append at most six further strict physical rows. Let \(B\) be the
actual late-to-late matrix padded by zero at the three early high
coordinates (FSAL, ghost, relay). Let \(E\) evaluate polynomials on
all high clocks. Each late-row low-to-high feed is literally
\[
        L\Pi,\qquad L=EJ-BE,
\]
where \(J\) integrates polynomials from zero. Its other coefficients
are \(B\). The FSAL and relay rows themselves equal
\(J_\xi\Pi,J_w\Pi\) as literal rows: exact through-size-six
primitives agree there on the full nine-coordinate size-five span.
Similarly evaluation of \(\Pi\) at 0, \(\xi,w\) gives the corresponding
physical coordinate rows. The decoder's feed restores local purity
through derivative size six in every late row by chronology.

On the six low rows the [rank-four theorem](../erk10-rank-three-port-one-label/README.md)
gives actual \(F_5=\ker\boldsymbol b_{\rm low}^\top\cap\ker E_o\),
with \(E_o\) the physical origin coordinate. If the marked covector
\(\boldsymbol b_{\rm low}^\top C_{\rm low}\) killed that space,
it would be a linear combination of those two covectors; then all
nonorigin nonzero low output weights would have the same clock,
impossible by scalar precision four. Thus one true marked pure
direction \(C_{\rm low}\boldsymbol u\), \(\boldsymbol u\in F_5\),
adds the fifth low nonorigin axis through size six. It is zero on all
high rows, including the ghost, since marking multiplies the actual
through-size-five difference by the actual clock there.
A genuine through-size-six ghost discrepancy gives the sixth pure
axis. All other high rows are pure through six. Consequently actual
order ten forces zero output weight on the five low nonorigin rows
and on the ghost. We use only the resulting origin/high support.

For a tree \(s\) let
\(g_s(X)=|s|X^{|s|-1}/\gamma(s)\) and
\(H_s=g_s-\Pi\boldsymbol\Phi_s^{\rm old}\).
Through size six, the joint actual-profile and nominal-model space
has rank \(6+6=12\): the pure directions have rank six, while the
six bushes independently span the nominal model. The decoder already
eliminates all residuals through size five and its actual side has
rank nine by hypothesis. Thus the size-six residual model span
has rank three. It equals \(Q\mathcal P_2\), where
\(Q=X(X-\xi)(X-w)\), by the three pure coordinate values and the
degree-five limit. All size-six trees have immediate children of
size at most five. Adding the three bushes of sizes seven to nine,
whose residuals have degrees six to eight and nonzero leading
coefficients, gives \(Q\mathcal P_3,Q\mathcal P_4,Q\mathcal P_5\)
through those respective source sizes. Every selected source
has immediate children of size at most five, so its whole high
profile is nominal except possibly at the ghost, which \(B\) never
reads and the output never weights.

## Actual one- and two-unary probes

Let \(C\) be the high clock diagonal, and let
\(\rho_j(X)=(1-X^{j+1})/(j+1)\).
Define the raw high reverse residual
\[
       \boldsymbol r_j=\boldsymbol b^\top C^j B-
                         \boldsymbol b^\top\rho_j(C).
\]
Origin output may be left outside the high sums because all the
polynomial probes and primitives below vanish at zero.
The true \([s]\) root with \(j\) extra leaves has size \(|s|+1+j\)
and differs at weighted high rows from its ideal by
\(-\boldsymbol b^\top C^j L H_s\); this is the literal leaf mark
multiplication, valid also at the two early pure aliases.
Integration by parts and scalar precision nine give
\[
 \boldsymbol b^\top C^j L f=-\boldsymbol r_j E f
\]
when \(f(0)=0,\deg f\le8-j\). Indeed both \(X^j Jf\) and
\(\rho_j f\) have degree at most nine and their integrals agree.
No take-up at the ghost is involved. Thus actual order ten forces
\(\boldsymbol r_j E(Q\mathcal P_{5-j})=0\) for each \(j=0,1,2,3\).

Call a late clock **visible** if not one of \(0,\xi,w\).
When there are five distinct visible sites, \(r_0,r_1\) have zero
aggregate at each by Vandermonde: evaluations of \(Q\mathcal P_4\)
separate all five because \(Q\) is nonzero there.
At the aliases themselves the next residual is exactly
\[
    H_{[s]}(0)=0,\qquad
    H_{[s]}(\xi)=JH_s(\xi),\qquad
    H_{[s]}(w)=JH_s(w).
\]
To see this, at FSAL or relay the incoming row is literally the
integrated decoder. Subtracting the actual unary primitive from
its exact model gives \(JH_s\) at that alias.
This also covers an appended collision with any alias, since the
polynomial \(H_{[s]}\) is evaluated there at the same clock.
The raw residual at the ghost is zero because both its \(B\) column
and its output weight are zero.

For source \(|s|\le8-j\), attach two unary edges, then \(j\) leaves
to the outer root, with \(j=0,1\). The actual budget is at most
\(|s|+2+j\le10\). Propagating the first unary error through the
literal \(B\), then including the second source, gives
\[
  \boldsymbol b^\top C^j B L H_s+
            \boldsymbol b^\top C^j L H_{[s]}=0.
\]
At visible sites \(r_j\) has zero aggregate; at the aliases the
preceding equalities apply. Consequently
\(\boldsymbol r_j E(H_{[s]}-JH_s)=0\).
Both polynomial reads lie within the integration degree budget,
so substituting \(L=EJ-BE\) and cancelling the common term
\(\boldsymbol r_j E JH_s\) yields
\[
        \boldsymbol b^\top C^j B^2 E H_s
              =\boldsymbol b^\top\rho_j(C)E JH_s.
\]
The total degree on the right is at most \(j+1+|s|\le9\).
A second integration by parts uses the exact upper primitive
\(J^*\rho_j=(\rho_0-\rho_{j+1})/(j+1)\). Expanding the left,
\[
 \boldsymbol b^\top C^j B^2
 =\boldsymbol b^\top J^*\rho_j(C)
  +(\boldsymbol r_0-\boldsymbol r_{j+1})/(j+1)
  +\boldsymbol r_jB.
\]
The two error terms in the middle are already paid by the single
unary marked tests on \(H_s\). As the available sources span
\(Q\mathcal P_{4-j}\), the new actual identities are
\[
       \boxed{\ \boldsymbol r_0 B E(Q\mathcal P_4)=0,\qquad
                \boldsymbol r_1 B E(Q\mathcal P_3)=0.\ }
\]

## Six distinct visible slots

For six distinct visible slots, \(r_0\) is literally zero on late
columns by its six-dimensional single test. Thus the latest live
late slot must have clock 1, where \(r_1\) is already zero.
The five-dimensional single test now kills \(r_1\) at every other
late coordinate. No condition on whether the final physical row
is live is needed. There must be some nonzero late weight away
from 1: otherwise the scalar rule is supported at most on
\(0,\xi,w,1\), which cannot integrate degree nine (the square
of their hull has degree at most eight and positive integral).
At the latest non-1 live column \(x\), all later live taps are
at clock 1 and the two literal reverse equations give
\((1-x)b_x=(1-x^2)b_x/2\), a contradiction.

## Five visible slots plus one invisible collision

First suppose the only additional late slot is an invisible clock
\(v\in\{0,\xi,w\}\). The errors \(r_0,r_1\) at late columns are
supported only on this one physical coordinate; call their entries
\(\delta_0,\delta_1\). If \(\delta_0\ne0\), the first double-unary
identity makes the entire \(v\) row zero on all visible columns.
Then the reverse equations at visible columns receive no weighted
tap from \(v\), and the latest visible live column must have clock
1. The latest visible interior live column contradicts its exact
second reverse equation as before. Such an interior is necessary
since otherwise there are at most four live scalar sites, even
allowing the invisible output.

If \(v=1\), the same latest-interior contradiction applies directly:
at its latest live non-1 column \(r_0,r_1\) are both zero and all
later live clocks are 1. Now suppose \(\delta_0=0,v\ne1\).
Full late first co-order forces the latest late live clock to be 1.
A latest non-1 live column cannot be visible since it would also
pay the second co-order. It must be the invisible \(v\), before
a later visible live clock 1. If \(\delta_1\ne0\), the second
double-unary identity implies the \(v\)-row taps on visible sites
annihilate \(Q\mathcal P_3\). The annihilator is a single cofactor
line, nonzero in every coordinate of a nonzero vector. By strictness
the \(v\) row's tap into the later visible clock 1 is zero, so the
whole line multiple vanishes. This again decouples all visible
columns and gives the earlier contradiction. If \(\delta_1=0\),
both late co-order equations are literal and the latest interior
contradiction is immediate. This proof permits every chronological
placement and does not assume \(v\) is last or its weight is nonzero.

## Five visible sites, one repeated

Otherwise the only extra late slot repeats one visible clock \(v\).
Write \(i<i'\) for its two positions. The late parts of \(r_0,r_1\)
are opposite at those two positions and zero elsewhere.
If the late part of \(r_0\) is nonzero, the first double-unary
identity says rows \(i,i'\) of \(B\) agree in every visible
aggregate. At their own clock \(v\) that forces the only possible
internal tap \(B_{i',i}\) to be zero. Every other site is a singleton,
so the two full \(B\) rows agree. At the same clock their decoder
feeds also agree, giving literal duplicate stages. Merge them into
the earlier row (redirect taps and add their output weights).
The decoder chart is preserved because the two evaluations have
the same clock. The resulting five distinct visible late rows
are impossible by the same single tests, which now individually
force both reverse equations on all five.

If the late part of \(r_0\) is zero, the latest live clock is 1.
When \(v=1\), every non-1 late column pays both equations,
so the latest interior contradiction holds.
If \(v\ne1\) and the late part of \(r_1\) is nonzero, its entry
at \(i'\) is nonzero. There must then be a later live singleton:
if \(b_{i'}=0\), the nonzero entry itself requires a later weighted
tap; if \(b_{i'}\ne0\), the exact first equation at \(i'\) and
\(v\ne1\) require one. Therefore the difference of the two \(B\)
rows has a zero coordinate at a later visible singleton.
The second double-unary identity places its aggregate in the
same all-nonzero cofactor line; it is zero, so the rows duplicate
as above. If both late errors vanish, the latest interior argument
is immediate.

Thus there can be **at most four distinct visible late sites**
in this architecture. There are at most seven possible scalar
sites after adding \(0,\xi,w\); in particular if the endpoint 1
is in that possible support, the
[anchored degree-nine obstruction](../rational-endpoint-moment-nine/README.md)
excludes the entire architecture. This includes any horizon with
\(\xi=1\) or \(w=1\), without requiring the endpoint weight to be
nonzero. If endpoint 1 is absent and there are two or more late
collisions/repeats, the present proof does not settle the case.

The literal residual coefficient gate for the example and the
latest scalar equality are already checked in
[Lean for the distinct case](../erk10-dirty-sixth-distinct-tail/README.md).
The additional literal double-unary argument above is mathematical,
not claimed as a new kernel theorem.
