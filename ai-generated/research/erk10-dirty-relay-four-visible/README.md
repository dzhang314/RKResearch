# Four visible sites cannot finish the rational single dirty relay

Together with the
[double-unary obstruction](../erk10-dirty-relay-double-unary/README.md)
and the [origin-only scalar gate](../erk-origin-degree-nine-scalar-floor/README.md),
this rules out an entire **conditional construction architecture**
for rational ERK10 in 15 stages.
The architecture is six actual order-five rows and their actual FSAL,
one nonzero size-six ghost pure through derivative size five, a true
pure-through-size-six relay, a full nine-coordinate degree-four decoder,
and at most six additional rows using that exact decoder feed and an
arbitrary strict late-to-late block. It covers arbitrary rational
FSAL and relay horizons, signs and zero individual output weights.
It does **not** exclude other rational 15-stage ERK10 methods, even
those permitting two ghosts or weakening size-six purity in the late rows.

The purely structural part below also holds over a field with \(10!\)
nonzero, conditional on the old six-row true defect rank four and the
stated exact decoder. We use the rational rank-four theorem for a
rational opening. The final rational nodal parity steps are explicit
extra arithmetic hypotheses, not facts about arbitrary fields.

## Exact set-up

Use the notation of the linked double-unary packet:
\(Q=X(X-\xi)(X-w)\), \(E\) high evaluation, \(J\) primitive from 0,
\(B\) the late-to-late strict block padded with three zero rows and
columns at the early high stages, and \(L=EJ-BE\).
The actual prefix decoder \(\Pi\) pays every size-five source, evaluated
on all nine physical prefix rows. Its high aliases at \(0,\xi,w\) are
pure through size six. A late clock is **visible** if it is not one
of these three values. At each late row the old-to-late feed is
literally the corresponding row of \(L\Pi\). As in the linked
packet, actual order forces the five low nonorigin and the ghost
weights zero.

For \(j=0,1,2,3\) write \(\rho_j=(1-X^{j+1})/(j+1)\) and
\[
    \boldsymbol r_j=\boldsymbol b^\top C^jB
                    -\boldsymbol b^\top\rho_j(C).
\]
On late row coordinate space let \(N\) be the kernel of aggregation
over the **four distinct visible sites** (ignore invisible
coordinates entirely). There are at most six late rows, so
\(\dim N\le2\). Equal-clock aggregation also gives \(N C\subseteq N\).
Here and below membership of a high row in \(N\) means membership
of its late restriction. Multiplying a high row by \(B\) always
ignores all three early high coordinates and produces zero at them.

The true one-unary tests give \(r_j E(Q\mathcal P_{5-j})=0\);
the actual double-unary and double-unary-plus-leaf tests give
\(r_0 B E(Q\mathcal P_4)=0,\ r_1 B E(Q\mathcal P_3)=0\).
Because evaluations of \(Q\mathcal P_3\) span the visible
coordinate values, this means
\[
       r_0,\ r_1,\ r_2,\ r_0B,\ r_1B\ \in N.
\]
Lists with repeated or interleaved scalar sites have exactly the
same aggregate conclusion. These are marked ordinary rooted tests,
not assumed stage co-order.

## Two more actual rooted probes

Choose a source tree \(s\) of size \(k\le7\) among the same
selected sources: the size-six trees (all root children of size at
most five), or the size-seven bush. Their residuals span \(Q\mathcal P_3\).
Write \(h_j=H_{[s]^j}\) for the decoder residual after \(j\) unary
attachments, so \(h_0=H_s\). The sources selected this way have ideal
actual high profiles except the ghost, which is not read through \(B\).
The exact literal alias equalities say
\(h_{j+1}=Jh_j\) on \(0,\xi,w\). All error rows used below have a
zero coordinate at the ghost. The actual high error after one unary
attachment at weighted rows is \(-Lh_0\); repeating the operation
gives one more \(B\)-propagated term and one new decoder residual
with that same sign.

**Triple unary.** Its size is \(k+3\le10\), giving
\[
 \boldsymbol b^\top B^2 L h_0+
 \boldsymbol b^\top B L h_1+
 \boldsymbol b^\top Lh_2=0.
\]
Let \(\boldsymbol e=\boldsymbol r_0-\boldsymbol r_1+
\boldsymbol r_0B\), and use the upper primitive
\(J^*\rho_0=\rho_0-\rho_1=(1-X)^2/2\). Then
\(\boldsymbol b^\top B^2=\boldsymbol b^\top J^*\rho_0(C)+\boldsymbol e\).
Since \(r_0,e\) aggregate to zero on visible late sites,
and every \(h_{j+1}-Jh_j\) vanishes at the aliases,
their evaluations of that difference are zero.
In the triple-unary equality, replace \(h_2\) by \(Jh_1\) in
the \(-r_0 E h_2\) term and cancel \(r_0 E Jh_1\) from the
preceding \(bB L h_1\) term.
Integration by parts on the remaining ideal \(b\rho_0(C) E Jh_1\)
leaves \(-e E h_1\); cancel that against \(e EJh_0\) in
\(bB^2Lh_0\), using \(e E(h_1-Jh_0)=0\).
Thus
\[
       \boldsymbol b^\top B^3 E h_0
        =\boldsymbol b^\top (J^*\rho_0)(C)EJh_0 .
\]
Every integrand used has degree at most \(k+2\le9\):
\(\rho_0\) has degree one, \(J^*\rho_0\) degree two, and the
largest relevant primitives have degrees \(k+1\) or \(k\).
Since \(J^*\rho_0=1/2-X+X^2/2\), expanding another \(B\)
in the ideal part leaves the already paid combination
\(r_0/2-r_1+r_2/2\) under a second integration by parts.
It follows \(e B E h_0=0\).
Subtract the already paid \(r_0B-r_1B\) and obtain \(r_0B^2\in N\).

**Unary, leaf, unary.** First attach a unary root to \(s\),
then an extra leaf at that root, then an outer unary root.
Its size is again \(k+3\le10\).
The interior leaf multiplies the actual error by \(C\).
If \(h'\) is the residual of the interior marked tree, its
alias values are \(XJh_0\) because at those true rows the leaf
multiplies by the actual scalar clock.
The rooted output identity is
\[
   \boldsymbol b^\top B C L h_0+\boldsymbol b^\top Lh'=0.
\]
Replace \(-r_0 E h'\) by \(-r_0 C E Jh_0\), by the alias
values and visible aggregate zero. The cancellation leaves
\(\boldsymbol b^\top B C B E h_0
  =\boldsymbol b^\top\rho_0(C) C E J h_0\).
Use \(J^*(X\rho_0)=\rho_1-\rho_2\).
Expanding the true left side gives the ideal
\(\boldsymbol b^\top(\rho_1-\rho_2)(C)\) plus \(r_1-r_2+r_0CB\).
The first two errors are already paid on \(h_0\) and the
degrees remain at most \(k+2\le9\).
This gives \(r_0CB\in N\).

## Exhaustive structural exit

If the late restriction \(r_0=0\), there is full literal first
co-order on the late columns. At least one late weight is nonzero
(otherwise at most the three aliases contribute and scalar degree
nine is impossible). At the latest live late coordinate, strict
causality gives zero incoming reverse coefficient, so its clock
is 1. This exit forces endpoint 1 in the possible support.

Suppose \(r_0\ne0\). If \(r_0B\ne0\), it cannot be a scalar
multiple of \(r_0\), since a nonzero eigenvalue of a nilpotent
strict matrix is impossible. Hence \(r_0,r_0B\) span \(N\),
and \(r_0B^2\in N\) makes \(N\) invariant under right
multiplication by \(B\). If \(r_0B=0\) but \(r_0C\) is
independent of \(r_0\), the same conclusion follows using the
basis \(r_0,r_0C\) and \(r_0CB\in N\).
These alternatives include every case of two independent
vectors in the at-most-two-dimensional \(N\); in dimension one
only the dependent alternatives can occur.

If \(N B\subseteq N\), every invisible row has zero
aggregate tap into each visible site (its coordinate row belongs
to \(N\)); every two rows at a common visible clock have
the same visible aggregate taps (their difference belongs to \(N\)).
Use the first physical occurrence of each visible clock as its
representative. The resulting visible aggregate block is strict
in that chronological order: a later first occurrence cannot
be read by an earlier representative, including its own label
by strictness. The exact aggregate first and second co-order
equations descend to this block, with all invisible contributions
zero. Among its nonzero aggregate weights the latest must be at
1; the latest non-1 cannot exist since it would see only clock 1
in its two exact reverse equations. Thus at most one visible
site contributes and the entire scalar support has at most four
live sites including aliases. This contradicts degree nine.
Over any field paying \(10!\) this follows without positivity:
the order-four Hankel matrix with entries \(1/(i+j+1)\),
\(0\le i,j\le4\), has determinant \(1/266716800000\), a paid
nonzero scalar; any rule on at most four sites has rank at most
four. The analogous 3 by 3 determinant \(1/2160\) justifies
the earlier two-site precision-four exclusion over such fields.

It remains \(r_0B=0\) and \(r_0 C\) a scalar multiple of \(r_0\).
Its nonzero entries all have the same stage clock \(v\)
because \(C\) is diagonal. Take the chronologically latest
nonzero entry, at row \(i\).
If \(v\) is visible, those entries sum to zero by \(r_0\in N\),
so \(r_0B=0\) and the equal-clock decoder feed give a zero
affine combination of the actual incoming rows at \(v\).
If \(v\) is invisible, the same B relation makes their weighted
incoming rows equal to their coefficient sum times \(J_v\Pi\).
That is the literal earlier pure row at the alias \(v\)
(origin if \(v=0\)). Move this alias to the other side.
In either case row \(i\) is an affine combination of earlier
physical incoming rows, all at its own clock. All signs are
permitted; the coefficient at \(i\) is nonzero, the only
division needed. It is irrelevant how other clocks interleave
the related rows.

This affine relation between incoming rows is also an affine
relation between their true stage derivatives through order ten:
each affected row is locally pure through size six at \(v\);
all immediate children of size at most five have the same
primitive there, and at most one larger child can occur in a
tree of size at most ten. Any exceptional factor depends
linearly on the incoming row; multiplication by the other
common factors preserves the affine relation.
Thus delete row \(i\), redirect its taps to the earlier
combination and transfer its output weight accordingly.
The resultant strict tableau preserves all ordinary rooted
outputs through order ten by chronological row induction and
the root product formula. It remains the exact same decoder
chart: evaluations of same-clock late replacements are equal;
when a replacement is an earlier alias, the loss of that
clock tap from late \(B\) adds precisely its literal
coordinate feed \(E_v\Pi\) to the old part. No old
prefix row or its decoder is modified.

The deletion preserves all four visible scalar labels and
reduces the number of late physical rows. Repeat the argument.
Eventually either the invariant-block contradiction applies
or \(r_0=0\) forces endpoint 1. A zero-dimensional aggregate
kernel already has \(r_0=0\).

## Final rationality gates

With four visible sites the possible scalar support has at
most seven sites: the visible set plus \(0,\xi,w\). In the
only surviving structural exit it contains 1, so the
[anchored degree-nine scalar floor](../rational-endpoint-moment-nine/README.md)
contradicts it over \(\mathbb Q\). No endpoint weight is
required to be nonzero. The direct necessary scalar nodal
equations in the four-visible case are
\(\int_0^1 X^j QF=0\) for \(0\le j\le2\), where \(F\)
is the degree-four visible site hull; the arithmetic lower
bound rejects them when the forced endpoint is added.
If there are at most three visible sites, then at most six
possible scalar sites contain origin 0 and the
[origin-only parity gate](../erk-origin-degree-nine-scalar-floor/README.md)
already rejects them, without forcing endpoint 1.
Five or six visible sites were excluded in the linked
double-unary packet. Together the cases complete the
conditional rational architecture, not an unrestricted
bound on physical stage count.

The scalar modular receipts and literal seed/minor each have
their own Lean certificates or exact replays in the linked
packets. This additional triple-unary structural and affine
contraction argument is mathematical and is not claimed as
one native tableau theorem.
