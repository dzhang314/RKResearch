# Every sole invisible ERK10 ghost has original cubic pure rank two

Work over any characteristic-zero field. Assume a literal 14-stage
strict explicit order-ten tableau with exactly one zero output
coefficient, and that its original quadratic defect is invisible.
Use the [single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md):
the ghost is physical 2, \(e=e_2\) is pure of grade two,
\(r=Ae\) is real original pure grade three, and \(u\) is the
quadratic seed on the thirteen live rows of the genuine reduced
weighted transpose. Write \(f_j=\dim F_j\).

**Result:** \(f_3=2\). This does not rule out rank two or
change the unrestricted 14–15 stage interval. The new case
here is one reverse active clock and \(r,u\) independent.
The other clocks/linear-dependence forks are tracked below.

## 1. All but the independent one-clock case

Suppose \(f_3=3\). Strict forward growth into \(f_5=5\)
then gives \(f_4=4\). The original \(F_3\) projection onto
live rows equals the exact rank-two paid dual room \(W_2\):
it is contained there by orthogonality with \(E_6\), and
only the line \(Ke_2\) is lost. Each projected direction
has a true original pure grade-three lift with ghost value zero,
obtained by subtracting its own ghost coordinate times \(e_2\).
The same calculation in grade four gives \(F_4|_I=W_3\).
Therefore the projected directions under discussion all
vanish at physical origin 1 and terminal 14, where old
grade-four point exactness is paid.

If \(u\) has three or more active clocks, the
[rank-four multiclock theorem](ERK10-INVISIBLE-GHOST-RANK-FOUR-MULTICLOCK-EXCLUSION.md)
has just excluded it. If \(u\) has exactly two, then
\(W_2=\langle u,Cu\rangle\) is clock-invariant, since the
two clock powers isolate the two active blocks.
If \(C W_2\subset W_2\), the original \(F_3\) is also
clock-invariant: the aligned ghost-zero lift is stable on
the live rows and \(e_2\) is a clock eigenvector. The
actual original outgoing Hermite bound at grade three would
then give \(f_4\ge f_3+2=5\), contradiction. This argument
also excludes any invariant \(W_2\) in what follows.

If \(u\) is active at one clock and proportional to \(r_I\),
the actual \(r\) support is the same single clock and includes
physical 13, since the true reverse quadratic seed is nonzero
there. The previously checked
[dependent last-thirteen rank exit](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-RANK-THREE-EXCLUSION.md)
excludes \(f_3=3\) in that chart. It is the independent
single-clock fork that remains.

## 2. The exact terminal kernel with one carrier block

Suppose \(u\) is supported at one clock \(\theta\), and
\(u,r_I\) are independent. On the live rows \(W_2=\langle u,r\rangle\).
The action of \(C\) descends to the quotient by \(Ku\) because
\(Cu=\theta u\). Count the distinct clock eigenspaces on
which the image of \(r\) has nonzero component in this quotient.
Equivalently it counts each different clock \(x\ne\theta\)
on the support of \(r\) and, additionally, \(\theta\) when
its \(r\)-block is not proportional to \(u\).
On distinct such labels its successive clock powers attain
exactly their Vandermonde rank.

If the count were one, \(W_2\) would be clock-invariant,
already impossible. So \(W_3=\langle u,r,Cr\rangle\), and
the general non-invariance of the paid linear \(W_3\)
in the [single-ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md)
makes the quotient count at least three. The original
\(F_5\) is then exactly \(Ke_2+\langle u,r,Cr,C^2r\rangle\)
using genuine old lifts, since its rank is five. If the count
were three, this \(F_5\) itself would be invariant; the old
grade-five outgoing Hermite bound would force \(f_6\ge8\).
The exact rank is \(f_6=7\), so the quotient count is at
least four.

The universal terminal evaluation argument from the
[rank-four multiclock proof](ERK10-INVISIBLE-GHOST-RANK-FOUR-MULTICLOCK-EXCLUSION.md#4-nonzero-pooled-defect-with-constant-l)
shows \(\ker(\mathrm{ev}_{14}\mid F_6)\) has rank six.
Specifically the actual \(e_{14}\) is grade five, and its
zero numerical advance has model \(JP_{e_{14}}\) with
value \(b_{14}\ne0\) at 1. Subtracting the clock model
gives the nonzero terminal pure value.
The six vectors
\[
                    e_2,\quad u,\quad r,\ Cr,\ C^2r,\ C^3r
\]
are genuine old grade-six pure terminal-zero vectors
(\(u\) is its paid original grade-three lift here, not a
free function on the live set), and independent by the
four quotient clock labels and the ghost marker.
Thus they **fill** the terminal kernel.

In particular \(r^2,u^2\) are actual original pure grade-six
vectors, both zero at the terminal. The first has a live
representation \(r^2=\beta u+r R(c)\) for \(\deg R\le3\).
At every **noncarrier** (\(u_i=0\)) with \(r_i\ne0\)
this is the literal amplitude equality \(r_i=R(c_i)\).

## 3. The carrier amplitudes and exact support contradiction

There are at least three off-\(\theta\) distinct active \(r\)
labels by the quotient count. Suppose there are exactly three.
Then all \(r\) support, including the carrier clock, uses at
most four labels, so its seven paid \(br\) moments force
every pooled \(br\) mass zero. At each of the three
off-\(\theta\) labels the nonzero \(r\)-amplitude is uniform by
§2. Each such group requires at least two physical rows and
has zero ordinary mass, saving at least six ordinary support
sites in total. The \(u\)-carrier rows are disjoint from these
groups. They have \(bu=bu^2=0\) by the actual dual row
and the paid original lift. They need at least two live rows;
if there are exactly two, these identities force uniform
\(u\) and opposing weights, so they cancel ordinary mass.
If there are three or more they compress to at most one
ordinary support site at their one clock. Either way they
save at least two more sites. This leaves at most
\(13-6-2=5\) ordinary sites, contradicting the anchored six-site
floor. Therefore at least four distinct off-\(\theta\)
\(r\)-active sites occur.

Now represent the other actual square \(u^2\) in the same
terminal kernel. Its \(r\)-polynomial factor, degree at most
three, has a zero at every off-\(\theta\) active \(r\) label.
It is identically zero, so \(u_i=\rho\ne0\) is uniform on
all \(u\)-carriers. Their ordinary weights sum to zero.
Let \(m\) be their number. Both endpoints have \(r=u=0\).
If \(m\ge4\), there are at most \(11-m\le7\) active
noncarrier rows. The noncarrier \(br\) moments still vanish:
the carrier \(br\) sum is zero by \(bu\) against \(r\), and
their clock is fixed. Thus noncarrier pooled \(br=0\)
in this count. Every active noncarrier label requires at
least two live rows, since its amplitude is the common
nonzero \(R(x)\). The four distinct off-\(\theta\) labels
therefore need eight rows, contradiction. Thus \(2\le m\le3\).

The three true tests of \(bu\) against \(1,r,r^2\)
now make the weight sum zero in each \(r\)-amplitude group
on the carriers, including a possible zero group.
There can be only one such group, since any group with zero
weight sum needs two physical rows. Hence carrier \(r\) is one
uniform value \(\eta\).
If pooled noncarrier \(br\) were zero, its at least four
uniform active groups would all cancel ordinary weight.
Together with the carriers this would lose at least ten
ordinary physical sites, too many. The noncarrier pool is
therefore nonzero and needs at least eight active labels.

## 4. Removing the carrier from the genuine cubic mask

There are thirteen live rows and at least two carriers
and eight noncarrier active rows. Thus there are at most
three noncarrier dormant physical rows, including 1 and 14.
The ordinary scalar \(R\)-weighted quadrature through degree
six lies on those dormant sites: \(r=R(c)\) at all active
noncarriers, while carrier ordinary masses and \(br\)-masses
sum to zero in their fixed clock block.
If only the two endpoint sites occur, the anchored Gram
excludes \(R\ne0\). Otherwise the one extra dormant row
has an interior clock \(w\) and
\((X-w)R\) is the fixed Lobatto quartic up to scale.
These are the same two scalar alternatives of the
[paid cubic-response seam](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md#2-a-paid-scalar-and-causal-lemma-when-the-literal-response-is-cubic).

For the middle witness here use the actual original
grade-three vector
\[
 T=R(c)-r-\frac{R(\theta)-\eta}{\rho}\,u-R(c_2)e_2 .
\]
It vanishes at the ghost, at all carriers and at all active
noncarriers; its formal model is \(R\). At the endpoints
and the at most one middle dormant site it is literally
\(R(c)\). Multiplying by \(C\) and \(1-C\) yields the
same strictly causal product
\((A(CT))((1-C)T)=0\), of total grade nine.
Its formal integral at \(R\propto L_4/(X-w)\) is instead
nonzero by the checked middle-seam Bézout certificate.
This contradiction excludes the independent one-clock case.

All cases of \(f_3=3\) have been exhausted.
The reviewed strict growth lower bound gives \(f_3\ge2\),
so \(f_3=2\) for any remaining sole invisible ghost candidate.

[ERK10InvisibleCubicRankGate.lean](../lean/RKCert/ReviewedNative/ERK10InvisibleCubicRankGate.lean)
checks the two actual square-profile implications, the
carrier mask value identity, and the physical count leaves.
The old rank lifts, support and exact rooted cuts are the
mathematical derivation above.
