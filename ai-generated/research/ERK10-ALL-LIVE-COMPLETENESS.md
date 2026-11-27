# Completeness ledger: all-live 14-stage ERK order ten

**Theorem (conditional on all output weights live).** A strictly
explicit 14-stage RK tableau of rooted order ten over a
characteristic-zero field cannot have every \(b_i\ne0\).
This is an atlas proof, not a single native theorem stated on RK
tableaux. Individual algebra gates are checked in Lean; the rooted
and support reductions are the mathematical arguments in the linked
proofs. The known unrestricted interval remains **14–15**, because
zero weights are allowed there. This ledger covers no such zero-weight
cases.

## 1. Initial forks are exhaustive

The [equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md) starts with
arbitrary 14-stage rooted order ten and gives \(E_5\) rank 11,
\(F_5\) rank 5, \(bA=b(1-C)\), a live last weight, and an exact
grade-four last stage. In the all-live scope, the \(b\)-pairing
is nondegenerate and the actual weighted transpose is again rooted
order ten. In particular the pure rank-two/three/four spaces
in both orientations have dimensions 1/2/3; the quadratic
defect \(d=Ac-c^2/2\) is nonzero. Split on independence of
\(d,Cd\). No sign/nonnegative-weight assumption is made.

1. **Independent \(d,Cd\).** The independent fork of the [equality
   ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md#independent-quadratic-defect-the-two-clean-boundary-primitives)
   proves an exactly quadratic profile on dirty stages and splits
   on its pooled dirty measure. If zero, exactly four opposing
   dirty pairs and six true clean Lobatto rows occur. The
   [physical 7|7 reduction](ERK10-BALANCED-SEVEN-SEVEN.md)
   and [24-order exact seam exclusion](ERK10-BALANCED-SEAM-EXCLUSION.md)
   exhaust them over characteristic zero. If nonzero, exactly
   nine distinct dirty stages and five distinct clean stages occur.
   This is entirely excluded by the [unbalanced clean-five
   proof](ERK10-UNBALANCED-CLEAN-FIVE-EXCLUSION.md), including its
   special centered cases. Neither branch needs a comparison of
   grade-five original and reversed models beyond what it proves.
2. **Dependent \(d,Cd\).** Here \(Cd=\theta d\). Both literal
   shifted-nine taps are live, so rows 2 and 13 are carriers
   at their common clock \(\theta\ne0,1\); in particular there are
   at least two carriers. If nonzero defect amplitudes differ,
   [the nonconstant-amplitude exclusion](ERK10-NONCONSTANT-AMPLITUDE-EXCLUSION.md)
   exhausts this whole fork over characteristic zero.
   Otherwise rescale to the carrier indicator \(s\), put
   \(r=As\), and use the constant-amplitude census below.

## 2. Constant-amplitude carrier count

Write \(m\) for the number of carriers and \(n,\ell\) for the
number of noncarrier \(r\)-active rows and their distinct clocks.
The physical endpoints are \(r\)-inactive.
The [local entrance and low-label exclusion](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md)
first forces \(\ell\ge2\); the [four-carrier
census](ERK10-DEPENDENT-R-PAIR-PROFILE.md) proves if \(m\ge4\)
then \(\ell\le2\).
The two-label exclusion then eliminates every \(\ell=2\)
presentation at any \(m\), including its same-carrier-clock,
uniform pair, and triple cases. Thus \(\ell\ge3\) and
\(m\in\{2,3\}\). The [three-carrier exclusion](ERK10-THREE-CARRIER-EXCLUSION.md)
eliminates \(m=3\) in **both** cases of the pooled \(br\) measure.
When \(m=2\), the two carriers are exactly physical 2 and 13
and their ordinary pooled weights cancel. Their \(r\)-values
are zero, as are those of physical 1 and 14.

## 3. Two carriers, pooled \(br=0\)

Each active clock must have at least two physical rows. Hence
\(\ell\le5\). For \(\ell\le4\) the four paid \(br^2\)
moments force its pooled measure zero too. Every two-row group
then has zero ordinary pooled mass. The ordinary scalar support
is at most \(12-2\ell\), so requires \(\ell\le3\) by the paid
degree-nine support floor of six, using both physical anchors.
With \(\ell=3\), equality in the support bound forces every
group to have size 2 or 3. A single nonuniform triple is
impossible by its sole nonzero cubic charge, and three
triples are excluded by the [cubic Jacobi contact](ERK10-DEPENDENT-TWO-LABEL-EXCLUSION.md#two-carrier-ledger-beyond-the-two-label-branch).
The other possibilities are:
* \((2,2,2)\): [three-pair hyperplane exclusion](ERK10-THREE-PAIR-HYPERPLANE-EXCLUSION.md).
* \((2,3,3)\): [actual doubled-entrance exclusion](ERK10-DOUBLED-ENTRANCE-TRIPLET-EXCLUSION.md),
  using the [two-triple census](ERK10-TWO-TRIPLE-FRONTIER.md).
* \(\ell=5\) separately forces ten rows in five pairs,
  each with unequal nonzero amplitudes and nonzero ordinary
  pooled mass by the five-site \(br^2\) moment kernel.
  The actual repeat pairs 4/5 and 10/11 lie in opposite
  physical halves. Each physical half has five active rows,
  so the number of crossing pairs is odd and at most three.
  The [one-crossing](ERK10-FIVE-PAIR-ONE-CROSSING-EXCLUSION.md)
  and [three-crossing](ERK10-FIVE-PAIR-THREE-CROSSING-EXCLUSION.md)
  proofs exhaust it in characteristic zero.
There is no unlisted \(\ell=4\) or alternative \(\ell=5\)
multiplicity.

## 4. Two carriers, pooled \(br\ne0\)

The [Vandermonde and one-pole census](ERK10-THREE-CARRIER-EXCLUSION.md#three-carriers-close-exact-surviving-two-carrier-census)
starts with \(8\le\ell\le n\le10\) and excludes
\((\ell,n)=(8,9)\) and \((9,9)\), including possible
endpoint overlap at the one dormant row. The four remaining
cardinalities are exhaustive:
* \((8,8)\): both dormant rows are forced to be physical 5
  and 10 by the [fifth-head contact](ERK10-FIFTH-HEAD-CONTACT.md).
  The same note closes their common-clock case. The
  [distinct-dormant seam exclusion](ERK10-DISTINCT-DORMANT-SEAM-EXCLUSION.md)
  closes the different-clock case, including its endpoint and
  finite pivots.
* \((9,10)\) and \((10,10)\): two distinct adjacent repeat
  groups are compulsory by the [fifth-head
  contact](ERK10-FIFTH-HEAD-CONTACT.md#counts-and-the-separate-shared-clock-exclusion);
  if they shared a clock, they would lose even more than two
  numerical labels. Either way ten active stages cannot
  have nine or ten distinct labels.
* \((8,10)\): the two adjacent groups are exactly the two
  distinct repeats, each with unequal nonzero amplitudes.
  The [two-active-pair reconstruction](ERK10-FORCED-TWO-ACTIVE-PAIR-SEAMS.md)
  gives the degree-at-most-three nonzero \(br\)-weighted mean.
  An anchored Gram excludes degree zero. The [linear-mean
  and endpoint exits](ERK10-FORCED-TWO-PAIR-FINITE-EXITS.md)
  exclude all endpoint repeats and the degree-one mean;
  the [quadratic-mean exclusion](ERK10-QUADRATIC-MEAN-EXCLUSION.md)
  handles degree two with all finite/infinite residue cases
  accounted for. Finally the [cubic endpoint
  exit](ERK10-CUBIC-MEAN-ENDPOINT-EXIT.md) makes both endpoint
  mean values nonzero, so the [three mixed-moment
  contradiction](ERK10-CUBIC-MEAN-CROSSOVER-EXCLUSION.md)
  closes the remaining cubic over characteristic zero.

Every initial fork, carrier count, padded multiplicity, and choice
of endpoint/degree is covered within the all-live scope. No rank or
pivot exception is discarded beyond what the linked exact subproof
actually handles. In particular the full-order weighted transpose
was used only in the all-live chart. Its extension to an arbitrary
zero-weight row is not assumed.
