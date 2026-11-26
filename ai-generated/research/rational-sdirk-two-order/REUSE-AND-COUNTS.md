# One receiver and one dense preparation reused across successive lifts

Fix any prescribed negative real-algebraic common diagonal \(\gamma\). The two-order Newton lift in TWO-ORDER-NEWTON-TAIL.md can repeatedly use one minimum-width Laguerre preparation and the same existing physical receiver. This is an exact ordinary construction, not an assertion of minimum stage count.

## Literal reuse

Start with the genuine dense derivative decoder \(D\) through even grade \(q=2k\ge2\), using \(L(q)=k(k+1)\) old rows, where \(L(d)=\lfloor(d+1)^2/4\rfloor\). Its last Laguerre layer has one selected physical row at a root \(\xi\) of \(W_q=q!(J-\gamma)^q1\). Since \(\gamma<0\), \(\xi<0\). This row is individually exact through size \(q+1\): the nominal layer-\(q\) error at that size is a multiple of \(W_q\) by the paid-band formula. The physical sample at that next size equals the nominal one because each child is within the already paid cap \(q\). This is a literal sample property of that row, not an extrapolated local stage order. In addition, the physical old tree columns through grade \(q\) span the entire preparation. In fact the \(L(q)\) independent commutator/parity witnesses in the sharp dense lower proof all lie in their span. These two facts hold for the canonical signed-diagonal dense preparation over its selected-root coefficient field.

The strict predecessor row at \(\xi\) is exactly the functional \((J-\gamma)D\) evaluated at \(\xi\), on *all* the numerical preparation coordinates. The two functionals agree on every elementary column for trees of size \(\le q\), since the old stage's unary output is correct through \(q+1\) and its diagonal is \(\gamma\); the spanning fact makes this a literal row equality. Extend \(D\) by zero on all subsequent stages, so the row identity persists at every lift, regardless of the current output weights.

Now raise ordinary order by two, to \(p\le2q+2\), using the same dense \(D\). In the quadrature fix not only the \(a=p-q-1\) odd ladder nodes of the two-order proof, but also \(\xi\), placed first. All these fixed nodes are exterior, since the ladder is to the right of \(1\), so the prescribed-hull quadrature argument applies. Use only the last \(a\) distinct clock rows for the correction right inverse. The first receiver is unchanged by that correction. Its row into the *entire* old prefix is \((J-\gamma)D\) at \(\xi\), with its own diagonal \(\gamma\) and no earlier new taps. It is therefore a literal duplicate of the old physical row already identified. Redirect all references from this new row to the old one, transfer its output weight to that existing row, and delete the duplicate. Induction on the elementary weight recursion proves exact preservation of every rooted output, not just order through \(p\). No retained diagonal or old stage equation changes.

The number of quadrature sites is unchanged by requiring this extra site when \(q\) is even. In fact with \(a+1\) fixed nodes the number of free nodes is \(\lceil(p-a-1)/2\rceil=k\); with just \(a\) fixed nodes it is \(k+1\). Thus deletion saves one physical row at every two-order upgrade, with the same stage reused each time. The rule's next-degree mismatch still follows from the fixed-hull argument. If one needs the initial odd order \(q+1\), the same quadrature with only \(\xi\) fixed has \(k\) free nodes and precision \(q\). Append independently fed rows with diagonal \(\gamma\) and pure local order \(q+1\), then merge the identical \(\xi\) row as above. This initializer uses \(k\) new physical stages and has exact odd order \(q+1\).

## Counts for the fixed shared preparation

For an even target \(p=2m\), choose \(q=2k\le p\) with \(p\le2q+2\) and let \(J=m-k\) be the number of two-order steps. The \(j\)-th step costs \(k+2j-1\) stages after reuse. The total is
\[
 L(2k)+kJ+J^2=m^2-mk+k^2+k .
\]
For odd \(p=2m-1\), use the initializer through \(2k+1\), \(J=m-k-1\), and subsequent costs \(k+2j\). The total is
\[
 L(2k)+k+kJ+J(J+1)=m^2-mk+k^2+2k-m .
\]
These formulas assume \(k\ge1\), \(J\ge0\), and \(p\le4k+2\). At zero steps the even integrated dense preparation already gives order at least \(p=q\); no next-order claim is needed for that seed. A one-row common-diagonal stage suffices for order one.

## An alternative that grows the paid decoder without rebuilding it

One can allow \(q\) to advance by one at each two-order step, preserving all old rows. Start with a dense \(q_0\) preparation of ordinary order at least \(q_0\). At step \(j\) the target is \(p=q_0+2j\), the available dense grade is \(q=q_0+j-1\), and \(a=j\). The prescribed-hull quadrature has
\[
              j+\left\lceil\frac{q_0+j}{2}\right\rceil
\]
sites. They are all individually exact through \(q+1=q_0+j\). If there are fewer than \(q_0+j\) distinct sites, add only the deficit as independent zero-weight receivers, at distinct rational points and with the same \(\gamma\), using the old decoder and no taps into the paying rows. Interpolation then supplies the next dense decoder from these actual rows, with no change to the existing literal feed. In this alternative there need not be a reserved co-site merge. The total count for \(p=q_0+2J\) is
\[
 L(q_0)+
 \sum_{j=1}^J\max\!\left(q_0+j,\ j+\left\lceil\frac{q_0+j}{2}\right\rceil\right).
\]
No old prep is discarded or rebuilt. A final next-degree mismatch is proved whenever at least one Newton step is taken.

## Comparison through order twenty

The published unrestricted real-algebraic SDIRK upper is supplied for comparison only. The two columns are universal for any fixed negative real-algebraic \(\gamma\), so they do not permit choosing a favorable diagonal anew each order. Neither changes that unrestricted numerical table. The rational improvements at orders nine and ten use different prescribed positive rational diagonals and the separate rational-node formulas, not these two columns.

| p | Archived unrestricted real-algebraic upper | Fixed prep, one shared row | Growing exact decoder |
|---:|---:|---:|---:|
| 1 | 1 | 1 | 1 |
| 2 | 1 | 2 | 2 |
| 3 | 2 | 3 | 3 |
| 4 | 3 | 4 | 5 |
| 5 | 5 | 6 | 7 |
| 6 | 7 | 8 | 9 |
| 7 | 9 | 12 | 12 |
| 8 | 11 | 14 | 15 |
| 9 | 14 | 18 | 19 |
| 10 | 17 | 21 | 22 |
| 11 | 20 | 27 | 27 |
| 12 | 23 | 30 | 31 |
| 13 | 26 | 36 | 36 |
| 14 | 30 | 40 | 41 |
| 15 | 34 | 48 | 47 |
| 16 | 38 | 52 | 53 |
| 17 | 43 | 60 | 59 |
| 18 | 48 | 65 | 66 |
| 19 | 54 | 75 | 73 |
| 20 | 59 | 80 | 80 |

Over arbitrary paid rings the two-order proof keeps the same common physical unit diagonal, using only paid unit differences in both the Newton and decoder solves. The exterior Laguerre and quadrature existence used in the present sharper counts is a field construction; no simultaneous claim of these counts over all rings is made.

These are mathematical comparisons across the stated coefficient domains.
