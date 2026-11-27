# What both new weighted nine floors do and do not do for ordinary ERK11

Work over a characteristic-zero field. The two paper theorems for weighted
size nine assert that **any** actual row exact for \(\ell_1\) or \(\ell_2\)
has last nonzero physical position at least 13. Their rooted bridges are
mathematical; the exact scalar leaves are separate. No new ordinary stage
count follows by applying either directly. For a hypothetical 17-row
ordinary order-eleven tableau the old ordinary floor and strict truncation
force its physical output \(b_{17}\ne0\). There is no inactive-final branch.

## Exact size guard for the ordinary cutoff

Use the [zero/one-spare cutoff](../lower-bounds/paid-beta/separated-pure/ZERO-OR-ONE-SPARE-DETECTOR-CUTOFF.md)
at \(s=17,\ r=11,\ m=0,\ g=5,\ L=5,\ k=11\).
Its source theorem needs \(k+1<N_*\) at each of the sizes and shifts it
uses. The augmented detector takes the genuine \(\zeta=bA\), shift one,
size ten. In the missing-shift calculation its next tap \(\zeta A=bA^2\)
is shift two and size nine. In its reweighting, \(\zeta\) plus a
detector row becomes a new actual **shift-one size-nine** row; it need
not itself be a tap. The unaugmented detector instead uses size ten
at shifts zero and one (reweighting and genuine next tap, respectively).
Each size-ten case has floor at least 14, either by the older paid
floor or by applying the appropriate size-nine theorem to one
further genuine tap. Thus the two off-census theorems really pay
\(12<13=N_*\) for the common size guard. Neither an inferred
unweighted prefix order nor a restriction to \(bA^2\) suffices for
the reweighted size-nine case.

## Exact split still needed

Let \(f=\dim F_5,\ \epsilon=[h_1\ne0],\ \eta=[c_{17}=1]\) and
\(H_i=E_i+K e_{17}\) when \(\eta=1\), \(H_i=E_i\) otherwise.
The paid separation through degree five gives
\(\dim E_5=6+f,\ f\ge5\). The terminal-coordinate endpoint Gram
gives \(\dim H_5=6+f+\eta\), and \(\epsilon+\eta\ge1\).
The reverse rank bound gives spare
\[
       0\le\omega=7-f-\epsilon-\eta\le1 .
\]
Hence:
* \(\omega=0\) means either \(f=6,\epsilon+\eta=1\), or
  \(f=5,\epsilon+\eta=2\). Both have the cutoff through first 11.
* \(\omega=1\) means exactly \(f=5,\epsilon+\eta=1\).
  If there is a genuine late read, the cutoff theorem forces a
  measured spike
  \[
       \dim H_{5+j}=\dim H_5+j+1
                \quad\text{at some }j\in\{1,2,3,4\}.
  \]
  For a direct contradiction or proof of cutoff it is not enough
  to assert nominal ranks. Reanchoring at any such \(j\) has
  \(L'=5-j<5\) and \(k'+1=12+j\ge13\); neither the original
  penultimate theorem nor the strict common size guard automatically
  applies there. In a reanchor proposal these are **two distinct**
  obstacles. In particular the first-spike case would need a
  budget-four argument, not merely the new floor13.
* Whenever all positive taps cut through 11, the literal prefix
  separates its models through degree five: a possible alias
  \(P=XQ,\deg Q\le4\), is killed by the five reads
  \(\ell_1,\ldots,\ell_5\); the paid \(X(1-X)\) Gram kills \(Q\).
  Conversely this separation of the literal prefix forces all
  positive reads to vanish on its late vectors, because their
  models are then zero; adjoining the endpoint direction does not
  change positive reads. Thus in the \(f=5\) one-spare case genuine
  late read is equivalent to a rank deficit of the literal first
  11 on \(E_5\): a separated prefix requires rank at least 11 from
  the six polynomial directions and five pure directions, while
  rank 11 is injective on the global 11-dimensional \(E_5\).
* In the cutoff branch, the prefix consequently has **exact**
  rank eleven and pure dimension five. It has an exact dense
  size-six decoder at its known sharp width 11. When global
  \(f=6\), the kernel of restricting \(E_5\) to the first 11 is
  exactly one actual pure dimension; when \(f=5\), that restriction
  is injective. The extra endpoint if present is a separate
  augmented direction. The existing generic dense-width theorem
  cannot turn this sharp situation into a contradiction. The next
  needed argument must exclude a sharp 11-row dense prefix as part
  of an ordinary order-eleven **extension**, or show a cutoff
  through at most ten using additional full-tableau premises.

Accordingly the clean next assignments are (i) the genuine-late,
one-spare measured spike, and (ii) the sharp 11-row cutoff prefix
with its actual ordinary order-eleven extension. These are not
extra assumptions silently imposed in either weighted-nine theorem.
The ordinary interval stays 17–18 pending both issues.
