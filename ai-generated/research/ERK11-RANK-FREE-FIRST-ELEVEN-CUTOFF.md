# Rank-free first-eleven cutoff for a hypothetical 17-stage ERK11

Let \(A\) be strictly lower triangular on 17 physical rows, and let
\(b\) be an ordinary order-eleven output over a characteristic-zero
field. The old ordinary stage floor forces \(b_{17}\ne0\), by strict
truncation. Write \(C=\mathrm{diag}(A\mathbf1)\), \(Y=I-C\),
and use actual rooted spans \(E_j\) through tree degree \(j=|t|-1\),
with the usual polynomial models. Integration and primitives are
formal operations over the coefficient field.

**Theorem.** Every positive tap \(bA^a\), \(1\le a\le5\), on \(E_5\)
factors through the literal first eleven physical rows. Equivalently,
\[
 v\in E_5,\ v_{1:11}=0
 \quad\Longrightarrow\quad bA^a v=0\quad(1\le a\le5).
\]
Thus the literal first eleven constitute a sharp dense size-six chart,
with full numerical rank eleven and pure dimension five. This needs
no assumption on \(\dim F_5\), the measured rank increments, or
whether \(c_{17}=1\). In particular it closes the **genuine late
output branch** of the five-pure one-spare rank spike. A rank spike
without a genuine late read is not asserted impossible.

In addition to the old paid word and stage bounds, the only extra
field-dependent inputs are the two actual size-nine stage floors:
any output exact for \(\ell_1\) or \(\ell_2\) through size nine has
last support at least thirteen, where
\(\ell_m(P)=\int_0^1(1-X)^mP(X)\,dX/m!\).
See [shift one](WEIGHTED-ORDER-NINE-SHIFT-ONE-ATLAS.md) and the
branch-complete [shift-two proof](WEIGHTED-ORDER-NINE-SINGLE-OFF.md).
These paper floors are proved for characteristic-zero fields.
All reductions below run over any field with \(11!\ne0\)
where those two floor inputs hold. No ordering is needed.

This result does not exclude a dense first-eleven chart with an
ordinary order-eleven extension. Eleven is the **attainable**
generic dense size-six width. The ordinary numerical interval
therefore remains 17–18.

## Paid word and terminal notation

Fix an actual \(v\in E_5\) zero through row 11 and write
\(\mu_a=bA^a v\). The paid budget on this six-row tail is
\(L=5\). Use the
[penultimate theorem and its budget-five extension](../lower-bounds/paid-beta/08-ORDER-ELEVEN-THRESHOLD.md):
\(\mu_4=0\); if \(\mu_5\ne0\), then
\(\mu_2=\mu_3=\mu_4=0\). These results are at an arbitrary
actual anchor, not a result about a particular measured rank.
They depend on actual word tests, triangularity, the diagonal
clock, and paid purity of the commutator.

For any actual \(\ell_m\)-weighted row \(\rho\) and an actual
rooted vector within a word budget \(L'\), the response of a
word of length \(d\le L'\) in \(A,Y\) is
\(\rho A^d v\) times the product of \(m+j\) for every \(Y\)
at outer-to-inner position \(j\). This follows from
\(\ell_m(JP)=\ell_{m+1}(P)\) and
\(\ell_m((1-X)P)=(m+1)\ell_{m+1}(P)\).
In particular for \(b\),
\[
                 bY^j A^a v=j!\,\mu_{a+j}
                        \qquad(a+j\le5).
\]
The reverse seeds \(h_1=bA-bY\), \(h_2=2bYA-bY^2\)
annihilate \(E_9\) and \(E_8\), respectively.

## If the top tap is visible

Assume \(T=\mu_5\ne0\). The unique five-edge path on rows
12–17 is live, so \(\gamma_i=A^i v\), \(0\le i\le5\), are an
actual echelon basis of that literal suffix. Put \(W=\mu_1\)
and \(y_i=1-c_{12+i}\). Write the clock action in this basis.
The one-clock words, using \(\mu_2=\mu_3=\mu_4=0\), give
\[
 \begin{split}
 Y\gamma_0&=y_0\gamma_0+5\gamma_1+a\gamma_4+a'\gamma_5,\\
 Y\gamma_1&=y_1\gamma_1+4\gamma_2+d\gamma_5,\\
 Y\gamma_4&=y_4\gamma_4+\gamma_5,\\
 y_0 W+aT&=0,\qquad y_1 W+dT=0 .
 \end{split}
\]
For example the first off-diagonal in the first line uses
\(bA^4Y\gamma_0=5T\). The next two coefficients use the
zero reads of \(bA^3Y\gamma_0\) and \(bA^2Y\gamma_0\).
The last supplied equation of the first line comes from
\(bAY\gamma_0=0\); the second line is the same descending
read on \(\gamma_1\). The equality \(Y\gamma_4=y_4\gamma_4+
\gamma_5\) follows from \(bY\gamma_4=T\).
In an adjacent two-coordinate quotient a repeated physical
clock has scalar action. Hence \(y_0\ne y_1\) and \(y_4\ne y_5\).

**Nonendpoint final stage.** The paid word \(bYAY\gamma_0\)
is zero, and its expansion above is \(a y_5 T\): the first
two terms read \(\mu_2,\mu_3\), and \(A\gamma_5=0\).
Similarly \(bY^2\gamma_1=0\) gives \(d y_5 T=0\).
If \(y_5\ne0\), then \(a=d=0\), and \(y_0\ne y_1\)
forces \(W=0\). The row \(h_1\) kills \(\gamma_i\) through
\(i=4\) by its paid budget, and \(h_1\gamma_5=-y_5 T\).
Reweight the actual ordinary output by \(b+h_1/y_5\).
It is exact through size ten and is zero on
\(\gamma_1,\ldots,\gamma_5\), which span the literal coordinates
13–17. It ends by row 12, below the old size-ten floor 14.

**Endpoint final stage.** Now \(y_5=0\), so \(y_4\ne0\).
The second seed \(h_2\) kills \(\gamma_0,\ldots,\gamma_3\)
and \(e_{17}\). Directly from \(Y\gamma_4=y_4\gamma_4+
\gamma_5\) and \(Y\gamma_5=0\),
\[
                  h_2\gamma_4=-y_4 T .
\]
Reweight the true shift-one output to \(bA+h_2/y_4\).
It is exact for \(\ell_1\) through size nine and vanishes
on \(\gamma_1,\ldots,\gamma_5\): the original tap is zero
on those basis elements except for \(T\) at \(\gamma_4\).
It ends by row 12, contrary to the new shift-one floor 13.
This argument requires neither \(W=0\) nor the actual
first seed \(h_1\) being zero in the endpoint case.

We conclude \(\mu_5=0\) as well as \(\mu_4=0\).

## A local first-only response on a triangular tail

Here is the needed mixed root/clock criterion, stated using
only paid words. Let a row \(\rho\) be last-active at its
actual final site, and suppose a fixed input \(v\) is zero
before a suffix with at most \(J+1\) sites. Use a word budget
\(J\ge3\) at shift \(m\), and assume
\[
     \nu_1=\rho Av\ne0,\qquad \nu_a=\rho A^a v=0
                       \quad(2\le a\le J).
\]
Write \(u=Av,\ \tau=\rho A\) and number the visible suffix
starting at 0.

**Size and clocks.** The scalar \(\rho Yv=(m+1)\nu_1\)
is nonzero, while \(\rho Y^jv=0\) for \(2\le j\le J\).
Group the charges \(\rho_i v_i\) by nonzero reflected clock.
The \(J-1\) consecutive zero moments imply there are at least
\(J\) distinct nonzero *charged* labels: on at most \(J-1\)
nonzero labels the relevant Vandermonde matrix, after scaling
by the lowest power, is nonsingular. If at most \(J\)
physical sites are visible, all \(J\) would have distinct
nonzero clocks and live charges. But then \(u\), starting
one site later, has at most \(J-1\) such charges.
Its \(J-1\) zero moments \(\rho Y^j u=0\), \(1\le j<J\),
would give \(\rho u=0\), contradiction.
Thus there are exactly \(J+1\) physical slots and \(v\)
starts at slot 0.

There is an endpoint clock in these slots. Otherwise, since
\(\rho u=\nu_1\ne0\) and its first \(J-1\) positive moments
are zero, every site \(1,\ldots,J\) would carry a live
\(\rho_i u_i\) at distinct nonzero reflected clocks.
Also \(\tau v=\nu_1\ne0\) and \(\tau Y^jv=0\) for
\(1\le j<J\); because strictness makes \(\tau\) end before
slot \(J\), its sites \(0,\ldots,J-1\) would all carry live
\(\tau_i v_i\), again at distinct nonzero clocks. But
\(\tau Y^j u=0\) for \(0\le j\le J-2\), on precisely
the intersection \(1,\ldots,J-1\). Its Vandermonde forces
\(\tau_i u_i=0\), contradiction.
Hence the \(J+1\) slots consist of one endpoint and
\(J\) distinct nonendpoint labels, each having \(\rho_i v_i\ne0\).

**Endpoint placement.** If the endpoint is at an index \(e>0\),
the \(J-1\) zero positive moments on \(u\) make it supported
only at the endpoint inside this visible suffix (all
nonendpoint \(\rho_i\) are nonzero). Its endpoint value \(u_e\)
and \(\rho_e\) are nonzero. If \(e<J\), the same
Vandermonde on the positive \(\tau Y^jv\) moments gives
\(\tau_e v_e=\nu_1\ne0\), because \(\tau\) sees precisely one
endpoint and at most \(J-1\) other labels. Then
\(\tau u=\tau_eu_e\ne0\) contradicts \(\nu_2=0\).
Thus the unique endpoint is either initial or terminal.

**Initial endpoint.** The nonendpoint sites \(1,\ldots,J\)
all have live \(\rho_i u_i\) by the same \(J-1\) zero moments
and nonzero \(\rho u\). The paid \(\tau Y^j u=0\),
\(0\le j\le J-2\), then kills every \(\tau_i\) on
\(1,\ldots,J-1\). In particular \(\tau\) ends at slot 0.
The actual vector \(A^2 v\) has zero visible coordinates:
it starts at slot 2 and the \(J-1\) tests
\(\rho Y^j A^2 v=0\), \(0\le j\le J-2\), test all its
distinct live sites \(2,\ldots,J\).

**Terminal endpoint.** The actual \(Av\) is supported only
at that endpoint inside the visible suffix, as above.
The row \(\tau A\) ends before slot \(J-1\) by strictness.
The tests \((\tau A)Y^j v=0\), \(0\le j\le J-2\), are
\(J-1\) Vandermonde rows on the first \(J-1\) distinct
nonendpoint clocks (where \(v_i\ne0\)). So \(\tau A\)
has no coefficient anywhere in the visible suffix.

These arguments concern actual words on the given input.
The local support asserted for \(A v\) or \(A^2v\) is only
through the actual terminal site of \(\rho\). When it is a
tap of a longer tableau, later coordinates must be counted
separately.

## Excluding all lower visible taps in the ordinary tableau

If any positive read remains, choose the highest nonzero
one \(\mu_k\), for \(1\le k\le3\) (on the fixed \(v\)).
Take \(\rho=bA^{k-1}\), actual shift \(m=k-1\), effective
size \(12-k\), and budget \(J=6-k\) on \(v\).
Its last position is at most \(18-k\) by strictness.
Thus at most \(J+1\) slots are visible from row 12, and
\(\nu_1=\rho Av=\mu_k\ne0,\ \nu_2,\ldots,\nu_J=0\).
All hypotheses of the local criterion hold. Its row count
forces the true last position \(18-k\).

* **Initial endpoint, \(k=1\) or \(2\).** The next genuine
  tap \(\rho A=bA^k\) ends at physical 12.
  For \(k=1\) it is shift-one size ten, below the old floor
  fourteen. For \(k=2\) it is shift-two size nine, below
  the new floor thirteen.
* **Initial endpoint, \(k=3\).** The true \(\rho=bA^2\)
  ends at physical 15. The local criterion gives zero
  \(A^2v\) through 15, so only rows 16,17 can contribute
  on that actual vector. The paid ordinary tests
  \(bY^2 A^2v=bY^3 A^2v=0\) kill its at most two
  nonendpoint charges (including coincident or endpoint
  labels). This contradicts \(bY A^2v=\mu_3\ne0\).
* **Terminal endpoint, \(k=1\).** The row
  \(\rho A^2=bA^2\) ends by 11, contrary even to the old
  weighted size-nine floor twelve.
* **Terminal endpoint, \(k=2\) or \(3\).** The actual
  \(u=Av\) is zero through the visible suffix except at
  its terminal endpoint, followed by \(k-1\) physical
  slots. Hence positive ordinary clock moments see at
  most \(k-1\) nonendpoint charge labels.
  The \(k-1\) consecutive paid zeros \(bY^a u=0\) for
  \(a=k,\ldots,2k-2\) eliminate them. Here
  \(a\le4\) is within the full word budget on \(u\).
  This contradicts \(bY^{k-1}u=(k-1)!\mu_k\ne0\).

This completes the factorization proof. The old floor
fourteen covers both ordinary and weighted size ten, so no
specific real-valued coefficient construction is used.

## Consequences and field boundary

A polynomial alias on the literal first eleven through
grade five has \(P(0)=0\) and is killed by the five
positive taps, i.e. by \(\ell_1,\ldots,\ell_5\).
Write \(P=XQ,\ \deg Q\le4\). The weighted Gram for
\(X(1-X)\) against degree at most four gives \(Q=0\).
Thus the prefix has genuine separated grade-five data,
and the paid dense size-six floor forces rank eleven
(and exactly five pure directions). This is the condition
that the earlier zero/one-spare ledger could miss.

Only two steps above require the **new** floors, and each
literally manufactures a 12-or-fewer-stage row of that
shift: the endpoint top-visible reweighting (shift one),
and the initial-endpoint \(k=2\) genuine tap (shift two).
All other alternatives are excluded over every paid
field. Thus the argument both applies over characteristic
zero and reduces every possible paid-characteristic
failure of this cutoff to those two concrete weighted
size-nine alternatives. Transfer to a general
commutative ring would require a residue field in which
the relevant weights, alias and paid floor assumptions
survive, or a separately established universal weighted
floor; there is no new unconditional ring claim.

The generic eleven-row dense chart remains realizable.
Ruling out its extension to ordinary size eleven is a
separate task; this result should not be reported as
the 18-stage lower bound. The Lean file checks independent
scalar and moment gates, while the actual rooted/order
and physical suffix assembly here is paper.
