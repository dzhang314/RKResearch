# Single-evaluation tilts: reclassify one effective high axis

This closes the last **rational** width-14 case for the
[one-direction relaxation](README.md).
Retain the regular five-row opening, score only its origin,
and require actual high purity through size four and at most
one actual high error direction at size five. Then a rational
order-ten method in this architecture needs at least ten high
rows, hence at least fifteen total. A split \(P/X\) is allowed.
The remaining width-fifteen rational mixed cases and the
unrestricted rational interval are not settled.

## Where an evaluation can occur

If the true tilt is \(\ell(f)=\kappa f(r)\), \(\kappa\ne0\),
the support argument of the main note forces \(r\in\{s,p,q\}\).
The old covector \(\tau\) representing this functional is
uniquely the single surviving coordinate on these three
nonzero distinct labels: their first three positive powers
are independent. Its vanishing on \(\boldsymbol V,C_o\boldsymbol V\)
requires \(V_r=P(r)/P(s)=0\).
Since \(V_s=1\), only **\(p\) or \(q\)** can be the host.
At either host the literal old stage is pure through size
four (the two existing old defect directions are zero there).

At \(p\) this forces \(\alpha=0\), equivalently \(p=3s/2\).
Its \(A_o\boldsymbol V\) entry is then \(p^2/(2s)\ne0\).
The **fixed** contact \(\boldsymbol\eta=0\) would require
\(\tau(A_o^2\boldsymbol d_o)=0\), because that column has
zero high part, so cannot have host \(p\). Free old contact
is not subject to that extra annihilation.

At \(q\) it forces \(\beta=0\), equivalently \(P(q)=0\).
For fixed contact, \((A_o\boldsymbol V)_q=0\) as well.
The literal old \(q\) row then yields
\[
 (A_o\boldsymbol V)_q=A_{q,s}+\alpha A_{q,p}
       =\frac{q^2[3ps-(2p-s)q]}{3s^3}.
\]
Indeed it has no \(e\)-tap and integrates \(X,X^2\) exactly
using \(s,p\); substituting the regular \(\alpha\) gives
that expression. Thus \(q=3ps/(2p-s)\), with \(2p-s\ne0\).
Writing \(P=X(X-q)(X-t)\), the regular old relation gives
\(t=2q-3s\). Therefore \(JP(q)=q^3(q-2s)/4\ne0\):
\(q=2s\) in this branch would also give \(p=q\), disallowed.
In the fixed branch the scaled tilt is
\(\ell(f)=f(q)/JP(q)\) when the high error direction is
\((BE-EJ)P\); this also follows from
\(\widetilde E(JP)=BEP\).

These old scalar gates are **not** contradictions.
The [exact split fixture](audit.py) uses
\(s=1,p=3/2,q=9/4,e=1/8\),
\(P=X(X-3/2)(X-9/4)\), and arbitrary causal toy high
rows, and obtains the genuine tilt
\(\ell(f)=(1024/729)f(9/4)\).
It is a 17-profile local replay, not a method of order ten.

## Reclassification creates pure sources

In the evaluation case the actual size-at-most-five response
satisfies
\[
 \boldsymbol\Phi^{high}-E_h f
   =-\kappa\,(\Phi^{old}_r-f(r))\boldsymbol\delta
\]
for *every* normalized combination with model \(f\), not only
for early-null inputs. Indeed subtract its bush combination
to obtain a zero-model input, and use the old pure functional
\(\tau=-\kappa E_r\) on that old residual.

Move the old chronological suffix beginning at the host \(r\)
into the high block. This moves just \(q\) if \(r=q\), and
\(p,q\) if \(r=p\). There is no reordering and the retained
old prefix is still closed under causality. The true old
model-zero pure span through size five is the entire
four-dimensional nonorigin old coordinate space, by the
regular opening ledger. For any \(f\in X\mathcal P_3\)
start with its bushes and adjust using this actual span so
that its retained old column is zero and each reclassified
old coordinate equals its nominal model \(f\) there.
Since the physical host now has zero model error, the
original high block also agrees with \(E_h f\).
Thus the reclassified block earns **pure** early-null input
\(E'f\), with the full \(f\in X\mathcal P_3\), at size five.

Applying actual same-root clock marks and unary contexts
therefore gives all pure word tests through length five on
this expanded block. The reclassified scores are zero by
the original output support; the opening origin and its
score do not move. The true scalar moments of degrees 0–9
are unchanged, as are the clocks on original stages.

## Erase the extra unscored axes from the tests, not the tableau

For each reclassified old coordinate \(j\ne r\), the same
old pure span supplies an actual size-at-most-five,
zero-model profile with full old column exactly
\(\boldsymbol e_j\). Since its physical host entry is zero,
its original high response is zero. Its reclassified
high profile is exactly \(\boldsymbol e_j\), with no
retained old component. Thus the actual order test gives
\[
                 \boldsymbol w^T W\boldsymbol e_j=0
                         \quad (|W|\le5).
\]
The coefficient at the index being erased is zero even for
the empty word (all reclassified old coordinates had
zero score). No assumption is made that its incoming
or outgoing taps vanish.

Let \(Q\) be coordinate projection that erases those axes.
Pre- and post-inserting \(Q\) at each letter of a pure
word still gives the same output on its input. Insert
from the right to the left: each difference pairs
an **unprojected** prefix of length at most five with
an erased-axis vector. The equality just proved makes
that pairing zero. The last projection on the output
does not change the scores. Equivalently the
[portable functional erasure lemma](../../lean/RKCert/ReviewedNative/ERK10TiltSilentErasure.lean)
gives this identity by prefix induction.

After restricting to surviving coordinates, this is
precisely the principal strict high submatrix \(B'\),
the unchanged clock diagonal \(C'\), and the restricted
evaluations and scores. There are \(n+1\) surviving
high coordinates: all original high rows and the one
reclassified old host \(r\). This is an equivalence of
the **short word budget**, not a claim that a literal
smaller Runge–Kutta tableau still has order ten.

## Why the rational pure census applies unchanged

For clarity the previously closed rational pure-word
case is used here as a theorem on the following raw
data, not on a new opening tableau:

1. Strict chronological high block \(B'\) of width
   at most ten, assigned clock vector \(\boldsymbol x'\)
   with mark \(C'=\operatorname{diag}(\boldsymbol x')\),
   and arbitrary physical scores \(\boldsymbol w'\).
   There is no condition \(\boldsymbol x'=B'\boldsymbol1\)
   in the raw word problem; the original opening used to
   compensate those row sums. The principal block after
   erasure is still strict, and the exogenous clocks
   and mark are exactly the original assigned clocks.
2. Exact scalar moments through degree nine for the
   high block and the unchanged old-origin score at
   \(0\), including degree zero. The new host has
   score zero, which the census expressly allows as it
   allows any physical and pooled scores. The erased
   axes have zero scores, so erasing them preserves
   all scalar moment identities, including the constant.
3. All exact pure words on \(Ef\) for
   \(f=X,\ldots,X^{9-|W|}\), \(|W|\le5\), with their
   nominal integration or marked primitives. These
   follow above using actual profiles, unchanged
   assigned clocks, and the nil contribution at every
   erased axis.

The nominal weighted power vectors, the shifted Hilbert
matrix, actual clock marks and the reverse defect grading
all use just these data. The forward annihilators
\(B'E'f-E'Jf\) use the same pure words; the independence
of their first two distinct nonzero forward rows uses
only strict causality and exogenous evaluations.
The Hilbert support ensures those witnesses exist even
if \(r\) itself has score zero. The paid plateau therefore
locates a live endpoint, and the earlier reverse-first
census uses only these word-derived actual row reads,
visible clock support, causal order, scalar quadrature,
and its rational terminal arithmetic. Inspection of its
grade-five blind tests and forward-range certificates
uses no supplementary \(BEP=EJP\) or actual old row
constraints once the pure budget is present. The raw
words allow stripping unused no-score terminal rows and,
when needed, padding by unused exact high-row copies
immediately after a nonendpoint row, without ever
recreating the five-opening chart.

Thus a hypothetical rational method with original
\(n\le9\) would give \(n+1\le10\) for these exact raw
pure words, contrary to the complete
[rational pure-word exclusion](../erk10-five-opening-plateau-endpoint/README.md).
The argument is valid when the old \(q\) row reads the
old \(p\) row, and its scalar coefficients are not altered.

Together with the full-mark and pure alternatives,
this finishes the rational 14-stage one-direction
classification in this exact opening. In paid fields
more generally the reclassified pure words force at
least ten coordinates, so \(n\ge9\) in the single
evaluation case; the real \(n=9\) case is not ruled out
by the rational census.
