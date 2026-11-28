# Three consecutive closures: zero pooled masses

Assume the full ten-row reverse chronology
\(0,a,b,c,z_1,z_2,z_3,d,e,f\), with \((z_1,z_2,z_3)\) a permutation
of \((a,b,c)\). The [all-open exit](README.md) also excludes this
chronology over any \(10!\)-paid field if **at most one** pair has
zero total score, with no condition on the individual scores.
Over \(\mathbb Q\), two or more zero-total pairs are impossible by
the [origin-anchored scalar parity floor](../erk-origin-degree-nine-scalar-floor/README.md):
they would leave at most six allowed scalar sites (including the
origin). The parity floor allows arbitrary signed or zero weights at every remaining site, including the origin and endpoint. Thus the stated chronology is excluded over \(\mathbb Q\)
for **all scores and pool totals**. The result uses three consecutive
closures for the zero-total extension, versus only the first two
when all pool totals are nonzero.

Continue to use the notation of the [main proof](README.md) and
[zero-score addendum](ZERO-SCORES.md). The case without zero pools
is already done, so write \(t\) for the sole pair of zero total.
One useful rule is independent of the defect grade: if the two
scores at \(t\) are nonzero and opposite, every opposed mode there
is a scalar multiple of the two physical scores. As a result,
even if both copies become available donors,
their contribution to \(K\) of that mode is the same scalar
multiple of the *total* scalar tap at label \(t\). If both
scores equal zero, all scalar taps into that label vanish, though
taps into a nonzero opposite defect there need not vanish.

## No leakage

Assume \(D_4\subseteq S\). Let \(z,j\) be the two nonzero-total
closures in chronological order. Their \(Y,Y^2,Y^3\) primitive
means are exact by the vanishing of
\(\boldsymbol u,\boldsymbol g,\boldsymbol k\) in each group sum.
No new label appears before \(j\). Hence the same cubic-interpolated
taps apply at the two target labels \(z,j\), with third donor label
\(t\); in particular the \(j,t\) determinant is nonzero.

If both actual \(t\)-scores vanish, use the source \(Y(Y-z)(Y-j)\)
at both closing groups instead. It vanishes on every available
scalar donor. Its primitive at \(z\) is \(z^3(2j-z)/12\), and at
\(j\) it is \(j^3(2z-j)/12\). Both vanishing would force
\(z=2j,j=2z\), impossible. Otherwise the \(t\)-scores are
nonzero and opposite. A zero opening score at \(j\) is impossible:
the \(j\)-column in both target means would be zero, since only
the first copy can appear among their earlier donors.
Therefore \(j_1\) is live.

For the defect \(K((\boldsymbol y-z)\odot\boldsymbol u)\), label
\(z\) contributes nothing, label \(j\) contributes only its first
copy, and label \(t\) contributes the same proportional mode on
one or both copies. The two-target determinant now forces
\(u_{j_1}=u_{t_1}=0\). The first nonzero-score interior
opener is active in \(\boldsymbol u\); it must therefore be
\(z=a\), with \(z_1\) live (all three openers are now live).
Since \(\boldsymbol h\) vanishes at both \(z\)-copies, the same
determinant applied to \(K\boldsymbol h\) forces \(\boldsymbol h\)
to vanish at the other openings. This contradicts the nonzero
\(h_{b_1}\) forced by the vanishing of \(u_{b_1}\), as before.

## Leakage

Assume \(D_4\not\subseteq S\). The low-grade pair directions and
inert-row argument depend on **zero group sums**, never on
nonzero group masses. Thus, with no more than one zero opening
score, the analysis in the two preceding notes gives either an
inert zero-score row, or two independent grade-at-most-three
modes at \(a,b\) and a nonzero score at the clean opener \(c_1\).
The inert case already contradicts \(\dim D_4=3\).

In the clean-\(c\) case take the chronological first closure
\(z\) among labels \(a,b\) having \(W_z\ne0\); one exists since
there is only one zero-total pair. Any earlier closed \(a\)- or
\(b\)-pair has zero total, so its normalized mode continues to
track its total scalar tap by the rule above (or that tap is
identically zero if both its scores vanish). Unclosed \(a,b\)
labels contribute only their first-copy scalars, and closed or
open \(c\) supplies just its one scalar label for the other terms.
Consequently the same cubic cancellation at this nonzero-mass
group proves \(z=c\), contradiction. Equivalently the cleared
identity is \(W_z z^2(z-c)^2=0\) using unnormalized sums.

If all three opening scores vanish, the first nonzero-mass
closure has no preceding nonzero-ordinate scalar donor. The only
earlier closure possible is \(t\), and with zero opening score
and zero total its second score is zero as well. The \(Y\) mean
is already impossible.

If just one opening score is nonzero at \(p\), compare the first
nonzero-total closure \(z\). The only live nonzero scalar label
available is still \(p\), possibly on both copies if \(p=t\) was
already closed. Its \(Y,Y^2\) payments force \(z=3p/2\), and its
mean scalar tap onto \(p\) is \(z^2/(2p)\ne0\).
The mode \(\boldsymbol u\) is active at \(p\), with
first entry \(-w_{p_1}p^2/2\). If both copies of \(p\) are
available, this mode tracks the actual weights by the rule
at \(t\). The exact group mean for \(K\boldsymbol u\) thus
forces some other first copy \(r_1\) to have nonzero
\(\boldsymbol u\) entry: its label is distinct from \(p\), and
a second copy cannot carry a nonzero mode if its first has zero
entry. These two modes force the last opener \(q_1\) to have
\(u_{q_1}=h_{q_1}=v_{q_1}=0\). At that original opening row
(no pairs have closed), the same three tests kill its taps to
\(p_1,r_1\) when present, then to the endpoint; the endpoint is
nonzero because otherwise it itself would be inert. The zero
opener is inert, contradiction.

No field-independent exclusion is asserted for **two or
more** zero-total pairs: only the origin-anchored parity/DVR
argument treats such scalar support in this packet.
