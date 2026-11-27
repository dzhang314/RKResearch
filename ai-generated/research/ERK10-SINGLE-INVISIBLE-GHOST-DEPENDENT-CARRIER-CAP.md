# Two or three carriers in the dependent rank-two invisible ERK10 ghost

Continue the [dependent reflected late-thirteen chart](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-THIRTEEN.md)
after the [rank-three exit](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-RANK-THREE-EXCLUSION.md).
There is exactly one zero output weight at physical 2, its actual
outgoing column \(r=Ae_2\) is supported at one clock \(t=c_3\),
and the live reverse quadratic seed \(u\) is a nonzero multiple
of \(r\). The original \(F_3=\langle e_2,r\rangle\) and \(r\)'s
nonzero amplitude is uniform, denoted \(\rho\ne0\).
Put \(s=A^\vee r\) on the live set, extended by zero at physical 2.
The already proved reduced reverse contact gives active noncarrier
\(s\) at physical 11 and 12, with \(c_{11}=2c_{12}-1\)
and \(c_{11}\ne c_{12}\), and \(s_{13}=0\).
All computations are over a characteristic-zero field.

**Result.** There are only two or three live \(r\)-carriers.
The noncarrier \(s\)-active sites span at least three distinct
clocks. In the zero-pooled-\(bs\) case, the only remaining
physical cardinalities \((m,q,n)\) are
\[
          (2,4,8)\quad\hbox{and}\quad(3,3,6),
\]
where \(m\) counts carriers and \(q,n\) the distinct clocks
and physical rows with \(r=0,\ s\ne0\) on the live set.
These are four, respectively three, unequal-amplitude
noncarrier pairs, with respectively one, two additional
live dormant noncarrier rows beyond the endpoints.
This chart and the nonzero pooled cases still do not
give a 15-stage unrestricted lower bound.

## 1. Actual grade-four column, grade-three dual, and localized squares

The live reverse rooms are
\(W_2=\langle r,s\rangle\) and \(W_3=\langle r,s,Cs\rangle\),
with \(W_3\) not clock-invariant. We have the true old
\[
 F_4=\langle e_2,r,s,Cs\rangle,\qquad
 F_5=\langle e_2,r,s,Cs,C^2s\rangle .
\]
The fifth direction is attained because otherwise \(W_3\)
would be \(C\)-invariant. Although \(s\) generally costs
old grade four, its weighted row \(bs\) annihilates
**all of \(E_6\)** because it belongs to \(W_2\).
In particular the actual \(C^j s\in E_{4+j}\)
pay three square moments:
\[
                  b C^j s^2=0,\qquad 0\le j\le2 .
\]
The same actual dual row also gives \(b C^j s=0\)
for \(0\le j\le6\), testing the clock powers in \(E_6\).
The actual product \(rs\) gives \(\sum_{\rm carriers}b_i s_i=0\).
All carriers have clock \(t\), so their contributions to the
first family vanish individually after pooling; their ordinary
weight sum is also zero by \(br=0\).
Do not drop their square contributions before a separate proof.

If the whole live \(s\)-support has at most three numerical
clocks, a quadratic interpolator in \(C\) localizes \(s\)
at each. Those localized columns are actual grade-five
pure vectors by the displayed flag. Their paid pairing
with the original grade-four \(s\) shows that all localized
\(bs^2\) masses vanish in this case (also directly from the
three dual moments). If the whole support had at most two
clocks, \(C^2s\in\langle s,Cs\rangle\) would make \(W_3\)
invariant. Thus always at least three clocks support \(s\).

There are 13 live sites; the endpoints have \(r=s=0\).
So \(n+m\le11\). The genuine initial pair of reverse
noncarrier responses gives \(q\ge2\). Whenever pooled
noncarrier \(bs=0\), each active noncarrier clock requires
at least two physical rows. The actual ordinary support then
has size at most \(13-m-n+q\), even before any pair-specific
cancellation. If separately every active two-row group has
zero ordinary mass, the stronger bound \(13-m-2q\) holds.
The anchor support floor is six.

## 2. Excluding every four-or-more-carrier case

If \(m\ge5\), then \(n\le6\), so the seven moments of \(bs\)
force the noncarrier pooled row to be zero. Now \(q\le3\).
At \(q=2\), total \(s\)-support is at most three clocks; the
third clock must be \(t\) distinct from both active labels
by noninvariance. Thus each noncarrier active pair has
\(bs=bs^2=0\) groupwise, hence zero ordinary pooled mass.
The support bound \(13-m-2q\) is at most four, impossible.
At \(q=3\), \(n\ge6\) and only \(m=5,n=6\) is possible.
The three active labels and the only other two live
noncarrier rows (the endpoints) supply at most five
ordinary sites regardless of within-pair amplitudes.
Thus \(m\le4\).

If \(m=4\) and pooled noncarrier \(bs=0\), then \(q=2\)
is excluded by the same localized-square count,
now \(13-4-4=5\). For \(q=3\), \(n\) is 6 or 7.
At \(n=7\) there are at most five ordinary support sites.
At \(n=6\), the only six potential sites are the three active
labels and three live clean rows including the endpoints.
Every active label must then be an interior Lobatto root.
The recovered genuine reverse active labels at physical
11 and 12 satisfy \(1-c_{11}=2(1-c_{12})\); reflection
preserves the fixed Lobatto quartic \(L_4\). Its checked
\(L_4(X),L_4(2X)\) Bézout identity forbids two such roots.
This argument does not suppose every pair had nonzero
ordinary mass beforehand; fewer effective sites were
already impossible.

If \(m=4\), then \(n\le7\); the noncarrier pooled row
cannot be nonzero at all, since its six-degree moments
would require **eight** distinct labels. This is an exact
dual \(E_6\) exclusion, stronger than relying on grade-four
scalar moments alone. Hence \(m\le3\) in every branch.

## 3. Residual zero-pooled cardinalities at two or three carriers

There are at least two carriers because the nonzero
individual weights at them cancel. If \(q\le2\), total
\(s\)-support can have a third clock only from a separate,
active carrier clock \(t\). Noninvariance requires that
third clock. But three-clock localization gives
\(\sum_{\rm carriers}bs^2=0\) in that case, and the two
preceding carrier moments are already zero.
For \(m\le3\), their three amplitude moments make every
value group cancel; the zero value at physical 13 then
forces **all** carrier \(s\)-values zero (otherwise two
different groups need two rows each). This contradicts
the required third clock. Thus \(q\ge3\).

Let pooled noncarrier \(bs=0\). If \(m=2\), the two
carrier weights are opposite and \(s_{13}=0\), so
\(\sum_{\rm carriers}b_i s_i=0\) forces every carrier \(s\)
zero. At \(q=3\) all three square masses then vanish
by localization, giving at most \(13-2-6=5\)
ordinary support sites. So \(q=4\), and \(n=8\) or 9.
At \(n=9\) the only ordinary support is the endpoints
and those four active labels; that fixed six-site
Lobatto case is excluded by the actual doubling.
At \(n=8\) there are four pairs and one live dormant
noncarrier besides endpoints. Their four square masses
annihilate degrees through two. If identically zero,
all four pairs cancel ordinary mass and too few sites
remain. Thus each mass is nonzero by the four-node
Vandermonde. Each pair has unequal amplitudes and
nonzero ordinary pooled mass. This is the stated
\((m,q,n)=(2,4,8)\) remainder.

If \(m=3\), then \(q=3\) or 4 and \(n\le8\).
At \(q=4\) one must have \(n=8\), giving the same
forbidden exact six ordinary sites. At \(q=3,n=8\)
there are at most five ordinary sites; \(n=7\)
gives at most six, and equality would again place
all active labels in the fixed Lobatto quartic,
incompatible with the two doubled active labels.
The only remaining choice is \(q=3,n=6\).
If \(s\) lives at no separate carrier clock, the
whole support uses at most three labels, so all
square pools vanish. At each noncarrier label
other than possibly \(t\), every pair then cancels
ordinary mass, leaving at most the four live clean
sites and the one possible mixed label \(t\).
Thus \(t\) must be a distinct active carrier label,
so the whole \(s\)-support uses exactly four clocks.
The four square pools give the one-dimensional
Vandermonde nullspace through degree two. They cannot
all be zero, because then the three noncarrier
pairs would all cancel. So all four are nonzero,
all noncarrier pairs are unequal with nonzero ordinary
mass, and exactly two carrier sites have unequal
nonzero \(s\) while \(s_{13}=0\).
This is the separate \((3,3,6)\) remainder.

## 4. Exact nonzero-pooled cardinalities

If the pooled noncarrier \(bs\) measure is nonzero,
\(q\ge8\). With \(m=2\) the carriers are exactly physical
3 and 13, and \(s=0\) on both by the carrier moment.
Since \(n\le9\), only \(n=8\) or 9 occurs.
If \(n=8\), the one additional live dormant noncarrier
must be physical 10: otherwise rows 10 and 11 are both
active at their compulsory repeated clock, leaving at
most seven distinct active labels. Thus \(q=8\) and the
dormant shares the actual active clock at row 11.
If \(n=9\), the actual 10/11 repeat forces \(q\le8\),
so \(q=8\) with exactly that one repeated pair.

If \(m=3\), then \(q=n=8\); every live noncarrier other
than the endpoints is active and their eight clocks are
distinct. Physical 10 cannot be another active row at
the same clock as 11; it must be the third \(r\)-carrier.
Hence its common repeat clock is \(t\),
\(c_{11}=t,\ c_{12}=(1+t)/2\).
The fifth reverse row is a carrier in this case.
In the normalized repeated-head calculations of the
[dependent late-thirteen proof](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-THIRTEEN.md),
its \(p=1,\ \tau=1/2,\ \epsilon=1\) and its nonzero
tap is \(a=a_{54}\). The fourth response is \(-1/2\);
the true difference gives
\(\Delta R=3a+1/2\), hence the fifth response is
\(3a\ne0\). Thus actual \(s_{10}\ne0\).
Since \(s_{13}=0\) and the three carriers' paid first
sum is zero, \(s_3\ne0\) too. These nonzero-pooled
cardinalities and their contact guards remain open.

[ERK10SingleGhostDependentCarrierCapGate.lean](../lean/RKCert/ReviewedNative/ERK10SingleGhostDependentCarrierCapGate.lean)
checks quadratic localization, the two-point weight identity
and the physical support arithmetic. The actual reverse-dual
grade payment and scalar rank bridges are as shown above.
No general zero-weight or positive-characteristic claim is made.
