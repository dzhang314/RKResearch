# Checked rational labelled terminal assembly

The [native body](../../RKCert/ReviewedNative/RationalLabelledTerminalAssembly.lean)
uses the concrete chronological one-zero-seed donor prefix, followed
by actual terminal rows indexed by an output label and a copy label.
The stage type is
\(\mathrm{Fin}(1+(d+1)n)\oplus(\mathrm{Fin}\,m\times\mathrm{Fin}\,p)\);
this module does not flatten the terminal copies into a final Fin
index. Each copy reads the final-bank primitive baseline plus its
natural copy parameter times the measured first-bank contrast.

The actual seed law, Quiet through two and nonzero gain are
discharged by the existing checked providers. The theorem retains
\(3\le n,\ 4\le p,\ 2+d\le n+1,\ p\le n+1,\ p\le2+d+1,\ p\le m\),
distinct output clocks \(c\), and all target moments
\(\sum_j\omega_j c_j^k=0\) with \(k+4\le p\). Under those conditions it
gives the literal reviewed HasOrder for the specified labelled
matrix and weights, each copy's actual row-sum clock \(c_j\), and
coalesced outgoing mass \(\omega\) on David's denominator-cleared
two-node defect \(2A(A\mathbf1)-(A\mathbf1)^2\).

The [unchanged typed audit](../../AuditReviewedNativeRationalLabelledTerminalAssembly.lean)
expands the actual matrix and weights, keeps the explicit target
moment sum and all hypotheses, and checks all three conclusions.
The [exact transcript](typed-audit-output.txt) has one named report,
labelled_hasOrder_clocks_and_mass, using only propext, Classical.choice
and Quot.sound. The body and separate no-output audit both exited
zero without warnings. The [acceptance record](acceptance.json)
binds those warm measurements to the exact provider and tool
fingerprints; no cold build is asserted.

No suitable target mass is chosen here. There is no unconditional
order existence, final strict Fin packing, stage minimum, or
positivity claim.
