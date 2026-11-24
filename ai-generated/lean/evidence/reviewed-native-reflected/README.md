# Reflected tree payment on the reviewed tableau

This native algebraic dependency is for the known DIRK and ERK lower
bounds. It does not assert a numerical stage bound. The proof uses
`FiniteRootedTree`, `Φ`, and `HasOrder` directly. Its only
direct project proof dependency is `RKCert.ReviewedNative.GradedColumns`,
which supplies exact paid forward probes. There is no legacy order
translation.

For a commutative coefficient ring, define the ordinary and reflected
clocks, respectively, by
\[
\mathbf c\coloneqq A\mathbf1,\qquad
\mathbf y\coloneqq \mathbf1-\mathbf c.
\]
The zeroth-indexed physical reverse row is
\[
\mathbf d_k\coloneqq
 (k+1)A^{\top}(\mathbf b\odot\mathbf y^{\odot k})
 -\mathbf b\odot\mathbf y^{\odot(k+1)}.
\]
For a reviewed tree \(t\), define its size, normalized column, and
mixed probe by
\[
n\coloneqq |t|,\qquad
\mathbf v\coloneqq \operatorname{forestFactorial}(t)\,\boldsymbol{\Phi}_t(A),
\qquad
M_{r,k}\coloneqq (\mathbf b\odot\mathbf c^{\odot r}
                            \odot\mathbf y^{\odot k})\cdot\mathbf v.
\]
The adjacent beta-moment identity is
\[
(k+1)M_{r+1,k}=(n+r)M_{r,k+1}
\qquad\text{if }n+r+k+1\le p.
\]
At \(k=0\), this follows by subtracting the two paid forward probes and
using \(M_{r,1}=M_{r,0}-M_{r+1,0}\). At higher \(k\), subtracting the
preceding identities at \(r\) and \(r+1\) and using
\(M_{r,k+1}=M_{r,k}-M_{r+1,k}\) gives the result. No analytic integration
or quotient is needed.

The normalized unary root \([t]\) has the same paid mixed probe as one
additional ordinary clock power on the normalized column for \(t\).
For \(k=0\) this equates moments with the same tree order. For \(k>0\)
it survives the same finite difference. The normalized unary column
also equals \(n A\mathbf v\), and \(n\) is a unit by the reviewed bushy
condition. Mathlib's transpose and dot-product identities give
\[
\mathbf d_k\cdot\boldsymbol{\Phi}_t(A)=0
\qquad\text{if } n+k+1\le p.
\]
Here the forest factorial is also a unit by the actual tree order
condition, not merely nonzero. The proof therefore applies to
commutative rings with zero divisors.

The executable statement
`RKResearch.Certified.Graded.reflectedStageRow_treeSpace` gives the
inclusion in the row's kernel under `j+k+2≤p`, where
`treeSpace A j` spans trees of order at most `j+1`.
The audit checks the three ordinary reverse seeds at order six and
the seventh reverse seed against every tree of order at most eight at
order fifteen. No triangularity, characteristic, sign, weight, or
diagonal assumption enters the payment.

With Lean and Mathlib `v4.36.0`, after the exact native graded
dependency compile `RKCert.ReviewedNative.ReflectedMoments`, run
`AuditReviewedNativeReflected.lean`, and replay the leaf with
`leanchecker --verbose RKCert.ReviewedNative.ReflectedMoments`.
The receipts verify a clean leaf build, an independent replay, and
seven standard-only theorem axiom reports.
