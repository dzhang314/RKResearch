# Checked chronological rational donor chain

The [native implementation](../../RKCert/ReviewedNative/RationalDonorChain.lean)
appends \(d+1\) rational donor banks of width \(n\) to an actual
\(s\)-stage seed. Bank zero receives input only from the seed. Every
later bank reads only the immediately preceding bank. Its row at
label \(x\) uses the checked rational primitive moments on the
distinct sample clocks \(z\). All of these rows are entries of one
finite matrix.

For a base row law through \(r_0\) and \(r_0+d\le n+1\), the chain
proves that at bank \(k\), site \(x\), the normalized native stage
value of every tree \(t\) with \(|t|\le r_0+k\) is
\(z_x^{|t|-1}\). These are values of the actual reviewed stage
function \(\Phi\), with its forest-factorial normalization. The
proof generalizes the bank index in the induction: the root factor
is at the current bank, and the branch reads the actual previous
bank. For \(r_0\ge2\), the stage's actual row-sum clock is \(z_x\).

The chronology sends bank site \((k,x)\) to physical rank
\(s+x+nk\). A strict lower seed gives genuine strict lower
triangularity on the resulting Fin index, including zero diagonal
entries. The concrete constructor takes one zero seed stage and
taps \(z_x\) into the first bank. Its final bank is pure through
\(2+d\) when \(2+d\le n+1\), at the same physical ranks at which
its strictness is proved.

The [unchanged typed audit](../../AuditReviewedNativeRationalDonorChain.lean)
checks six literal clients: seed \(\Phi\), the predecessor row
action, physical strictness, native Fin purity, actual row-sum
clocks, and the concrete seed's strictness and last-bank purity.
Its [exact transcript](typed-audit-output.txt) has seven named
reports, each with only propext, Classical.choice, and Quot.sound.

## Measurement and scope

The repaired body and separate no-output audit both exited zero
with Lean 4.36.0 and Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842.
The body used ten previously measured project modules. The audit
used the same fifty fragments and the five new fragments of the
repaired body in one project root. It emitted no object or warning.
The four nonfatal body warnings are precisely the pre-existing
ones, with two locations shifted by the proof-only repair.

The [portable acceptance record](acceptance.json) records both
successes and the original failed attempt separately. The latter
supplied no objects. No compiled file is included, and the
measurements were not a cold package build. Source digests can be
checked from the repository root:

    sha256sum -c ai-generated/lean/evidence/reviewed-native-rational-donor-chain-20261126/checked-sources.sha256

The conclusion is about donor rows, local rooted-tree stages and
literal strictness. It does not supply terminal weights, assert
HasOrder for a full tableau, or claim positivity or a stage minimum.
