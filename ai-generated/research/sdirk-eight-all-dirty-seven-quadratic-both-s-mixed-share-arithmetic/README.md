# Both-singleton mixed prefixes with one shared D: all four arithmetic cases

Assume the [same mixed one-shared frame](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md): strict ten stages, ordinary order at least eight over a characteristic-zero field, all ten literal quadratic defects nonzero, exactly seven distinct clock labels, both endpoints singleton. Orient S,D,D first, with opposite S,D,S or S,S,D, sharing one observed D label. This packet excludes all **four arithmetic/arithmetic** phase meshes (A1A2, A2A2, A1A3, A2A3). It makes no assumption on signs or any field ordering.

The first subindex is which later forward D is shared, with actual offsets \(u,2u\); for the reverse phase A2 or A3 the shared D offset \(v\) is respectively second or third in the actual reverse orientation. Its later S offset is \(2v\) or \(v/2\) as paid, not an allowed reorder. The [separate star-containing five charts](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-stars/README.md) cover every other chronological phase in this scope.

## Same projective rows, no extra restrictions

Use the [actual five quadratic reads and affine third-D recovery](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-rank/README.md#two-paid-affine-scale-rows-with-no-guessed-missing-d-copy), with true mirror scale \(\lambda\). The determinant of the two affine paid equations is \(E=A D_1-C B_1\). The third-D affine \(z(\lambda)\) must satisfy
\[
 G(\lambda)=m_0(\lambda-1)+H z(\lambda)(m_2+m_3(z(\lambda)+H))=0,\qquad
 J(\lambda)=M_3(z(\lambda))=0 .
\]
Homogenize \(G,J\) separately against each true scale line as in the [star proof](../sdirk-eight-all-dirty-seven-quadratic-both-s-mixed-share-stars/README.md#a-rank-safe-projective-scale-and-the-actual-missing-d). The declared quadratic/cubic degrees are safe even if the leading coefficients disappear upon specialization: the homogeneous row is just the corresponding scale coefficient to that degree times the true evaluation. The row is necessary even when either or both line coefficients vanish. Thus no rank assumption at a special residue occurs. Rank zero is independently impossible, but not an ingredient needed to strip the polynomial pivot.

The four determinant/paid-row resultants in \(v\), after only true \(u\)-only guard removal, have the following exact profiles:

| Phase | Guarded projected degrees | Irreducible common \(u\)-factors |
| --- | --- | --- |
| A1A2 | 655,1071,587,980 | degree 7, multiplicity 2 |
| A2A2 | 563,933,573,948 | degree 9, multiplicity 2 |
| A1A3 | 637,1051,473,805 | degree 9, multiplicity 2; degree 12, multiplicity 4 |
| A2A3 | 594,982,532,889 | degree 12, multiplicity 4 |

Every candidate is checked in the abstract exact \(u\)-field. The determinant is made monic in \(v\) there, then the entire part supported by one **genuinely forbidden** guard is removed exactly. The exact pre/post degrees and fixed full-degree simple places are:

| Phase / factor degree | True nonzero guard used | Exact \(v\)-degree | Prime, residue \(u\) |
| --- | --- | --- | --- |
| A1A2 / 7 | \(t\) (later reverse S distinct from first S) | 17 → 15 | 19,11 |
| A2A2 / 9 | \(q-t\) (D cannot be that S) | 16 → 15 | 11,6 |
| A1A3 / 9 | \(q-t\) | 16 → 15 | 31,21 |
| A1A3 / 12 | \(N(v/2)\) (actual nonzero A3 later D numerator) | 16 → 14 | 37,14 |
| A2A3 / 12 | \(N(v/2)\) | 17 → 15 | 17,6 |

The exact trim precedes reduction, so its unit check is not discarding a characteristic-zero point whose guard merely drops in the residue. At each fixed simple place the trimmed monic determinant has all coefficients integral, so an actual \(v\) would be integral under an extension of the \(\mathbb Q_p\) embedding. Its residue would be a common root of that monic row and all four integer homogeneous rows. The joint polynomial gcd is one in every case, ruling out roots in the whole residue algebraic closure. Thus no reality/sign test, primitive root isolation or conditional truncation is needed. These are characteristic-zero contradictions, not claims of impossibility for arbitrary positive characteristics.

## Replay and status

Run `SYMPY_GROUND_TYPES=flint python check_arithmetic_cases.py` with SymPy 1.14 and python-flint 0.8. With an optional `--fast-library` compiled from the [previous exact CRT kernel](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-final/README.md#replaying), each resultant is instead reconstructed under the same strict integer coefficient bound, with exact prime-residue and integer specialization cross-checks. Both routes calculate the same ordinary resultant, neither uses empirical rational reconstruction. Positional phase IDs allow one chart per process.

The [shared Lean scalar companion](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonMixedShareRank.lean) does not formalize all rooted ingress or the exact polynomial calculations. Together with the five star phases, this excludes every **mixed chronological opening with one shared D**, but not the disjoint mixed case or the cases with just one later D at both ends. See the [scope ledger](LEDGER.md); the general 10–11 stage interval is unchanged.

The publication audit independently re-ran the complete exact elimination. The scalar Lean companion is a draft and was not kernel-checked for this release.
