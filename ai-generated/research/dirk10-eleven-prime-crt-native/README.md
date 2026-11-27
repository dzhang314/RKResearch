# One native eleven-stage DIRK10 certificate for 32 prime characteristics and 59²

The [literal CRT tableau](tableau-crt.json) is a single 11-stage lower triangular matrix and weight vector over \(\mathbb Z/M\mathbb Z\), with
\[
 M=493171545720458172452176512475299940647302199454377045107793303879169620903625874853054017
  = 59^2\!\!\!\prod_{p\in\mathcal P\setminus\{59\}}\!\!p ,
\]
where
\[
\begin{split}
\mathcal P=\{&59,73,127,149,191,199,283,373,419,461,467,521,563,601,739,761,\\
 &773,811,829,857,863,919,947,967,1031,1171,1193,1319,1409,1481,1487,1499\}.
\end{split}
\]
It has **order ten and a unit normalized eleventh-bush defect**. Consequently the **minimum is eleven** in every nonzero commutative unital ring of characteristic \(n\) dividing \(M\), using the reviewed arbitrary-ring lower bound. This includes each listed field characteristic, characteristic \(3481=59^2\) (for example \(\mathbb Z/3481\mathbb Z\)), and mixed divisors. It does not require the target ring to be a field, ordered, reduced or finite as a set.

This is the finite batch only. There is no claim here of a formal Hensel lift to all powers of any prime. The separate [prime-family construction and mathematical lifting analysis](../dirk10-eleven-prime-families/README.md) records the wider lifting argument. Characteristic zero and any positive characteristic not dividing \(M\) are outside this certificate.

## What was actually checked

The construction merges the 31 other literal primes with the literal \(59^2\) row, which reduces to the original 59 row. The independent [exact audit](audit-crt.log) reads only the literal coefficient array to check all 1,205 ordinary rooted trees **directly modulo \(M\)**. It also checks the reduction of every matrix entry, weight and clock to each of the 32 prior prime fixtures and to the \(59^2\) fixture; the normalized eleventh-bush defect has residue 11 modulo 59 and 1604 modulo 3481. Its inverse modulo the whole composite integer is explicit.

The Lean proof does not assume a field structure on \(\mathbb Z/M\mathbb Z\), does not divide defect grades and does not infer zero equations from a sum of squares modulo \(M\). Instead it uses the reviewed **SufficientFlags** argument, with a generic finite ring projector. The prime and \(59^2\) flags all have the same grades of dimensions
\[
                 0,0,0,1,2,3,5,7,8,9
\]
and pick the same initial nonorigin pivot coordinates. Thus the full flag columns combine by ordinary CRT with no piecewise pivot branches. All actual comparisons are checked in the composite ring: primitive differences, stage and clock projection, mixed product closure, scalar moments and annihilation by the weights. Pivot independence and completeness are not required by the soundness bridge. A separately checked inverse proves the eleventh bush is a unit.

The typed audit exports **RKResearch.Certified.DIRK10PrimeCRT**:

- **paid** and **next_unit**: the literal tableau's rooted order and unit next-bush defect.
- **exists_paid_of_dvd**: both properties for any 11-stage specialization via the canonical ring homomorphism from \(\mathbb Z/M\mathbb Z\) to a ring of characteristic \(n\) with \(n\mid M\).
- **exists_exact_of_dvd**, **exists_exact_prime_in_list**, **exists_exact_char_59**, **exists_exact_char_3481**: the exact order-ten forms.
- **minimum_stages_floor**: at least eleven stages, from the reviewed field lower bound transported via a maximal residue field to every nonzero commutative ring.

The [typed audit](typed-4.36.0.log) lists only the standard axioms propext, Classical.choice, Quot.sound. The complete checks ran in Lean/Mathlib **4.36.0**. The modulus and factor/divisibility arithmetic alone also passed core Lean 4.34.1, 4.35.0 and 4.37.0-rc1; these are not claims about other full Mathlib pairings.

## Reproduce the literal data and proof

From ai-generated:

    folder=research/dirk10-eleven-prime-crt-native
    inputs=research/dirk10-eleven-prime-families
    tmp=$(mktemp -d)
    python3 -B "$folder/audit_crt.py"
    python3 -B "$folder/prepare.py" --seeds "$inputs/seeds.json" --literals "$inputs/tableaux.json" --out "$tmp"
    cmp "$tmp/tableau-crt.json" "$folder/tableau-crt.json"
    python3 -B "$folder/generate.py" "$folder/tableau-crt.json" "$tmp/lean"
    for f in "$tmp"/lean/*.lean; do cmp "$f" "lean/RKCert/ReviewedNative/$(basename "$f")"; done
    sha256sum -c "$folder/sources.sha256"
    sha256sum -c "$folder/dependencies.sha256"

From ai-generated/lean in the pinned environment:

    lake build +RKCert.ReviewedNative.DIRK10PrimeCRT
    lake env lean AuditDIRK10PrimeCRT.lean

The Python regeneration and independent literal audit require only the standard library. The generated flags are candidate data, not a trusted checker or oracle.
