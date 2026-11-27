# Lean endpoint: rational ERK order nine in fourteen stages

The [literal fourteen-stage rational tableau](../erk9-fourteen-rational-triple/README.md) is certified directly by the kernel against the reviewed rooted-tree order predicate. It reduces the rational upper bound from 15 to 14, and the certificate applies to every characteristic-zero field. It does not change the general real-algebraic **order-ten** lower/upper interval of 14–15.

The theorem **RKResearch.Certified.ERK9RationalFourteen.order_nine** holds in every commutative ring with an inverse for \(D=3941167085856000\). The literal strict-lower-triangular proof and the size-ten bush give **exists_exact_of_unit** for every **nontrivial** such ring, and **exists_exact_charZero** and **exists_exact_rational** give the exact result over characteristic-zero fields and the rationals. The verified normalized bush relation is
\[
           2160\bigl(10\,\mathbf b\boldsymbol\Phi(\operatorname{Bush}_{10})-1\bigr)=-1 ,
\]
so the exact next-order failure needs no positivity, characteristic zero, or separate nonvanishing coefficient once \(D\) is invertible. The tableau has extra denominator primes \(11,13,19,47\), so the result is not a uniform factorial-only ring bound.

The generated disk data are untrusted until checked. The normalized integer cache has 274 profiles, 132 stage actions, and 586 compatible joins. The native checker verifies the leaf, every compatible join and action, and all output payments with kernel reduction. The reviewed ERKNormalizedVectorCover induction then covers every presentation of every rooted tree through nine. The ten-vertex bush identity is kernel-checked separately using its actual scalar row sums. The integer-to-ring proof uses the reviewed homogeneity and scaling bridge. The typed audit reports only standard axioms: propext, Classical.choice, and Quot.sound.

From the ai-generated/lean directory with the pinned Mathlib environment:

    lake build +RKCert.ReviewedNative.ERK9RationalFourteen
    lake env lean AuditERK9RationalFourteen.lean

From ai-generated, regenerate the data and check blocks with:

    folder=research/erk9-fourteen-native-upper
    dst=$(mktemp -d)
    python3 "$folder/generate_lean.py" --source research/erk9-fourteen-rational-triple/tableau.json --emit "$dst" --modules "$dst/modules.txt"
    cmp "$folder/modules.txt" "$dst/modules.txt"
    for f in "$dst"/ERK9RationalFourteen*.lean; do cmp "$f" "lean/RKCert/ReviewedNative/$(basename "$f")"; done
    sha256sum -c "$folder/sources.sha256"

Source generation and direct kernel checking were replayed with Lean/Mathlib 4.36.0. Other release-matched Mathlib pairs were not run here.
