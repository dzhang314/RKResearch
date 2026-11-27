# Lean certificate: exact order ten in twelve rational DIRK stages

The reviewed kernel checks the [literal rational tableau](../dirk10-twelve-rational-three-ports/README.md). The main declarations are in **RKResearch.Certified.DIRK10RationalTwelve**:

- **order_ten** for the literal coefficients over every commutative ring inverting \(D=101588047290852467338246934187117072000\).
- **bush_defect**, the cleared eleventh-bush equation \(2488320(11\,\mathbf b\boldsymbol\Phi_{\mathrm{bush}_{11}}-1)=1\).
- **exists_exact_of_unit**, including lower triangularity and failure of order eleven in every **nontrivial** ring inverting \(D\).
- **exists_exact_charZero** and **exists_exact_rational**, with the same ordinary DIRK statement over any characteristic-zero field and over \(\mathbb Q\). **rational_diagonals** checks two unequal nonzero diagonal entries.

These declarations certify the **upper** endpoint. The separate [rational lower proof](../causal-profile-reduction/dirk-order10-rational-lower-twelve.md) proves optimality mathematically. No unrelated real-algebraic lower bound is strengthened.

The data generator supplies untrusted scaled integer Gram tables. Each multiplier identity, grade recurrence, branch matrix product, and zero energy is checked by the kernel. The reusable **RootedTreeGram** result identifies these energies as sums of squares of the reviewed rooted-tree defects over the integers and then transfers to the coefficient ring. No trusted numerical oracle, native decision axiom, interval proof, or placeholder is used. The [typed audit](typed-4.36.0.log) lists only propext, Classical.choice, and Quot.sound.

## Replay

From ai-generated, regenerate the arithmetic module and check source provenance:

    dir=research/dirk10-twelve-native-upper
    tmp=$(mktemp -d)
    python3 -B "$dir/generate_lean.py" research/dirk10-twelve-rational-three-ports/tableau.json --graded > "$tmp/DIRK10RationalTwelveGram.lean"
    cmp "$tmp/DIRK10RationalTwelveGram.lean" lean/RKCert/ReviewedNative/DIRK10RationalTwelveGram.lean
    sha256sum -c "$dir/sources.sha256"

From ai-generated/lean, use the pinned environment:

    lake build +RKCert.ReviewedNative.DIRK10RationalTwelve
    lake env lean AuditDIRK10RationalTwelve.lean

Direct source builds and the typed audit passed on Lean/Mathlib **4.36.0**. The local two-module build timings are in the two build receipts. Other release-matched Mathlib versions are not asserted by this receipt.
