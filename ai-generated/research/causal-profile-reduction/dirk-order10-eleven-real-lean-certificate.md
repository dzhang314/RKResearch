# Kernel-checked real eleven-stage DIRK10 endpoint

The [exact algebraic construction and independent full tree replay](dirk-order10-eleven-real-algebraic.md) now also have a complete reviewed native Lean proof. The two typed theorems are:

- There is a lower triangular real eleven-stage tableau with HasOrder 10 and not HasOrder 11.
- Every lower triangular real tableau with HasOrder 10 has at least eleven stages.

Both depend only on propext, Classical.choice and Quot.sound. No compiler-assisted decision axiom, postulate about a fixture, or source-level sorry is used. The [typed audit](dirk-order10-eleven-real-lean-audit.txt) was replayed on Lean 4.36.0 with the repository's pinned Mathlib. That is the tested native toolchain.

The [exact coefficient table](dirk-order10-eleven-real-coefficients.json) records the nested rational basis \(r_9^i r_8^j k^\ell\), with \(i<2,j<3,\ell<3\), and the three monic moduli. The [decimal display](dirk-order10-eleven-real-decimal.csv) is only a 15-digit view, not evidence of exact order.

## Arithmetic and proof structure

The Python construction generates the tableau, but the kernel need not trust that construction. The three coordinates in the native data are scaled to integral monic relations: \(25k\) at the base, and a common positive integer times \(r_8,r_9\) at the subsequent two levels. A coefficient is an integer polynomial of degree at most \(2,2,1\) in the respective variables over a positive integer denominator. Equality is tested by **cross multiplication** of exact integer numerators. The interpretation theorem proves that the three integer reductions preserve the relevant operations under the monic relations. Separate exact rational sign changes and the reviewed real Horner root lemma supply those roots with disjoint brackets.

The grade submodules are spans of stored vector bases of dimensions \(0,0,0,1,2,3,5,8,9,10\). The early bases contain the cubic defect, its carrier and clock shifts, and the grade-six terminal primitive. At grades 7, 8 and 9 the generated bases are sparse weighted-null vectors using the last 3, 2 and 1 physical active coordinates as elimination columns. The proof need not trust those descriptions: every membership witness and weighted zero read is checked on its literal entries.

The small kernel receipts verify all paid stage advances, clock advances, coordinate products, monomial primitive residuals, output silences and ordinary moments. A denominator-free structural induction on the reviewed normalized trees transports these exact grade tests to full order. The 11-vertex star has a checked residual inverse. The lower bound is the existing reviewed rank theorem imported unchanged.

## Sequential rebuild

The [source manifest](dirk-order10-eleven-real-lean-manifest.txt) lists the new modules in build order, apart from pre-existing repository dependencies. From the ai-generated/lean directory, with the pinned toolchain and the repository's normal dependencies available:

    lake build +RKCert.ReviewedNative.DIRKOrderTenSaturation:olean \
      +RKCert.ReviewedNative.PolynomialBracket:olean
    mkdir -p .lake/build/lib/lean/RKCert/ReviewedNative
    while IFS= read -r path; do
      file=$(printf '%s' "$path" | cut -d/ -f3-)
      case "$file" in Audit*) continue;; esac
      stem=$(printf '%s' "$file" | sed 's/[.]lean$//')
      lake env lean -o ".lake/build/lib/lean/$stem.olean" "$file" || exit
    done < ../research/causal-profile-reduction/dirk-order10-eleven-real-lean-manifest.txt
    lake env lean AuditDIRKOrderTenElevenReal.lean

Use one or at most two concurrent proof workers. The highest stage-action bands are deliberately broken into 12 small modules; merging them into a single elaboration unit can exhaust memory. The split receipts, not outputs of any rejected unsplit check, are the evidence. With enough memory, the ordinary targeted Lake build of the final module also resolves its transitive imports.
