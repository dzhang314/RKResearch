# Regular star-front ordinary-arithmetic-rear closure for actual silent 6 or 7

No strict ten-stage SDIRK8 over a characteristic-zero field occurs in the following chart. Physical first is ordinarily silent and is the **sole nonzero quadratic-defect row**. Eight ordinary active clocks are distinct. The additionally ordinarily silent physical row \(\zeta=6\) or \(7\) has its own nonzero reverse read at a distinct ninth site. Its nine-site reverse numerator is constant nonzero, and the genuine mixed quintic profile is regular at the actual fourth anchor, with both early quartic values nonzero. The literal front is star and the physical ordinary rear is arithmetic. The other silent placements, arithmetic front, and unrestricted **10–11** interval are not resolved by this packet.

## Independent true tail and ordinary fifth

Use the [regular literal model](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md#common-true-coefficient-model) with fixed ordinary pegs \(a=\gamma A_0,b=\gamma B_0,q=\gamma s,x=1-\gamma\). The actual ordinary penultimate and eighth are \(c=x-\gamma u,d=x-2\gamma u\). The [four-peg pivot](../sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed/README.md#fixed-known-peg-pivot-not-a-residue-assumption) gives a five-peg determinant \(N(v)\) proportional to the true missing quartic in the prospective peg \(x-\gamma v\). In particular \(N(u)=N(2u)=0\), the leading coefficient \(R_4=[v^4]N\) is nonzero, and \(R_0=N(0)\ne0\) because the terminal is already a known ordinary peg. This uses only scalar precision **seven**.

Put
\[
 D_1(v)=\sum_{j=1}^4 (2^j-1)R_j v^{j-1},
 \qquad
 D_0(v)=\sum_{j=0}^4 (2-2^j)R_j v^j.
\]
The first is the direct second synthetic remainder:
\(N(2v)-N(v)=v D_1(v)\). Thus \(D_1(u)=0\) follows from the two **actual distinct** rear clocks with \(\gamma u\ne0\); it need not be inferred from residue distinctness. The second satisfies \(N(v)=D_0(v)+vD_1(v)\), so \(D_0(u)=0\). The true tail relation in the [ordinary arithmetic chart](../sdirk-eight-silent-one-eight-reverse-live-regular-finite/README.md#rear-arithmetic-exact-nested-resultant-projections) is also a paid degree-six equation \(F(u)=0\) after the known factors \(u^2,\gamma,L_4(a),L_4(b)\) are removed. This does not substitute an ordinary weight at the actual silent stage.

Take the exact resultants of \((D_1,D_0)\) and \((D_1,F)\) in \(v\), and call their guarded rational integer representatives \(A_*,B_*\). The raw \((s,\gamma)\)-degrees are \((55,168),(56,177)\). Remove powers of \(\gamma\) (16 and 15) and one true normalized degree-five profile leading coefficient in each; the outputs have degrees \((53,146),(54,156)\). In the first output there is additionally a factor with degrees \((5,14)\) that exactly divides the true missing-quartic leading coefficient \(R_4\); removing it gives \(A_*\) of degrees \((48,132)\). The code checks the exact divisibility, not just a modular shared leading root. Both projected scalar equations remain necessary if any projected input drops leading degree at a candidate.

Physical fifth is actually ordinary and is distinct from both actual tail sites. Deleting their two true linear factors preserves this fifth as a root of the remaining monic quadratic. In particular it remains a root of the complete \(N(x/\gamma-Y)\), where \(Y=c_5/\gamma\), and of the [actual literal fifth equation](../sdirk-eight-silent-one-eight-reverse-live-star-silent-eighth-closed/README.md#independent-literal-fifth-and-two-exact-outer-projections). Its independent exact fourth projection is therefore necessary. Apart from a squared genuine nonzero regular anchor factor, the rational fifth projection is the product of \(J_{11},J_{14}\), whose \((s,\gamma)\)-degrees are \((11,23),(14,46)\). The code reuses the exact product and anchor checks. This is not a fifth-stage ordinary assumption for a silent physical fifth.

## Complete exact diagonal and fourth fibres

Use the two rational outer resultants \(\operatorname{Res}_s(A_*,J_d)\) for \(d=11,14\), and keep \(B_*\) as an independent true tail condition in every fibre.

| \(d\) | Exact outer degree | Exact \(\gamma\)-valuation | Coefficient bound bits | CRT primes | Exact factors | Full fourth-fibre components |
|---|---:|---:|---:|---:|---:|---:|
| 11 | 2556 | 271 | 7207 | 121 | 11 | 52 |
| 14 | 4056 | 470 | 11126 | 186 | 10 | 57 |

The Sylvester coefficient bound is the product of the row \(\ell^1\) norms. Integer CRT exceeds twice that bound with both whole \(s\)-degrees preserved at every prime. The optional existing LP64 FLINT interpolator selects enough good \(\gamma\)-points to attain the full degree bound; each first entire prime image is compared to the ordinary resultant, and the final polynomial is checked at a second independent prime. The ordinary resultant remains a fallback. After removing the exact strict-diagonal power and content, the full product of retained exact diagonal factors is checked.

For each exact diagonal factor, use its entire monic algebra and all residue factors at \(1129\). In six large-factor cases one of the three unmodified fourth equations preserves its full degree with a leading unit in every local component. In the other cases the exhaustive selected fourth basis is the exact specialization of \(J_d\) in the monic diagonal algebra. This includes degree drops to \(10,12,13\); none is interpreted as a missing candidate. Normalize by a checked exact unit. For the recorded exact forbidden supports, a monic divisor \(D(s)\) is accepted only after verifying that it divides the exact fourth equation and divides the indicated power of \(R_4(s)\) in the entire monic diagonal algebra. Thus an actual fourth root must remain in the quotient even where a residue leading coefficient or pivot vanishes. CRT guesses make no inference before these identities pass.

The complete monic fourth inputs remain integral at the selected place. For each of the **109** reduced components the fourth polynomial is coprime to the joint equations \(A_*,B_*,J_d\), so no actual fourth clock remains. This excludes the chart before the later clock and four paid linear chronology checks become necessary. No division by \(u-1\) or \(u-2\) occurs; the proof independently covers those gaps for \(\zeta=6,7\). The [fixed-gap packet](../sdirk-eight-silent-one-eight-reverse-live-star-arithmetic-fixed-gaps/README.md) separately covers both singular gaps even when \(\zeta=5\).

## Replay and native scope

Install **sympy==1.14.0** and **python-flint==0.9.0** and run **python3 check_star_arithmetic67.py** with the declared sibling source directories. The optional C helper is the same bounded-degree interpolation as the arithmetic-front silent-eighth proof; set **RK_DISABLE_FAST_CRT=1** to use the slower exact-resultant implementation without compiling it.

The [native scalar lemmas](../../lean/RKCert/ReviewedNative/SDIRK8OrdinaryArithmeticRearQuartic.lean), checked on Lean/Mathlib 4.36.0, give the second synthetic remainder, preservation of the actual ordinary fifth after two genuine deletions, nonvanishing of the actual silent-clock affine denominator, and the two cleared backward reads with the true ordinary eighth weight. The fixed-gap packet checks the actual suffix determinant separately. The exact arithmetic projections and complete local verification are source-level.
