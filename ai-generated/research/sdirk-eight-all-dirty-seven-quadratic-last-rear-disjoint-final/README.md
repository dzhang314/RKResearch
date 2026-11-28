# Last two disjoint-prefix charts at the unique-singleton seven-clock boundary

Under the [seven-clock unique-singleton and disjoint-prefix hypotheses](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-two-star/README.md), we exclude the true forward A2 (the one observed forward D is physical row 2) against both true rear arithmetic phases, A2 and A3. This is a characteristic-zero field result without ordering, signs, root-splitting or mirrored tableau symmetry. Together with the [other seven disjoint charts](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-more/README.md) and the two overlap packets, this finishes the **exactly one singleton physical endpoint** branch. See the [standalone topology ledger](SYNTHESIS.md).

## Same paid equations, no new pivot

Use the [three singleton reads and two actual D equations](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-two-star/README.md#three-singleton-reads-and-two-original-weighted-d-equations), with \(s=2d\) at the true front A2, \(e=-l_0/l_1\) the recovered third D, and a genuine rear arithmetic pair at D offset \(H-e\). When the rear D is the second row, its reflected S clock is \(2(H-e)\); when the rear D is the third row, its S clock is \((H-e)/2\). The actual tap formulas are different and used separately. Keep the inherited nonzero clocks, \(L_4\) on anchors, \(\ell_1\), paid residual values, and graph-off guards. The exact integer rows \(E,X,Y\) use only these true denominator and rational content factors. The leading coefficient in \(d\) is **not** assumed to survive at a candidate \(H\).

The two ordinary resultant pairs and their irreducible common-\(H\) factor profiles after true \(H\)-guard removal are:

| True rear | Raw degrees | Guard-trimmed degrees | Factors \((\mathrm{degree},\mathrm{multiplicity})\) |
| --- | --- | --- | --- |
| A2 | 2937,3253 | 2077,2305 | (24,1),(36,2),(4,8),(4,9) twice,(2,9),(3,20),(27,20),(18,20),(12,21) |
| A3 | 2937,1599 | 2083,1185 | (36,2),(2,3),(4,3) three times,(3,10),(12,10),(18,10),(27,10) |

The [fixed-place check](../sdirk-eight-all-dirty-seven-quadratic-last-rear-disjoint-more/README.md#projections-and-exact-guard-census) is identical in form to the other disjoint packets: trim the exact monic \(E\) in the indicated number field by literal guards, or keep one positive raw \(d\)-degree in the small degree-two field. Then a prescribed unramified simple good place and joint unit gcd exclude all \(d\) in an algebraic closure, not just the prime-field roots. This neither imposes positivity nor transfers a stage lower bound to that finite characteristic.

## Deterministic exact reconstruction, not a modular search

Take \(A,B\in\mathbb Z[H,d]\), with degrees \((h_A,a),(h_B,b)\) in \((H,d)\), for either pair \((E,X)\) or \((E,Y)\). The Sylvester determinant over \(\mathbb Z[H]\) has degree at most \(h_A b+h_B a\). For each block polynomial sum the absolute **integer** coefficients within each \(d\)-coefficient row as \(s_i\), and form \(U=1+\lfloor\sqrt{\sum s_i^2}\rfloor\). On \(|H|=1\), every Sylvester row from that polynomial has Euclidean norm less than or equal to \(U\). Hadamard's determinant inequality and the Cauchy coefficient formula show that each projected integer coefficient has absolute value at most \(U_A^bU_B^a\). The exact code asserts a CRT modulus **strictly exceeding twice this explicit bound** and takes the unique centered integer representative. This is a priori reconstruction, not stabilization under a few primes.

All primes are checked, distinct, and skip degree drops in the eliminated variable globally. The wheel-only path uses each ordinary modular FLINT resultant. The optional C kernel instead evaluates both rows at enough distinct \(H\) points where their individual leading \(d\)-coefficients are nonzero, obtains full-degree univariate resultants and interpolates through more points than the degree bound. Thus it agrees with the same modular Sylvester determinant even when other specialization points drop in degree. The first prime of each accelerated projection cross-checks against the independent multivariate implementation. Further direct exact specialized integer resultants are redundant orientation/implementation checks; they are not the reason CRT is exact. No modular field claim is substituted for a characteristic-zero proof.

## Replaying

With SymPy 1.14 and python-flint 0.8, run `SYMPY_GROUND_TYPES=flint python check_final_disjoint.py`. Add `--rear A2` or `--rear A3` for the single complete branch. The default needs no compiler (modular ordinary FLINT); it takes several minutes. An optional bounded-memory Linux LP64 accelerator targets the matching FLINT wheel ABI:

```sh
FLINT_SO=$(python -c 'import flint; from pathlib import Path; print(next((Path(flint.__file__).resolve().parent.parent/"python_flint.libs").glob("libflint-*.so*")))')
cc -O3 -shared -fPIC flint_multipoint.c "$FLINT_SO" -Wl,-rpath,"$(dirname "$FLINT_SO")" -o /tmp/rk-sdirk8-flint-multipoint.so
SYMPY_GROUND_TYPES=flint python check_final_disjoint.py --fast-library /tmp/rk-sdirk8-flint-multipoint.so
```

The solver only writes diagnostics, no coefficient cache is needed. The [candidate Lean scalar clearing lemma](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSDisjointRearStar.lean) applies before either arithmetic projection and is shared; the projection, place checks and synthesis are not all in Lean. Both-singleton endpoint methods and the general 10–11 stage interval remain separate.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
