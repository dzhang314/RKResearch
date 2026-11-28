# Shared extra rear D label is impossible

In strict ten-stage SDIRK of classical order at least eight over a characteristic-zero field, suppose all literal quadratic defects are nonzero, there are exactly seven distinct clocks and precisely one physical endpoint is at a singleton label. Orient the singleton first. The [scoped ledger](../sdirk-eight-all-dirty-seven-quadratic-two-s-dss-arithmetic-new-a2-final/LEDGER.md) leaves the first three stages with two S and one D, and the reflected first three with two D and one S. Here we exclude the case where the one forward D clock equals the **other** observed rear D clock, not the terminal clock. The [terminal-overlap packet](../sdirk-eight-all-dirty-seven-quadratic-last-rear-terminal-overlap/README.md) excludes the terminal overlap separately. Two singleton endpoints and distinct-prefix D labels are not addressed here.

## Actual readings and full-rank recovery

Use the [same physical normalization, phase table and paid affine factor](../sdirk-eight-all-dirty-seven-quadratic-last-rear-terminal-overlap/README.md#literal-pair-data-and-true-affine-factor) with first singleton \(0\), terminal D \(H\), observed nonterminal rear D \(d\), and forward D now \(d\). The other known singleton clocks are \(s,t_s\), and \(e\) is the recovered third D. All three phases A2, A3, star for each forward/rear pair remain. For the star, both actual orders give the same pair comparisons; they are not arbitrary row reorderings. Let \(f_d,f_s\) be original forward paid defects, and \(\rho_d,\rho_t\ne0\) their reflected counterparts at \(d,t_s\). The reflected terminal defect is \(1/2\). The paid affine recovery uses no sign, splitting or residual-sum assumptions, and gives the same quadratic graph \(R\) and row \(E=0\).

The true reflected scale is \(\lambda=R(t_s)/\rho_t\). Both occurrences at \(d\) are now paid, and their distinct actual residuals \(f_d,\lambda\rho_d\) give \(\beta=B\lambda=-L_4(d)/(f_d\rho_d)\). In the normalized field write \(\lambda A_2=T_0+\lambda T_1\). The unique quadratic rows are recovered by these three distinct clock evaluations:
\[
\begin{array}{c|cc}
y&T_0&T_1\\\hline
0&-\beta/2&2 L_4(0)\\
d&-\beta f_d&-\beta\rho_d\\
H&2 L_4(H)&-\beta/2 .
\end{array}
\]
The forward and rear singleton tests give exactly the same forms \(X,Y\) as in [the terminal packet](../sdirk-eight-all-dirty-seven-quadratic-last-rear-terminal-overlap/README.md#actual-overlap-and-two-paid-singleton-equations), but with these \(T_0,T_1\). This uses actual traces only at consumed rows. A shared root between \(R\) and the D nodal cubic, the actual rank of a later fourth read, and nonzero trapezoid coefficients beyond the actual pair are not assumed.

## Exhaustive projection and exact guard removal

Build the three cleared integer rows and audit their allowed denominator/guard factors exactly as in the terminal packet. Project \(E,X\) and \(E,Y\) separately in \(d\), preserving any candidates in a leading drop, and take the gcd of their true \(H\)-guard-trimmed projections. Its irreducible factor degrees with multiplicities are:

| Front / rear | Projected degrees | Factors \((\mathrm{degree},\mathrm{multiplicity})\) |
| --- | --- | --- |
| A2 / A2 | 570,478 | (2,1),(36,1),(3,2),(12,2),(18,2),(27,2) |
| A2 / A3 | 570,478 | (4,1),(36,1),(3,2),(12,2),(18,2),(27,2) |
| A2 / star | 480,388 | (36,1),(3,2),(12,2),(18,2),(27,2) |
| A3 / A2 | 324,295 | (18,1),(4,1),(18,2) |
| A3 / A3 | 324,295 | (18,1),(2,1),(18,2) |
| A3 / star | 261,232 | (18,1),(18,2) |
| star / A2 | 270,241 | (6,3),(9,4) |
| star / A3 | 268,241 | (6,3),(9,4) |
| star / star | 197,169 | (2,1),(6,3),(9,4) |

For each of the 32 fibres the following operations apply. The three degree-two fibres use the raw rows. In all others form the exact monic \(E\)-row over the rational \(H\) number field. Remove only factors dividing the true nonzero front pair guards; for the two degree-four fibres use instead \(s-t_s\) and \(M_3(0)\); for the slope fibres use the exact common factor of the two true nonzero affine slopes \(F_*'\) and \(L'\). In particular the slope filter does **not** assume these slopes are units modulo a selected prime. The exact gcd/quotients in the abstract \(H\)-field preserve every actual \(d\). The resulting monic degrees are recorded and asserted before any finite calculation.

For each factor, a fixed prime \(p\) and residue \(h\) is checked to be a simple root of the full-degree \(H\) factor. This gives an embedding of that number field into \(\mathbb Q_p\). For the trimmed \(E\), every coefficient of its \(H\)-power representation is checked \(p\)-integral; monicity then implies that every corresponding algebraic \(d\) is integral. In the raw degree-two cases at least one positive-degree row keeps its exact fibre degree, so its leading coefficient is a \(p\)-adic unit and it supplies the same integrality conclusion. In each case the relevant reduced rows have joint gcd one. An actual \(d\), transported under an extension of that field embedding into \(\overline{\mathbb Q}_p\), would reduce to a common root in \(\overline{\mathbb F}_p\). Thus **all embeddings** of the characteristic-zero candidate are ruled out, not just rational ones and not just roots individually found in the prime field. No claim about an arbitrary method in characteristic \(p\) follows.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_extra_overlap.py` with SymPy 1.14 and python-flint 0.8. The relative sibling packet supplies the shared literal projection. The native scalar companion and typed audit are shared with that sibling because the clearing identities are unchanged after moving the overlap from \(H\) to \(d\). The topology and exact polynomial contradiction are paper and exact Python, not all rooted ingress in Lean. The numerical interval is unchanged.
