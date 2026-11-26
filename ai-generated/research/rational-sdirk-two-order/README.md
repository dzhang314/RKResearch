# Exact rational strict SDIRK of orders eight through ten

| Order | Physical stages | Common diagonal | Cleared next-bush defect |
|---:|---:|---:|---:|
| 8 | 13 | 1/4 | 1245689/77486080 |
| 9 | 19 | 1/7 | 87763/1296540 |
| 10 | 21 | 1/8 | 2432737/143649669120 |

The arrays in `tableau-8.json`, `tableau-9.json`, and `tableau-10.json` give the explicit rational coefficients and output weights. Run `python check.py .` from this directory to verify triangularity, the common nonzero diagonal, every order equation, and the next-bush defects using only Python's standard library. The test counts through the target order are 200, 486, and 1,205.

The [construction](TWO-ORDER-NEWTON-TAIL.md) raises order by two while keeping old stage equations and the common diagonal. The [rational specialization](RATIONAL-ENDPOINTS-AND-ROTATING-ANCHOR.md) gives the arithmetic and explains physical receiver merges. Run the separate generator with `--repo-root` pointing to this repository to reconstruct the arrays from the earlier seed methods.

These rational upper bounds do not improve the real-algebraic upper bounds or certify new Lean theorems.
