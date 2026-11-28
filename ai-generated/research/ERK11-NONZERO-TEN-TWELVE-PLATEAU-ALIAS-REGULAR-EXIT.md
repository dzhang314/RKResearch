# The regular dormant opposite-plateau chart is empty

**Scope.** In the all-live half-clock, two-carrier, both-new ERK11 equality problem, take ten nonzero-first-pool labels, twelve active rows, both full plateau pairs and the dormant physical 9 at \(\zeta=d\). In the [regular sparse chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md) **all six width pivots are live**: the two initial slopes, the two fixed moment-block determinants, and the two raw affine slopes. This entire regular chart is impossible over ordered fields. The same follows for its reflected \(\zeta=a\) chart. This does **not** exclude the union of the six exceptional masks, the endpoint-only aliases, or any unaliased center. More generally the field arithmetic applies over characteristic zero with the inherited mixed-moment guards supplied explicitly. There is no unrestricted stage-bound change.

## 1. The full list of regular width factors

The exact \(d\)-resultant of the actual reciprocal width equation \(\mathcal D\) and the independent sparse first-pool projectivity mark \(\Pi\) has degree 1060 in \(a\). Its factor degrees, with multiplicity, are \(1^{16},3^3,8^8,12^6,12^7,815^1\). This is a necessary projection, not a statement that its roots are possible tableaux.

The [paid two-row moment proof](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-DEGREE815-EXIT.md) excludes the sole irreducible degree-815 factor. It uses an exact simple prime-29 place where \(a\) reduces to 6 and the **whole** width/line gcd in \(d\) is \(d-9\). All subsequent guard denominators are live there; the ordinary two-row left plateau compatibility at the known first response has residue 17, not zero. This excludes every characteristic-zero conjugate on that irreducible factor, not only one chosen ordinary width.

For clarity, the preceding degree-815 proof uses the scalar divided-difference relation to reconstruct the common first/second pool scale; the new contradiction is the literal two-row ordinary moment identity, not another proportionality assertion about the already proportional two \(Q\) lines.

## 2. The five smaller factors and their exact departures

The single degree-one factor fixes \(a=0\), contrary to the calibrated front. For every other smaller irreducible factor in the exact projection, the following table gives a literal root of the width and line equations in its exact rational width field. It is also the **only** common \(d\) root in any extension of that width field.

| Exact \(a\)-factor degree and multiplicity | Its exact \(d\)-fiber satisfies | Residue component degree for the residual unit check (prime 17) |
|---|---|---:|
| 3, multiplicity 3 | \(d=1\), forbidden because \(b=1-d\ne0\) | 3 |
| 8, multiplicity 8 | Left raw affine slope \(g_1^L=0\) | 7 |
| 12, multiplicity 6 | Left raw initial slope \(\ell_0=0\) | 4 |
| 12, multiplicity 7 | Right raw initial slope \(r_0=0\) | 2 |

To verify each line, work over the exact field \(\mathbb Q[a]/H(a)\) of the corresponding factor. Intersect the width equation with that indicated mask and the true line equation to obtain a monic linear factor \(d-d_0\). The replay explicitly evaluates all three original polynomials at \(d_0\) and finds zero. Divide \(\mathcal D,\Pi\) **exactly** by \(d-d_0\) before any reduction. If another common root existed in characteristic zero, it would solve both deflated equations. The chosen residue component is separable, with the width degree preserved, so irreducibility and the simple-prime lift allow embedding any root of the exact \(H\) into that place. All deflated coefficients used there have unit rational denominators, and the deflated width polynomial retains its degree in \(d\). Thus a putative other root of the deflated width equation is integral. The two entire deflated residues then have unit gcd, contradiction. This checks all alternative \(d\) candidates without assuming a common root could not reduce onto the masked root.

The two initial-slope departures and the affine-slope departure migrate to the already named **exceptional masks**. They are not infeasible width pairs by this argument. An exceptional tableau could also have a different \(d\) for the same \(a\), since such a tableau is not required to satisfy the regular line equation \(\Pi=0\). The table only removes width factors from the regular branch in which \(\Pi\) was earned.

The exact small-width replay uses the archived factor coefficient checkpoint from the same exact resultant, with the degree-815 companion optionally recomputing it. The regular branch is exhausted by the six factor components above. No proof step divides by a zero mask or extrapolates a residue statement to any different alias.

The two replay scripts in [the companion directory](erk11-plateau-alias-regular-exit) take the [archived exact regular width factors](erk11-sparse-plateau-alias-eliminant/optional-exact-factor-data/exact-regular-width-factors-d.json) as their positional input. The degree-815 script also accepts `--full` to recompute and match the factor exactly. The [Lean scalar gate](../lean/RKCert/ReviewedNative/ERK11PlateauAliasPaidPairGate.lean) checked on all four targeted versions.
