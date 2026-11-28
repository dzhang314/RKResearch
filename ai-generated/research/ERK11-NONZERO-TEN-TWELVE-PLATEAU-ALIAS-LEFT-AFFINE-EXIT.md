# The dormant plateau alias has no left affine pivot loss

**Scope.** In the [sparse plateau-alias chart](ERK11-NONZERO-TEN-TWELVE-SPARSE-PLATEAU-ALIAS-ELIMINANT.md) with \(q=10,n=12\), both plateau pairs full, and sole dormant physical 9 at \(\zeta=d\), this excludes the entire **left raw affine slope** mask. Use the prior left initial-slope and left fixed moment exclusions and the ordered geometric guards. The new elimination is characteristic zero with those guards supplied. It does not assume any right affine pivot, or change the unrestricted stage interval. Reflection transfers to the opposite plateau orientation.

## 1. The true mask needs both raw coefficients

The necessary four-row determinant in the true left calibrated hull parameter \(t\) is
\[
 g_0+t g_1=0.
\]
It is the determinant of the three scalar moment rows and the actual grade-five outer equation \([L_8,R_9]=0\) in the sparse coefficient coordinates. It follows from the actual nonzero first/second-pool coefficient vector, whether or not a numerator profile would be identifiable. Thus the mask \(g_1=0\) forces \(g_0=0\) as well. Use **raw** coefficients: a common polynomial factor may vanish before the affine equation is normalized.

Let \(\Gamma=\gcd(g_0,g_1)\) over \(\mathbb Q[a,d]\), and \(e_i=g_i/\Gamma\). The raw mask implies either \(\Gamma=0\), or \(e_0=e_1=0\). The next two steps examine these separately. The proof does not use a proportionality test on the two second-pool profiles.

## 2. Every common factor forces an already forbidden value

The exact raw bidegrees are \((26,23),(29,27)\). After removing a factor \(a^7\), already live, the bidegree-\((8,12)\) common factor is the product, up to a nonzero rational scalar, of three distinct irreducibles of bidegrees \((0,4),(4,4),(4,4)\). The replay verifies three **bivariate divisibilities**, one for each factor:

1. The factor of bidegree \((0,4)\) divides the left initial slope \(\ell_0\) of the actual derivative direction against \(R_9\). Its zero set is already excluded by the [left slope theorem](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-SLOPE-EXIT.md).
2. One factor of bidegree \((4,4)\) divides the fixed left moment determinant \(\Delta_L\). Its zero set is excluded by the [left fixed-moment theorem](ERK11-NONZERO-TEN-TWELVE-PLATEAU-ALIAS-LEFT-MOMENT-EXIT.md).
3. The other factor of bidegree \((4,4)\) divides \(x_N-a x_D\), using the inherited two-support numerator and denominator
   \[
   x_N=H I_2-C_1I_1,\qquad x_D=H I_1-C_1 I_0.
   \]
   For the actual middle clock \(x=c_8\), the mixed payments give \(x_N=x x_D\), with \(x_D\ne0\) by the strict variance argument. Thus this factor would force the **literal physical** collision \(c_8=a\). That is impossible: the exactly two unequal active pairs are already the two full plateau pairs, and physical 8 is active and a singleton under this census. It cannot supply a third active copy at \(a\).

These divisibilities suffice without computing or fitting the degree-64 projection of the third common factor. In particular an apparent zero-on-zero left outer equation there is not an unresolved flank parameter.

## 3. The reduced double zero has no actual width

The reduced coefficients have bidegrees \((11,11),(14,15)\). Form the two exact \(d\)-resultants with the established reciprocal diagonal \(\mathcal D(a,d)\). The resultant degrees in \(a\) are 231 and 298; their monic common gcd has degree 52 with irreducible degrees and powers \(8^2,12,12^2\), where the superscripts give multiplicity and the two degree-twelve factors are distinct. Over each exact field \(\mathbb Q[a]/F\), the three equations \(\mathcal D=e_0=e_1=0\) have **monic linear gcd in \(d\)**. At those exact roots:

* The degree-eight factor gives \(H=x_D=0\).
* The degree-twelve factor of multiplicity one is the old left-slope field and gives both left derivative slopes zero.
* The degree-twelve factor of multiplicity two gives \(x_D=x_N=0\) and zero Gram variance.

All contradict actual paid guards or the earlier left-slope theorem. This calculation does not infer a candidate from projection ancestry: it verifies the simultaneous width equations and the terminal zero values exactly in each field. It uses no finite-place assumption, no topology for unresolved right pivots, and no additional order on the algebraic width fields themselves.

The standalone replay constructs the raw equations, checks the exact factor and divisibility split, and replays all three exact width fields. The companion Lean checks the raw-vs-reduced scalar split and the inference from the cleared middle-clock equation to a literal alias. The tableau-grade and rational elimination arguments remain mathematical.

The [standalone exact replay](erk11-plateau-alias-left-affine-exit/replay_erk11_plateau_alias_left_affine_pivot.py) and [Lean scalar gates](../lean/RKCert/ReviewedNative/ERK11LeftAffineMaskGate.lean) were independently checked, the latter on all four targeted versions.
