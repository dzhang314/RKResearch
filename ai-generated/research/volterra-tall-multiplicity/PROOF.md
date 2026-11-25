# Physical zero diagonals, nonlinear grade rank, and the reduced tall denominator

Source-only mathematical reconstruction and cross-order check, anchored to RKResearch `7d5ba756fcf30d2e970ec5579bb185079b83384b`. No compiler run. A separate inherited byte-sealed proof of this particular splice was not located. The paid rank step, mixed zero-site predecessor, quadratic nonsingular count, and tall response convention below have reviewed sources; this is not a newly Lean-checked theorem or an improved unrestricted stage table. `SOURCES.sha256` pins the specific inputs.

## 1. What is actually assumed

Let `p≥1`, let `K` be a field, and let `A` be a lower triangular `s×s` matrix with weights `b`, satisfying literal reviewed `HasOrder p A b`: for each finite rooted tree of order at most `p`, its tree factorial times its numerical output is 1. In particular `c=A1`; all integers `1,…,p` are units by the bushy conditions. No node distinctness, realness, output positivity, irreducibility, absence of silent states, diagonalizability, or stage order is assumed. The field may have positive characteristic, in which case that characteristic is greater than `p`. Let `z` be the number of physical diagonal entries of A equal to zero, counted with multiplicity; neither the number of zero nodes nor the number of zero weights is `z`.

Let `E_j` be the nested elementary stage-column span of actual trees of order at most `j+1`, and `F_j` the span of their equal-order normalized differences, as in `GradedColumns`, `GradedDefects`, and `GradedSeparation`. Put `T=DA−AD−A²` with `D=diag(c)`, and for `0≤j<p` put `k_j=1+min(j,p−1−j)`. For consecutive chosen indices `i≤j−2`, reviewed `volterra_treeSpace` sends `E_i` into `F_(i+2)⊆F_j`. Since `j≤p−1`, its grade is affordable. The `k_j` clock columns `1,c,…,c^(k_j−1)` belong to `E_j`. The paid probes `bᵀD^a, 0≤a<k_j`, kill `F_j` since `a+j+1≤p`; on these clock columns their matrix is `(1/(a+h+1))_(a,h<k_j)`. It is invertible by the Cauchy determinant: all denominators and positive index differences are paid nonzero field integers (`2k_j−1≤p`). Thus the fresh columns and `T E_i` are independent subspaces. The triangular diagonal of `T` is `−A_ii²`, so restriction to the `z` zero-diagonal sites is injective on `ker T` by its first-nonzero-coordinate pivot. In particular `dim(E_i∩ker T)≤z`, and

    dim E_j ≥ k_j + dim E_i − z.                            (1)

The initial grade contributes at least `k_j` without a loss. Applying (1) along any nonempty J of grades in `[0,p−1]` whose pairwise differences have magnitude at least two gives

    s ≥ Σ_(j in J) k_j − (|J|−1) z.                         (2)

There is no charge for crossing unselected grades: nest `F_(i+2)` into `F_j`; do not apply T repeatedly at a long gap. Actual kernel intersections can be smaller than `z`; (2) does not constrain their identifiability from clocks and scalar outputs. No support or chronology claim about a canceled clock is used.

## 2. Exact integer optimization of the packets

Write `l=|J|`, `1≤l≤ceil(p/2)`. The maximum of the sum in (2) is

    M(p,l) = floor(l(p+1)/2) − floor(l²/2).                 (3)

Indeed `k_j=(p+1)/2−|j−(p−1)/2|`. For ordered indices `j₁<…<j_l`, pair `j_i` with `j_(l+1−i)` on the outside. The sum of the distances of each pair from the center is at least its spacing `2(l+1−2i)`. Summing the pairs gives `floor(l²/2)`; if `l` is odd and `p` even there is a further half for the unpaired central integer. A block with all gaps two and center at the nearest integer to `(p−1)/2` attains that lower bound, and fits because `2l−1≤p`. This recovers the exact rank-census lower bound at given `z`:

    B_z(p)=max_l [M(p,l)−(l−1)z]
          = z+B_0(p−2z)  if 2z<p,
          = ceil(p/2)   if 2z≥p,
    B_0(u)=ceil(floor((u+1)²/4)/2), for u>0.               (4)

For the middle identity, the adjusted positive grades `k_j−z` form the central tent `k_(j−z)` at order `p−2z`. An optimizing set may include just the positive band if it is nonempty: (3) shows a maximizing set is a centered step-two block, and all positive grades of the better parity can be taken. If no adjusted positive grades exist, a singleton with maximal width is optimal. This is the unmasked (`P=1`) specialization of the reviewed local-nullity cut, with an empty discarded prefix. Exactness here is for the integer rank model, not for full RK attainability.

## 3. Tall bookkeeping and a finite-characteristic refinement

Use normalized *reduced* `R(X)=1+X bᵀ(I−XA)⁻¹1=P/Q`, and denote the unreduced characteristic pair by `N/H`, `H=det(I−XA)`. Since `A` is lower triangular, `deg H=s−z`. Write `H=CQ, N=CP` with `C(0)=1`. Let `r=deg Q` (retained poles **with** multiplicity), `m=deg P`, `c₀=deg C`, and `ν=s−deg N`. The finite adjugate or reviewed Cayley–Hamilton numerator gives `ν≥0`; exactly

    z+r+c₀=s,          m=s−c₀−ν=r+z−ν.                     (5)

Only coprimeness of P and Q identifies r with the actual retained denominator; an arbitrary inflated normalized fraction is not permitted in (5). Put `e=deg(Q/gcd(Q,Q′))` and `μ=r−e`. On combining (2) and (5) we have the unconditionally valid, *measured* split

    l s ≥ M(p,l)+(l−1)(r+c₀) ≥ M(p,l)+(l−1)r.             (6)

Here `r` is an observable, not a function of p forced to be large.

**Paid-prefix extension to any field.** In the reviewed tree model `p!` is a unit. Let `U=Σ_(0≤j≤p) X^j/j!`, `B=Q′/gcd(Q,Q′)`, and `V=Q/gcd(Q,Q′)`. Thus `VQ′=BQ`, `deg V=e`, and `deg B<e` if B is nonzero. For `e=0`, B=0. With `L=QU` we have an *exact polynomial identity*

    V L′−(V+B)L=VQ(U′−U)=−VQ X^p/p!.                      (7)

Paid tall order identifies `L_j=P_j` for all `j≤p`, by the finite geometric expansion. Formula (7) at `k=j+e<p` says: if `L_(j+1),…,L_(j+e+1)` are zero, then `V_e L_j=0`. On the derivative side only these higher coefficients occur; on the right it is the top `V+B` coefficient `V_e≠0` multiplying `L_j`. This is valid for `e=0` as well. If `p>m+e`, the zero window just above m can be propagated to `L_0=1`, a contradiction. Consequently

    p ≤ m+e ≤ m+r.                                          (8)

No unbounded exponential series, `1/(p+1)`, or characteristic-zero hypothesis occurs. The reviewed Lean *fraction-to-derivative-gcd conclusion* at the cited base assumes characteristic zero. Formula (7) is a mathematical extension, not an executed change to that theorem.

Over an algebraic closure in characteristic zero, `e` equals the number of distinct geometric roots. In positive characteristic `q`, it is the number of distinct roots whose multiplicity is **not divisible by q**. For a root α of multiplicity h, differentiation of `(X−α)^h U₀` at its first possible nonzero leading term gives derivative valuation `h−1` if h is nonzero in the field, and at least h otherwise (including the zero derivative). Gcd commutes up to unit with field extension. In particular the unweighted distinct-root *inequality* still follows, but interpreting its exact degree as that full count is false. This distinction can hold for an actual paid tableau: in `F₇` take `s=7`, `A=I+L` for the unit subdiagonal shift, and `b=(5,3,3,5,1,6,6)`. Exactly `R=(1+X+4X²)/(1−X⁷)`, already reduced. The first two moments `bᵀ1=1`, `bᵀA1=4=1/2` certify actual order two, and the next tall coefficient 0 fails `1/6=6`. Here there is one geometric pole of multiplicity seven but `e=0`. The recurrence of A or the cleared polynomial through degree 7 certifies the whole rational fraction. This is not a new small-stage record.

Combining the left inequality of (6) with `r≥p−s+c₀+ν+μ` from (8) gives a compact additional ledger:

    (2l−1)s ≥ M(p,l)+(l−1)(p+2c₀+ν+μ).                     (9)

The two occurrences of canceled degree have specific origins in (5): it costs a unit of nonzero physical diagonal count not retained in r, and a unit of physical numerator degree. Do not charge e.g. an invariant invisible dimension again if it is already represented by those losses.

## 4. What is sharp, unconditionally, and what changes at p≤20

On forgetting all diagonal, cancellation, and pole information, (9) yields

    S_p=max_(1≤l≤ceil(p/2)) ceil((M(p,l)+(l−1)p)/(2l−1)).  (10)

This is *exactly* the projection of the stage inequalities (2), (5), (8) onto the s-axis. Indeed `ceil(p/2)≤S_p≤p` (use singleton, and `M(p,l)≤lp`). At `s=S_p` use `r=p−s, z=2s−p, m=s, e=r, c₀=ν=μ=0`; then all inequalities hold. In fact normalized scalar Padé witnesses with these exact degrees exist. At `p=m+r`, define

    Q_i=(−1)^i binom(r,i)(p−i)!/p!,   P_i=binom(m,i)(p−i)!/p!.

For n≤p the degree-n coefficient of `Q ΣX^j/j!` is `(p−n)!/p!` times `Σ_i(−1)^i binom(r,i)binom(p−i,p−n)`. Taking the coefficient of `t^(p−n)` in `(1+t)^p(1−1/(1+t))^r=t^r(1+t)^m` gives `binom(m,n)`. No common factor is possible by (8) on the reduced pair; (8) also forces all r roots distinct, and exact tall order (the precision cannot exceed m+r). Over a splitting field, take a lower bidiagonal matrix having these reciprocal poles and `s−r` zeros on the diagonal, with unit subdiagonal; the input `e_0` is cyclic by its successively new unit coordinates. Fit `b` to the first s moments and change lower triangular basis so `e_0` becomes the all-ones input. The physical denominator is Q and the numerator has degree at most s, so those first s moments and the constant 1 determine the fraction exactly. This witnesses exactness even against scalar feasibility in a triangular state realization; it does **not** witness actual rooted-tree order or sharpness of stage counts. The packet inequalities are numerical necessary conditions, not consequences of scalar precision alone.

Over an ordered field, the separately established split-real-pole tall bound gives `p≤m+1_(some retained pole positive)≤s+1`. This makes its stage-only optimum together with the packet inequalities `max(1,p−1)`: for `p≥2` take `r=e=1,z=p−2,m=s=p−1,c₀=ν=0`, for which (4) holds. The `[p−1/1]` Padé pair above has `Q=1−X/p`, one positive pole, and a lower triangular scalar realization over the rationals. At p=1 an explicit one-stage realization works. If an actual method has no positive retained pole, the same ordered result gives `s≥p`, a conditional improvement. Do not impose the ordered extra-slot bound on general characteristic-zero complex tableaux.

For p=1,…,20, (10) reads

    1,1,2,3,3,4,5,5,6,7,8,8,9,10,10,11,12,12,13,14.

At p20 the integer-optimal unordered scalar costs are `(s,r,z)=(14,6,8)`; the ordered optimum is `(19,1,18)`. Neither improves any entry in the established DIRK table. Conditional geometry is nonvacuous: at p20, `z=0,1,2,3,4` imply `s≥55,46,38,31,25`, respectively; at the reviewed characteristic-zero lower endpoint `s=29`, (4) requires `z≥4` and hence `r+c₀≤25`. In particular a genuine order-20 method with retained degree `r≥26` needs `s≥30`. The full cross-order endpoint cap and scalar witnesses are tabulated in `EXACT.txt`. The bound without z,r descends to every nontrivial commutative unital ring using the existing `HasOrder.lower_triangular_of_all_fields`; field-local counts can change in a residue field, so this does not promote arbitrary nonzero ring entries to units or a ring fraction to a reduced field fraction. Order zero is excluded from the tent construction and imposes only s≥0.

`python3 -B check.py` reproduces `EXACT.txt`. It enumerates every separated subset through p20; checks independent exact integer optimization, Padé precision/coprimeness, and the conditional caps; and tests the paid finite-characteristic boundary and its actual small tableau with exact arithmetic. No external service, compiler, held input or shared edit was used.
