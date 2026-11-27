# DIRK10/11: all fixed physical clocks are impossible in the one-local branch

Assume a genuine lower triangular eleven-physical-stage tableau of rooted order ten over a characteristic-zero field. Let `c=A1`, `C=diag(c)`, and `g=Ac²−c³/3`. The physically nonzero g entries, regardless of their weights, are at a single numerical clock ξ. **There is no such tableau with all physical clocks in the six fixed Lobatto labels.** The specific formerly open case is nonconstant nonzero g on its single clock and `L=δ=0`; its contradiction follows from the absent first-clean donor column and true degree-four forward input. The exact theorem also applies when all dirty weights are zero. It does not exclude all eleven-stage DIRK10 tableaux or change the 11–12 stage interval.

## 1. Reduction to the literal absent-column prefix

Use only the valid common one-clock structure from the reviewed rank saturation and the degree-budget correction. Put `h=(A−ξ/2)g`, `H(X)=42XJ₄(X)` with `J₄` the fixed shifted Jacobi quartic, and t the physical terminal. The stage-space identities are

```
F₄=⟨g,h⟩,       F₅=⟨g,h,Ch⟩,       Ah=(m+nC)h,
F₆∩{v_t=0}=⟨g,h,Ch,C²h⟩,          Ae_t=0,
e_t=H(c)+δg+L(c)h,                  deg L≤1,   c_t=1,   g_t=h_t=0.
```

Here a grade-j defect is a genuine true zero-profile column at grade j. The universal band uses the genuine nonzero reflected cubic row for a rank bound, but never requires it to equal `βg`. The first nonzero clock must be ξ by the true C(2) row; throughout any inclusive prefix with only clocks 0 and ξ, every ξ row has `g=γ=ξ³/6`, every zero-clock row has g=0, and h vanishes. This follows by solving the C(2) aggregate tap into ξ and using the resulting `Ag=(ξ/2)g` at such rows. Thus ξ and γ are nonzero.

If nonzero g is constant, the already valid three-debut paired cut rejects three distinct fixed exterior nonzero clocks; the all-fixed case then is impossible. For nonconstant g, `g²` belongs to F₆ and vanishes at t. The above band shows

```
g²=γg+Q(C)h,       deg Q≤2,    Q(ξ)≠0,
h_i=g_i(g_i−γ)/Q(ξ)  at c_i=ξ.
```

Indeed `g²` does not lie in Kg, so Q is nonzero. There are at most two exterior clock labels with h nonzero, since each is a Q root. There are at least two: otherwise on the at-most-two total labels of g and h the clock satisfies a degree-two relation, making F₅ clock invariant, excluded by the actual inclusive Hermite rank gain. Thus there are exactly two exterior h-head labels. The leading g coefficient is γ by the first ξ read with h=0.

With all physical labels fixed, `L≠0` is impossible. If ξ=1, both exterior heads are at other fixed labels, so each is a root of L, because `H=g=e_t=0` there. If ξ≠1, it is fixed interior; the first ξ row gives δ=0, and a changed nonzero g-value on ξ forces `L(ξ)=0` via its nonzero h. Then at most the exterior head at clock 1 can have h nonzero at any fixed exterior label, again too few. Hence `L=0`; then on every dirty row `δg=−H(ξ)`, which by nonconstancy gives δ=0. Now `H(c)=e_t`, so the physical terminal is the only occurrence of clock one and ξ is one of the four interior labels. This reasoning applies without a nonzero dirty weight.

All six fixed numerical labels occur. For example the native unanchored Cauchy possible-support test at order ten applies since the physical terminal clock one is present, so there cannot be only five possible labels. Equivalently the paid degree-nine output on the six fixed nodes gives their nonzero Lobatto masses. No multiplicity census such as four core rows or two of each head is used in this proof.

Let x be the first physical occurrence of a nonzero ordinary interior outside ξ and the two h-head labels. There is such an x among the four interiors. At its row `g=h=0`, so the native F₅ span gives exact C(5), i.e. forward integration of polynomials of degrees **0 to 4**, not 5. Its possible effective donors are among the five nonterminal numerical clocks (zero and the four interiors). The tap into the physical t column is zero. Therefore the aggregate tap into x from a given nonterminal label is the actual integral up to x of that label's degree-four cardinal polynomial on the five labels. The exact scalar check verifies the three taps from each of the *other* interior labels are nonzero, independent of their supposed order. All three must therefore occur strictly before x. By the choice of x they are precisely ξ and both h-head labels; in particular neither head is 0. Call the first head to appear a and the other b. The strict prefix before the physical x row contains only clocks 0, ξ, a, b. It may contain repeated physical rows; the argument below never omits them.

## 2. The absent donor polynomial forces two distinct core values

Define

```
N(X)=X(X−ξ)(X−a)(X−b),       p(X)=I N(X),
```

where I is the primitive anchored at zero. **N has degree four.** Writing N as a sum of monomials of degrees 0 to 4, each `A c^k−c^(k+1)/(k+1)` is a true defect of grade `k+1≤5`. Consequently `A N(c)−p(c)∈F₅` (grade budget 4→5). At every physical row strictly before the first x, its entire inclusive donor set consists of earlier or current rows with clocks 0,ξ,a,b. N vanishes at each such donor, **including the receiver's own retained diagonal**. The later x column has not arrived; clock-one column t is zero as well. Thus `A N(c)=0` on that complete strict prefix, without replacing the tableau by a clipped one.

Write the actual residual as `A N(c)−p(c)=κg+ℓ(C)h` with affine ℓ. The fixed scalar check guards `p(ξ),p(a),p(b)≠0`. On every strict-prefix row at a or b this gives

```
ℓ(a) h_a=−p(a),          ℓ(b) h_b=−p(b).
```

Hence repeated prefix rows at a given head all have the same nonzero h, and the first two head values determine the affine ℓ. At the first ξ row, `h=0,g=γ`, giving `κ=−p(ξ)/γ`. Throughout the ξ prefix, the equation

```
p(ξ)+κ g_i+ℓ(ξ) g_i(g_i−γ)/Q(ξ)=0
```

is a polynomial of degree at most two in g_i with nonzero constant term p(ξ). Thus no such ξ row has g_i=0, and at most two distinct values occur. There must be two: if all g_i equalled γ, `Ag(x)=0` would make the nonzero aggregate ξ tap vanish. Denote the second value by `g′≠γ`; **all** prefix core rows take γ or g′ even if either occurs more than once. Its first occurrence (a definite physical row) is after a, since before the first nonzero exterior clock the inclusive `{0,ξ}` prefix permits only γ.

Write `Sξ,Sa,Sb` for the known nonzero degree-four-cardinal aggregate taps into x and set `J=g′/Q(ξ)`. If `S′` is the actual total ξ tap restricted to rows with g=g′, then `Ag(x)=0` gives `S′(g′−γ)=−γ Sξ`. The contribution of those rows to `Ah(x)` is `S′ g′(g′−γ)/Q(ξ)=−γ Sξ J`, while the γ rows have h=0. The exterior h values are constant on each head prefix as shown above, and h=0 at 0 and x. Since `Ah(x)=0`,

```
γ Sξ J = Sa h_a + Sb h_b.                              (1)
```

The absent-column equation at any changed core row then gives, after cancelling `g′−γ`, the decisive condition

```
γ ℓ(ξ) J = p(ξ),     ℓ(a)=−p(a)/h_a,     ℓ(b)=−p(b)/h_b. (2)
```

## 3. Determine every scalar in (2) in the two literal timings

At the first head a, the actual inclusive donor clocks are only 0,ξ,a, and all preceding ξ rows still have g=γ. The retained degree-one and degree-two clock moments at this head give

```
h_a = ξ²a³/[36(a−ξ)].
```

The native cubic-input defect `Ac³−c⁴/4` belongs to F₄, hence is exactly `(3ξ/2)g+αh`. The first ξ row pins the g coefficient; at a the identity `X³=(ξ+a)X²−ξ a X` on the inclusive donor clocks pins

```
α = 3(a−ξ)(a−2ξ)/ξ².
```

There are precisely two order relations between the **first** changed ξ row and the **first** b row, since they have different clocks.

- **Changed ξ before first b.** Its donor clocks still lie in `{0,ξ,a}`. Apply the same cubic interpolation identity and the true `Ac=c²/2`, `Ac²=c³/3+g` at the changed ξ row. Subtract the `(3ξ/2)g` contribution from the C(4) defect to get `αh′=(a−ξ/2)(g′−γ)`. Since `h′=J(g′−γ)`, this gives `J=(a−ξ/2)/α`. Equation (1) then fixes `h_b=(γ Sξ J−Sa h_a)/Sb`.
- **Changed ξ after first b.** At the first b, all available ξ rows still have value γ, even if many occur. If their total tap there is S, then `γS=h_b` by `Ag`. The degree-three input `X(X−a)(X−b)` takes a possibly nonzero value only at ξ among its actual donors, and its C(4) primitive defect is `αh_b` since the lower-degree inputs are exact at b. Hence `S·ξ(ξ−a)(ξ−b)=b³(2a−b)/12+αh_b`. Substituting α simplifies to `h_b=ξ²b³(2a−b)/[36(ξ−a)(a−2b)]`. Equation (1) then fixes J.

This exhausts the meaningful order relations even with physical repeats at ξ or a,b; the branch is not selected by how many rows occur, only by the first change from γ. Now all quantities in (2) are rational expressions in the four distinct fixed interior clocks `(ξ,a,b,x)`. The scalar check evaluates the affine interpolation of `ℓ(a),ℓ(b)` at ξ and contradicts (2) in both timings for every fixed permutation. All denominator and nonzero guards are explicitly checked. No property of physical rows after x has been used except the known zero terminal column.

## 4. Verification and scope

`DIRKOrderTenAllFixedPrefixScalar.lean` checks the true degree-four aggregate-tap guards and all 24 interior orders × 2 timings modulo 227. The typed audit reuses the prior root and small-division certificates. The independent Python replay expands nodal numerators coefficient by coefficient and verifies the same 48 separators modulo 227, 419 and 587. For characteristic-zero transport, only the splitting field of the fixed quartic is reduced at a prime over 227. The monic normalization is integral, the four roots have distinct residues `[24,51,177,204]`, and all required rational divisions are units in that residue. The checks do not reduce tableau taps, weights, or the unknown cubic amplitude g′; these have already been eliminated from (2).

The actual-tableau and characteristic-zero bridges in §§1–3 are mathematical, not a full native `HasOrder` theorem. The independent two-sided stage-six chronology uses a separate exact reflected pay and is not needed for this contradiction. The old degree-five forward nodal relation is automatic in this branch (`H(c)=e_t`) and is not reused. Together with the corrected one-off exclusion, an active single-physical-dirty-clock candidate needs at least two off-Lobatto labels. The unrestricted DIRK10 interval is still 11–12.
