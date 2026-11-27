# Six-stage strict SDIRK in three further prime characteristics

See also the [complete field classification and ring upper bounds](MINIMA.md).

The minimum stage count for classical order six over **each** of
`F_263`, `F_457` and `F_126963077` is exactly **six**.
The lower bound is the existing nonzero-commutative-ring theorem
[`common_diagonal_order_six_stages_universal`](../../lean/RKCert/ReviewedNative/SDIRKSixFourConstantEndpoint.lean).
The new upper witnesses are in
[`six-stage-witnesses.json`](six-stage-witnesses.json). The matrix entries are
ordinary residue representatives; the unlisted strict upper triangle is zero.

| Prime | Common diagonal | Nonzero weights | Checked order-seven bush payment |
| ---: | ---: | ---: | ---: |
| 263 | 231 | 5 | 161 |
| 457 | 22 | 5 | 43 |
| 126963077 | 85710816 | 6 | 4126301 |

All three tableaux have six distinct physical clocks; the first two have zero
first weight. Each listed seventh-order payment would have to equal one:
the witnesses have order exactly six. They do not change the characteristic-zero
minimum of seven, the global nonzero-ring minimum of six, or a higher-order
stage bound. The same upper witnesses work over coefficient extensions of the
respective prime fields.

Native Lean certificates: [263](../../lean/RKCert/Research/SDIRKSix263.lean),
[457](../../lean/RKCert/Research/SDIRKSix457.lean),
[126963077](../../lean/RKCert/Research/SDIRKSix126963077.lean).
Each proves the literal triangular form, common nonzero diagonal, row sums,
`HasOrder 6` via the repository's complete kernel-checked finite tree test,
and the order-seven failure. Independently, run `python3 check-six.py`:
it tests primality by trial division and enumerates all 37 unordered rooted
trees through six, without SymPy or a Lean evaluation oracle.

## How the witnesses were reconstructed

Instead of solving all 37 nonlinear conditions at once, start with the
[existing order-six endpoint restrictions](../../lower-bounds/characteristic-zero/sdirk_order6_six_stage_exclusion_20261123.md)
and their [integral chart polynomials](../../lean/RKCert/ReviewedNative/SDIRKSixIntegralReceipts.lean).
Write the normalized matrix as `T=A/γ`, so its diagonal is one, take
`z=1/γ`, and use normalized clocks `x=T1`. We searched the case of
arithmetic triples at both ends,
`x=(1,1+u,1+2u,z-1-2v,z-1-v,z-1)`, **as an ansatz**, not a completeness
claim for these characteristics. Solving the existing front, bridge and
terminal restrictions over the three fields selects:

| Prime | z | u | v |
| ---: | ---: | ---: | ---: |
| 263 | 189 | 111 | 159 |
| 457 | 187 | 81 | 423 |
| 126963077 | 118528251 | 119678568 | 119678568 |

Because the six clocks are distinct, scalar quadrature fixes the output
weights from `sum_i b_i x_i^j = z^j/(j+1)` for `0 ≤ j ≤ 5`. All three
terminal weights are nonzero in every example. With one-based row numbering
the selected front and reverse tail triples prescribe
`T21=u`, `T32=r(u)`, `T31=2u-r(u)`,
`T65=v b5/b6`, `T54=r(v)b4/b5`, `T64=(2v-r(v))b4/b6`, where
`r(t)=2t(3t-2)/(-2+t+4t²-t³)`.

The remaining nine entries are the three-by-three block from the first three
to the last three stages. Put `g=Tx-x²/2`, with componentwise products, and
`k=1+2u-u²`. The saturated cubic identities read
`(x-1)g=k(T-I)g` and `2T x²=T²x+x(Tx)`. In particular
`T x²=(2/3)(Tg+x(Tx))`.
For `P(t)=20t³−30zt²+12z²t−z³` the collapsed Legendre identity is

    P(x) = 2P(1) g + (2/u)(P(1+u)−kP(1))(T−I)g.

When `k ≠ 0` these equations determine

    D(t) = u k P(1) + (P(1+u)−kP(1))(t−1),
    g_i  = u k P(x_i)/(2 D(x_i)),
    (Tg)_i = (1+(x_i−1)/k) g_i.

This covers 126963077, where the indicated denominators are nonzero. At 263
and 457, `k=0`, so instead use `g=(1/2,0,0,0,0,0)` and

    Tg = g + u (P(x)−2P(1)g)/(2P(1+u)).

In either case, we know the three columns `T1=x`, `Tx=g+x²/2`, and
`Tx²=(2/3)(Tg+x(Tx))`. Subtracting the known tail contributions leaves
the same invertible three-clock Vandermonde system in each of the last three
rows. Finally scale back to `A=T/z`. The direct full-tree certificates do
not assume the chart arguments and do not rely on the ansatz for correctness.
