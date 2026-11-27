# Universal exact order twelve in twenty-four explicit stages

The [literal tableau](tableau.json) is strictly explicit, has 24
distinct physical rows, and has exact order twelve in every
nontrivial commutative ring in which \(12!\) is a unit. This improves
the [25-stage factorial-unit upper bound](../erk-signed-reverse/order-12-factorial-25/).
It is not a minimum-stage result. The proof and replay use exact
arithmetic; this packet does not claim a Lean certificate.

The common denominator is
\(28868710429988352000000000000=2^{21}3^{10}5^{12}7^2 11^7\),
which divides \((12!)^7\). The scalar sites are
\[
 -2,\ -1/8,\ 0,\ 1/4,\ 3/11,\ 1/2,\ 8/11,\ 3/4,\ 1,\ 9/8,\ 3 .
\]
Their exact cardinal weights integrate through degree eleven:
degree ten is cardinal interpolation, and the degree-eleven
nodal hull has zero mean by symmetry about \(1/2\).
No ordering, positivity, stability, or real-field assumption enters.

## Replace a scalar receiver by an earlier row

Use the established 11-row grade-six forward chart scaled by \(1/2\),
and a retuned six-row grade-four reverse chart as in the
[weighted reverse construction](../erk-signed-reverse/WEIGHTED-ORDERS-11-16.md).
The reverse donor clocks are \(0,3,1/2,1,1,9/8\). The physical
reverse origin \(x=1\) shares its empty raw row with the scalar mass
\(75625/979776\), a unit; no separate balancing copy or pure scalar
receiver is needed there. The two old forward aliases, at physical
clocks 0 and \(1/2\), are both retained. This gives a 25-row
base with a pure receiver at physical clock \(1/4\).

The old forward midpoint (row 9) also has clock \(1/4\).
Its literal row is not the same as the pure receiver. Let
\(\boldsymbol d\) be the old midpoint row minus the pure receiver,
restricted to the 11 forward coordinates. The [transport receipt](transport.json)
gives this row difference and a direction \(\boldsymbol k\) on the
old physical suffix groups. The coefficient of \(\boldsymbol k\)
at the quarter receiver is one; all copies of a physical row have
the same coefficient, and old groups already owned by the forward
prefix have coefficient zero. Add the row \(\boldsymbol d\) times
the corresponding entry of \(\boldsymbol k\) to each forward-attachment
row in the suffix. The suffix-to-suffix block and the clock vector
do not change.

The exact receipt checks two properties:

1. \(\boldsymbol d\cdot\boldsymbol\Phi_t(A_F)=0\) for every ordinary
   forward tree of size at most five, where \(A_F\) is the fixed
   11-row forward prefix.
2. Write \(L\) for the raw reverse matrix, \(C\) for coordinatewise
   multiplication by the physical clock, \(\boldsymbol\beta\) for
   the signed reverse masses, and \(\boldsymbol 1\) for the constant
   vector. For every word \(W\) in \(L,C\) of length at most five,
   \(\sum_i\beta_i k_i(W\boldsymbol 1)_i=0\), using the full
   raw suffix order with \(\boldsymbol k\) pulled back from its
   physical groups.

The first condition makes a new source require a child of size at
least six. The change reads only the unchanged forward prefix.
There is no serial invocation of two changes on the same path,
and two such changed factors in one product require size at least
thirteen. For size at most twelve a new source is propagated in
the fixed suffix by a single word of length at most five: an
extension is a suffix matrix action, and the remaining exact
sibling factors are clock powers. The weighted transpose moves
that word to \(L,C\). The second condition then makes its output
zero. This justifies the row substitution before folding; the
separate all-tree replay checks the final literal directly.

The three quarter-clock virtual rows (16, 17 and 25, one-based)
now have exactly the old midpoint row, not just its clock.
Complete row equality redirects every later tap and adds all
outputs to row 9. The previous groups retain their aliases.
The result is 24 distinct strict rows.

## Two exact order-thirteen defects

For a tree \(t\) put
\(\delta_t=t!\,\boldsymbol b\cdot\boldsymbol\Phi_t(A)-1\).
The thirteen-vertex bush has \(\delta_{t_1}=1161187/1373847552\).
The root with six leaf children and one six-vertex bush child
has \(\delta_{t_2}=24764718696320825821075/351704973312\);
its tree factorial is 78. The integer identity
\[
 16796191258733912319975497220096\,\delta_{t_1}
 -201613469131210752\,\delta_{t_2}=1
\]
survives every paid base change, so order thirteen is impossible
in any nontrivial such ring. In particular, 13 need not be inverted.

## Reproduction

Both scripts use only the Python standard library. The builder
pins the two unchanged neighboring signed-reverse sources by
SHA-256, checks the actual chart reads, replays the full transport
receipt, and regenerates the literal byte-for-byte. The independent
integer verifier uses only that literal; it checks all 7,813
ordinary rooted conditions and both next-order witnesses.

    python3 -B regenerate.py
    python3 -B audit_tableau.py
    sha256sum -c arithmetic-sha256.txt

The [end-to-end Lean certificate](LEAN.md) verifies the rooted order conditions, the two exact-order defects, and the factorial-unit existence equivalence at width 24 on Lean/Mathlib 4.36.0.
