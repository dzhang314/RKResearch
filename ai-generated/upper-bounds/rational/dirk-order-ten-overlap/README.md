# Exact rational order-ten DIRK in 14 stages

A lower triangular tableau with rational coefficients attains exact rooted
order ten in **14 physical stages**. Thus the rational DIRK10 stage interval
is now **12–14**, using the
[separate rational lower bound](../../../research/causal-profile-reduction/dirk-order10-rational-lower-twelve.md).
The real minimum remains 11. The subsequent [13-stage construction](../../../research/dirk10-thirteen-rational-two-ports/README.md) improves the rational interval to 12–13 by a different overlap. The smaller tableau is genuinely implicit and
does not reuse an ERK tableau. The construction also gives a separate
15-stage fallback on uniformly spaced clocks.

| Stages | Ordinary quadrature grid | Scaled order-11 star defect |
|---|---|---:|
| [14](dirk10-14.json) | \(0,1/9,4/13,2/5,3/5,9/13,8/9,1\) | \(919/61600500\) |
| [15](dirk10-15.json) | \(i/8,\ 0\le i\le8\) | \(37/1572864\) |

Both are exact rational certificates; the attached replays do not use
floating point. The results here are exact-arithmetic certificates; a
reviewed end-to-end Lean theorem is separate.

## Exact quadrature and two-ended overlap

For the shorter tableau, put \(y=2x-1\). The eight nodes are the images of
\(\pm1,\pm7/9,\pm5/13,\pm1/5\). With
\(U=(7/9)^2,V=(5/13)^2,W=(1/5)^2\), the degree-eight even nodal product
has zero uniform integral, by
\[
 -5+9(U+V+W)-21(UV+UW+VW)+105UVW=0.
\]
Multiplying it by \(y\) gives an odd product. The interpolatory rule
therefore integrates degree nine exactly: polynomial division by the
nodal product leaves a remainder of degree at most seven and quotient of
degree at most one. For nine uniformly spaced clocks, the degree-nine
nodal product is odd about \(1/2\), giving the same exactness conclusion.
The builder also checks the ordinary ten moments directly. [Eight sites are necessary](../../../research/rational-endpoint-moment-nine/README.md) for any rational degree-nine rule with both endpoints included, so a smaller grid cannot shorten this particular construction.

The [deterministic builder](build.py) generalizes the two-ended
[Lobatto reconstruction](../../../lean/evidence/reviewed-native-dirk-nine-sharp-c35/replay-lobatto.py)
to an arbitrary paid anchored degree-nine quadrature. In the forward
block, a fixed five-donor rational initialization is scaled to the first
matched nonzero anchor; the origin, two anchor evaluations, and two
anchored integral functionals are a five-component basis for the
forward polynomial lift. The reverse block uses a causal five-row
initializer with a four-dimensional weighted polynomial lift. When a
quadrature clock needs a further representative, its new reverse row
supplies exactly the difference between the target aggregate weighted
lift and contributions from existing representatives on the same clock.
This includes both selected anchor copies.

The builder reverses the second block by weighted transposition and
subtracts the forward evaluation lift of each reverse donor from the
forward primitive lift. There are \(q+2\) rows in the reverse block
for \(q\) quadrature sites and seven in the forward block. The three
leading physical copies of forward rows (origin and the two matching
nonzero anchors) are identical as literal full rows. Combining their
weights and incoming columns and deleting the three copies leaves
\(7+(q+2)-3=q+6\) physical stages. All comparisons, linear solves, and
zero-above-diagonal checks are in exact rational arithmetic. The root
order proof is not inferred solely from these linear fit identities.

## Independent literal order replay

From this directory run:

```sh
python3 -B build.py
python3 -B replay.py
```

The first reconstructs every entry and compares against the frozen
JSONs before reporting the exact tree check. The second reads only the
literal JSON, verifies \(c=A1\) and the shape of \(A\), and does an
independent evaluation using grafts of canonical balanced-bracket shapes.
Orders 1 through 10 have tree counts
\(1,1,2,4,9,20,48,115,286,719\), for **1,205 conditions per tableau**.
Sibling order has no effect on stage weights or factorials over
\(\mathbb Q\). For each shape \(t\), both replays check
\(\gamma(t)b^\mathsf{T}\Phi_t(A)=1\).
The separately checked nonzero \(11b^\mathsf{T}c^{\odot10}-1\) proves
failure of order eleven and hence exact order ten.
