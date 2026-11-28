# Exactly five physical quadratic zeros excluded in characteristic zero

**Theorem.** A strict ten-stage SDIRK tableau with nonzero common diagonal and ordinary order at least eight over a characteristic-zero field cannot have exactly five physical zeros of \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), where \(\mathbf c=A\mathbf1\). Silence and repeated clock values are allowed throughout. This is a structural exclusion at the ten-stage floor, not an increase in the ordinary lower bound.

The [paid-field support theorem](../sdirk-eight-five-zero-support-rank/README.md) first forces a unique supported degree-two direction. It is either a pure scalar quadratic, at two physical off clocks, or a genuine quadratic graph with at least three physical off clocks. Here the number of active off clocks counts those clocks with a nonzero weight on a **physical off-zero** stage; an ordinary clock can coincide with an off clock, and the ordinary aggregate of a live pair can still be zero.

| Supported direction | Active off clocks | Characteristic-zero exclusion |
| --- | ---: | --- |
| Pure scalar quadratic | 0 | [Four ordinary labels](../sdirk-eight-five-zero-pure-four-ordinary/README.md); five live labels with [silent](../sdirk-eight-five-zero-pure-silent-eighth/README.md) or [live](../sdirk-eight-five-zero-pure-live-eighth/README.md) row 8 |
| Pure scalar quadratic | 1 | [Both canceled and nonzero off aggregate](../sdirk-eight-five-zero-pure-active/README.md#2-two-active-clocks-or-one-with-a-canceled-ordinary-mass), including the separate [literal duplicate argument](../sdirk-eight-five-zero-pure-active/README.md#3-a-nonzero-ordinary-off-aggregate-forces-five-distinct-literal-zero-clocks) |
| Pure scalar quadratic | 2 | [Both canceled live pairs](../sdirk-eight-five-zero-pure-active/README.md#2-two-active-clocks-or-one-with-a-canceled-ordinary-mass) |
| Genuine graph | 0 | [Complete no-active synthesis](../sdirk-eight-five-zero-graph-arithmetic-live/README.md#3-full-no-active-off-consequence): four-site and four-off support, then all literal first-zero/rear phases including exceptional leading fibers |
| Genuine graph | 1 | [Canceled live pair, all three earliest positions](../sdirk-eight-five-zero-graph-one-active/README.md) |
| Genuine graph | 2 | [Both pair-mate clocks and the clean reflected graph read](../sdirk-eight-five-zero-graph-two-active/README.md) |

Several component rank statements and necessary conditions hold in wider paid characteristic. The theorem here uses exact characteristic-zero polynomial factors and, at specific stages, degree-preserving good reductions as certificates **about characteristic-zero gcds**. It does not claim exclusion in every positive characteristic, over arbitrary non-field rings, or for a different number of physical residual zeros. The Lean companion modules certify reusable parts of the algebra, not this entire assembled theorem from `HasOrder`.
