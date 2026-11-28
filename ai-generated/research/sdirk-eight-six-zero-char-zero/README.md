# Exactly six physical quadratic zeros excluded in characteristic zero

**Theorem.** Let \(A,\mathbf b\) be a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field. For \(\mathbf c=A\mathbf1\) and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\), exactly six physical entries of \(\mathbf g\) cannot be zero. No assumption of positive weights, distinct clocks, or absence of silent stages is made.

First apply the [six-zero support and activity census](../sdirk-eight-six-zero-census/README.md). The cases \(d_2=0\) and two constant off groups with any activity are already impossible over paid fields. A no-active case in characteristic zero cannot repeat a physical \((c_i,g_i)\) pair when \(d_2=1\). These rank reductions, the actual off activity, and the exact chronologies exhaust the following branches:

| Off geometry | Exact characteristic-zero exclusion |
| --- | --- |
| One physical off clock | [Both canceled and nonzero ordinary aggregate](../sdirk-eight-six-zero-one-clock/README.md), with all eight signed forward/rear frames and the pure-square gate at seven literal ordinary labels |
| Two physical off clocks, some active weight | [Paid constant-group scalar contradiction](../sdirk-eight-six-zero-two-clock-active/README.md#1-rank-and-two-constant-off-groups), or [one varying group and canceled pair](../sdirk-eight-six-zero-two-clock-active/README.md#2-one-varying-off-group-with-a-canceled-live-pair) |
| Two physical off clocks, both varying and silent | [Duplicate terminal reduction and ordinary moment exclusion](../sdirk-eight-six-zero-silent-duplicate-terminal/README.md#2-a-fixed-first-zero-pure-trace-arithmetic-third-or-four-off-front) |
| Two physical off clocks, varying silent triple and singleton | [Zero rear ratio, same-clock coincidences, both literal silent-eighth possibilities, and both live phases](../sdirk-eight-six-zero-silent-varying-triple/README.md). Live projections have degree-nine star fields and arithmetic degree-four and degree-69 factors; local fibers and simple good reductions retain every pivot case. |
| Three physical off clocks | [One canceled active pair, complete graph proof](../sdirk-eight-six-zero-three-clock-active/README.md). First-zero-three early/late mates; first-zero-four star; general and leading-drop arithmetic. Late degree-14/18 factors and regular arithmetic degree-9/27 first-clock pivot factors are checked in their exact local fields. |
| Four physical off clocks | [Four silent graph off rows and all repeated-terminal placements](../sdirk-eight-six-zero-silent-duplicate-terminal/README.md), including fixed and variable first zeros |

The exact finite reductions used in a few projections are **certificates about characteristic-zero field factors**, with degree-preserving or simple-root local embeddings. They are not broad positive-characteristic stage statements. Independent Gaussian, saturated support, and ordinary Vandermonde results are linked at the relevant reductions.

**Lean scope.** `RKCert.Research.SDIRKEightSixZeroPairScalar` certifies the literal first tap and the equal/opposite paid scalar contradictions. `RKCert.Research.SDIRKEightSixZeroReverseSupportedScalar` certifies the division-free reverse cardinal gate and the two-omitted-sites/profile parameter identities. The shared `SDIRKEightOrdinaryHankelPivot` and `SDIRKEightFiveZeroGraphArithmeticFront` certify structural moment pivots and cleared graph pencil identities under explicit hypotheses. These scalar gates do not formalize the entire rooted chronology, characteristic-zero field construction, or final theorem from `HasOrder`; those parts are the linked source proof and exact reproducible checks.

The theorem is structural. It excludes one physical residual count at the ten-stage floor, not every ten-stage method and not every coefficient ring.
