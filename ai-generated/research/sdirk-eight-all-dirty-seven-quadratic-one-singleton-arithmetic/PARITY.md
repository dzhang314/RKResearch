# Single-endpoint parity lemma and first literal mesh counts

**Lemma (no centered or antipodal projection root).** In the all-dirty exactly-seven-clock strict ten-stage SDIRK8 case with precisely one singleton physical endpoint, the normalized quintic projection has neither a centered zero nor an antipodal root pair, even over the algebraic closure of a characteristic-zero coefficient field.

Orient by the actual weighted mirror so the singleton is first. In centered coordinate \(t=y-h\), the physical endpoint labels are \(-h,h\), with \(h=m-1\ne0\) and \(m=1/(2\gamma)\ne0\). The two endpoint labels must be distinct since they have different multiplicities. Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md):
\[
 \mathcal Q(t)=L_3(t)-(a+b t)L_4(t),\qquad
 L_3=t^3-\tfrac35m^2t,\quad L_4=t^4-\tfrac67m^2t^2+\tfrac3{35}m^4 .
\]
The equations hold in any extension. The Legendre polynomials are coprime in the algebraic closure: at \(t=0\), \(L_4=3m^4/35\ne0\), and at the other possible roots \(t^2=3m^2/5\) of \(L_3\) its value is \(-12m^4/175\ne0\). In particular \(L_4\) is nonzero at every root of \(\mathcal Q\). If \(\mathcal Q(0)=0\), then \(a=0\). If \(\mathcal Q(z)=\mathcal Q(-z)=0\), sum the two equations using odd \(L_3\), even \(L_4\), to get \(2a L_4(z)=0\); again \(a=0\). Either way \(\mathcal Q\) becomes odd. The terminal double gives \(\mathcal Q(h)=0\), hence \(\mathcal Q(-h)=0\). But at the first singleton both the doubled-clock cubic \(P(-h)\) and the graph \(R(-h)=1/2\) are nonzero, and \(\mathcal Q\) is a nonzero scalar multiple of \(P R\). This is the contradiction. The argument does not require \(P\) and \(R\) to be coprime to each other.

## First use: literal S,D,D opposite D,D,D

This count sets up, but does not decide, the S,D,D forward and D,D,D weighted-rear branch. Write \(H=2h\), with the physical first singleton at \(y=0\). Label the three D clocks by the actual rear order \(D_1,D_2,D_3\). In original coordinates they are \((H,H-v,H-2v)\) for rear arithmetic or \((H,H-v,H+v-2)\) for rear star. The forward two later D labels are the ordered pair \((D_i,D_j)\). Try all six ordered pairs for each phase pair. Forward arithmetic requires \(D_j=2D_i\); forward star requires \(D_i+D_j=2\).

The ordinary guards include \(H,H+2\ne0\), distinct D labels, all D labels different from \(0\), the genuine scalar phase guards, and the [first-departure guard](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) on a singleton first row (its forward gap cannot be 2). The new parity guards forbid any \(2D_i=H\) or \(D_i+D_j=H\). Count a chart as excluded here only when a guard polynomial vanishes identically on its exact affine phase line; isolated forbidden points are not discarded as whole lines.

| Forward / rear | Ordered charts | Ordinary guards | Additional parity exclusions | Remaining lines |
| --- | ---: | ---: | ---: | ---: |
| arithmetic / arithmetic | 6 | 2 | 2 | 2 |
| arithmetic / star | 6 | 0 | 2 | 4 |
| star / arithmetic | 6 | 0 | 0 | 6 |
| star / star | 6 | 0 | 2 | 4 |

The ordinary arithmetic/arithmetic losses are \((2,1)\) by \(D_3=0\) and \((2,3)\) by \(H=0\). The extra arithmetic/arithmetic losses are \((3,1)\) by \(2D_3=H\) and \((3,2)\) by \(D_2+D_3=H\). The arithmetic/star losses are \((2,1),(3,1)\) by \(2D_2=H,2D_3=H\), respectively. The star/star losses are \((2,3),(3,2)\), both by \(D_2+D_3=H\). The other sixteen ordered lines are retained, with any individual zero-denominator, equal-label, or phase exceptions still needing the actual checks. In particular no phase pair is excluded by the count alone. The star pair clocks have equal known defects across its two orders, but the ordered counts do not claim that permuting the physical rows preserves order.

Run `python check_parity_counts.py` with SymPy 1.14 for the elementary symbolic division audit. The Lean companion of the parent packet includes the scalar antipodal-intercept identity and requires the already justified nonzero even value; the tableau parity ingress remains mathematical.
