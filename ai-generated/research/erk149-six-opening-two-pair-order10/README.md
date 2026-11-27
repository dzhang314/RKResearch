# All live chronology exclusions for the six-opening two-pair ERK10 cut

The neighboring [exact quadratic-field positive control](../../upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/README.md) is order nine. This result excludes order ten throughout its **six-opening cubic-decoder, two-pair high architecture** with the explicit live-share and low-clock guards below. It uses genuine rooted one-, two-, and three-letter contexts and makes no simplifying assumption about the reverse block. The unrestricted order-ten interval remains **14–15**.

## Scope

The strictly explicit six opening rows have the canonical clocks \(0,e,2p/3,p,q,r\) and the canonical moment/rough-tap structure of the positive packet. The scalar donor clocks \(p,q,r\) are nonzero and distinct; the decoder \(\Pi\) is interpolation through the literal four opening labels \(0,p,q,r\). The eight later rows have six distinct nonzero scalar sites: the final 1, two interior pairs at distinct clocks, and three other singleton interiors. The scalar term at 0 has the old origin weight. All eight high physical weights and all six high aggregate weights are nonzero, with arbitrary signs. No prescribed positive interval for the clock values is needed: only distinctness from 0 and 1 and one high clock per stated site. The high strict block and ordering of the seven nonterminal high rows are otherwise arbitrary. The literal lower-left cross matrix is \((EJ-BE)\Pi\), where \(J\) integrates from zero and \(E\) evaluates at high clocks.

Let \(\ell\) be the one-dimensional annihilator of the two actual pure size-five donor directions \(\mathbf Q,\mathbf V\) restricted to \(p,q,r\), as in the positive packet. We exclude every case where \(\ell\) is **not** proportional to \(E_r\), and also the case \(\ell=E_r\) where \(r\) does not coincide with one of the five high interiors. The point-collided sparse case and cases with a zero individual pair share are not covered.

## Exact direct source spaces

Use \(\rho_t=g_t-\Pi\boldsymbol\Phi_t^{\rm old}\). The size-five source span is \(H_5=\ker\ell\) inside \(X\mathcal P_3\). The whole prefix is exact to size four through the decoder. At every high stage the derivative is therefore ideal for any source with all root children of size at most four; call these sources direct. All size-five sources are direct.

The direct size-six sources contain the two cubics obtained by interpolating the physical donor defects \(C\mathbf Q\) and \(C\mathbf V\), up to a sign: attach a leaf to the root in each pure size-five combination. This is a true multiplication by the clock at the root and creates no child larger than four. The size-six bush also contributes the monic degree-five residue after cubic interpolation. If both cubic combinations were still in \(H_5\), then \(\ell C\) would annihilate \(\mathbf Q,\mathbf V\) and be proportional to \(\ell\). Distinct donor clocks identify each clock eigenrow with a single evaluation; independence of the two original pure directions at \(p,q\) makes \(\ell_r\ne0\). Thus that case is exactly \(\ell=E_r\). Otherwise the size-five and direct size-six span is all of \(X\mathcal P_4\), dimension five.

In the exceptional point case the donor at \(r\) is actually locally pure through derivative size five. Every direct size-six source therefore has \(\rho_t(r)=0\), as does \(H_5\). The added monic degree-five bush residue proves
\[
          H_5+H_{6,\mathrm{dir}}=X(X-r)\mathcal P_3 .
\]
Its direct size-seven bush also vanishes at \(r\) and raises this span to \(X(X-r)\mathcal P_4\). On the five interior sites this last space evaluates invertibly if \(r\) is not an interior site. In all branches covered by the proof, the direct sources through seven thus separate all five interior values. The direct sources through six have rank at least four on those sites.

## True order forces the lower reverse aggregates

If true order ten holds, the [fourteen-stage equality result](../ERK10-FOURTEEN-STAGE-EQUALITY.md) supplies literal full \(\mathbf b A=\mathbf b(I-C)\). Reverse the high rows and take the weighted transpose \(L\), which is allowed by the nonzero individual high weights. Put \(y=1-x\); the full actual equality restricted to any high column is exactly \(L\mathbf1=\mathbf y\). The origin does not enter the reverse word comparisons, since all \(\rho_t(0)\) and \(J\rho_t(0)\) are zero.

Set
\[
 \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\quad
 \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
 \mathbf h=L\mathbf u,\quad
 \mathbf k=L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4 .
\]
At the first reverse row (clock 1), all four vanish. For a direct source, true outer unary with one or two leaf marks respectively gives \(-\mathbf u\) or \(\mathbf g-2\mathbf u\) paired with \(E\rho_t\), by weighted adjointness and exact clock moments. These tests apply to all indicated direct sources through seven. The one-mark tests first force all interior aggregates of \(\mathbf u\) zero, and the two-mark tests then do the same for \(\mathbf g\). In the literal three-unary root on a direct source \(t\) of size at most seven, the contributions from \(\rho_{[t]}\) and \(\rho_{[[t]]}\) vanish by the already paid one-letter and empty-word reverses. The remaining contribution is \(\mathbf g/2+\mathbf h\) on \(E\rho_t\), minus the test of \(\mathbf u\) on \(EJ\rho_t\). The grouped lower rows therefore force all aggregates of \(\mathbf h\) zero. In particular \(\mathbf u,\mathbf g,\mathbf h\) belong to the two-dimensional opposed-pair space \(U\); this is a derived condition, not imposed on the tableau.

For direct sources through six, all true length-three tests can likewise be isolated: following the designated unary/leaf spine, other possible source terms are at strictly shorter exterior lengths. Those were paid for every source, not merely direct ones, since \(\mathbf u,\mathbf g,\mathbf h\) have zero aggregate on every scalar site. The degree-nine scalar quadrature is itself forced by true order ten. Three clock marks pay \(\mathbf k\) on \(E(H_5+H_{6,\mathrm{dir}})\). In order to separate \(L U\), first note \(L\mathbf u=\mathbf h\) is already grouped zero. The reverse word clock/transport/clock then pays \(L C\mathbf u\) on the same source span after subtracting the just-paid \(\mathbf k\) term. The three-primitive word pays \(L(\mathbf g/2+\mathbf h)\) there.

If \(\mathbf u\) has nonzero coefficient at both pairs, \(\mathbf u,C\mathbf u\) span \(U\). Otherwise the first pair's first occurrence always has \(u=-a^2/2\ne0\); the other pair's first occurrence, at \(y=b\), reads that first interior with some coefficient \(k\). Regardless of \(k\), \((g/2+h)_{B_1}=-b^3/6\ne0\). Thus \(\mathbf u,\mathbf g/2+\mathbf h\) span \(U\) in the second case. In either case both \(\mathbf k\) and \(L\mathbf v\), for every \(\mathbf v\in U\), must kill \(E(H_5+H_{6,\mathrm{dir}})\). At the five interior sites their aggregated rows therefore lie in a space of dimension **at most one**, and all their two-site minors must vanish.

## Actual chronology gives a nonzero minor

The first nonterminal reverse row must be a first occurrence of a repeated pair. Otherwise its actual \(Ly=0\) cannot equal \(y^2/2\) at a singleton. The next row must be a first occurrence of the other pair: a singleton at this point cannot read the only prior nonzero-\(y\) donor because it must kill its true \(u\ne0\); a repeat completion at the first clock also cannot pay the pair's \(Ly^2\) since all its previous nonzero \(y\)'s coincide with its own, making pooled \(Ly^2\) equal \(y\) times pooled \(Ly\). Thus the reverse starts with 1 and two distinct first occurrences.

For a completed pair at any point use its pooled row divided by its nonzero aggregate mass. This is a true weighted row on its available earlier donors. It has the exact \(Ly,Ly^2,L\mathbf u\) reads just proved. A singleton is already its own pooled row.

**A pair completes next.** Call the completed pair's reverse \(y\) clock \(a\) and the other pair's clock \(b\). Choose \(\mathbf v\) supported at the other pair with value 1 at its first occurrence. At the first completed group and the next group (a singleton or the other completed pair), all used incoming \(y\)'s lie in \(\{0,a,b\}\), and among the support of \(\mathbf v\) only the first \(b\) can be read. A pooled row at \(y=s\) therefore has the specific normalized responses
\[
 G(s)=(a+b)s^3/3-ab s^2/2-s^4/4,\qquad
 T(s)=\frac{s^2(2s-3a)}{6b(b-a)}
\]
for \(\mathbf k,L\mathbf v\) respectively. The first identity uses \(y^3=(a+b)y^2-ab y\) on the donor set; the second is the coefficient at the first \(b\) solved from \(Ly,Ly^2\). If the second group has clock \(c\), its determinant with the completed group's responses is
\[
             G(a)T(c)-G(c)T(a)
                =\frac{a^3c^2(a-c)^2}{24b(a-b)}\ne0 .
\]

**A singleton comes next.** Call its \(y\) clock \(c\), and call the first two chronological pair clocks \(a,b\). Its true incoming tap \(\beta\) on the first \(b\) donor is nonzero, or else \(L\mathbf u=0\) eliminates its only nonzero-\(y\) tap. The next group (a singleton or the first completed pair) at \(y=s\) uses only \(0,a,b,c\). Its two taps on the early \(a,b\) donors must be \(t\) times those of \(C\), by the actual \(L\mathbf u=0\) and \(u(C)=0\). Write \(q\) for its tap at \(C\). Its next two paid lower reads give
\[
           t c^2/2+qc=s^2/2,\qquad t c^3/3+q c^2=s^3/3 .
\]
Choose the opposed direction \(\mathbf v\) with unit value at the first \(b\). Its response at \(C\) is \(\beta\), and at \(s\) is \(t\beta\), since the second \(b\) cannot be an earlier donor here. The normalized determinant of the two cubic/second-direction responses is
\[
       \beta\{q c^3-s^4/4+t c^4/4\}
                     =-\beta s^2(s-c)^2/4\ne0 .
\]
In both chronologies the nonzero normalized determinant transfers to the actual aggregate rows by the nonzero masses. This contradicts the one-dimensional cap forced by actual order ten.

The three scalar identities (two determinant formulas and the second-pair response) are formalized over characteristic-zero fields in Lean/Mathlib 4.36.0, with a typed and axiom audit. The rooted-to-grouped reduction and the chronology argument above are mathematical, not an end-to-end native exclusion of the entire chart.
