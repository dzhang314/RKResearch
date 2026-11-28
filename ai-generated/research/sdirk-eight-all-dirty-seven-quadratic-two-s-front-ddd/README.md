# The doubled end cannot open D,D,D when there is exactly one singleton endpoint

Consider a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton physical endpoint. At the singleton end the [prior classification](../sdirk-eight-all-dirty-seven-quadratic-sdd-dss-arithmetic-new/README.md) leaves only a two-singleton opening, S,S,D or S,D,S. This packet proves that the opposite actual opening **cannot be D,D,D**. All literal arithmetic and star phase choices and all three possible overlap positions are covered, without signs, an ordering on the field, or a splitting assumption. This is a chronology result; the general 10–11 stage interval does not change.

## The three actual doubled labels and the unique overlap

Orient from the singleton by the actual weighted mirror if needed. Normalize the diagonal to one and use \(y=x-1\), \(m=1/(2\gamma)\), \(H=2(m-1)\) and \(t=y-H/2\). The first forward singleton is at \(0\); the terminal D is at \(H\ne0\). The reverse offset is \(H-y\). In D,D,D at the rear, the three actual distinct D labels in their reverse physical order are
\[
  (d_1,d_2,d_3)=(H,H-v,H-2v)\quad\text{in arithmetic},
  \qquad (H,H-v,H+v-2)\quad\text{in star}.
\]
The known normalized reverse defects \(\rho_i\) have \(\rho_1=1/2\), \(\rho_2=\kappa(v)/2\), and \(\rho_3\) equal to either \(q_{\rm ar}(v)/2\) or \(\rho_2\), respectively. Here \(\kappa(z)=1+2z-z^2\), \(q_{\rm ar}(z)=N(z)/D(z)\), \(D(z)=-2+z+4z^2-z^3\), and \(N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\). These are the [literal first-three gates](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md); the true arithmetic guards are nonzero \(v,\kappa,D,N,3v-2\), and star requires \(v,v-1,v-2,\kappa\ne0\). Reverse arithmetic \(v=2\) is not discarded solely as a gap.

The single later forward D is necessarily one of these labels, \(d=d_i\). Let \(s\) be the later forward singleton, and \(f_d,f_s\) their known forward defects. The actual choices of phase are
\[
\begin{array}{c|ccc}
\text{forward phase}&s&f_d&f_s\\\hline
\mathrm{A2}\ \text{(D second, arithmetic)}&2d&\kappa(d)/2&q_{\rm ar}(d)/2\\
\mathrm{A3}\ \text{(D third, arithmetic)}&d/2&q_{\rm ar}(d/2)/2&\kappa(d/2)/2\\
\text{star (either order)}&2-d&\kappa(d)/2&\kappa(d)/2 .
\end{array}
\]
For a forward star the offset of the physical second row can be \(d\) or \(s\); applying the true formula separately gives these same pairs since \(\kappa(2-d)=\kappa(d)\). No theorem that permuting rows preserves order is needed. The forward first-departure guard excludes literal gap two when the first clock is singleton. The five labels \(0,s,d_1,d_2,d_3\) are distinct. The only planned overlap is the one D used once in each prefix. The [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md) forbids centered or antipodal D labels. All these guards apply without ordering the labels.

## Third-D and paid front singleton graph gates

Use the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), with \(\mathcal Q=L_3-F_*L_4\) proportional to \(P R\), where \(P\) has the three distinct D roots and \(R\) is the genuinely quadratic singleton graph normalized by \(R(0)=1/2\). The affine \(F_*\) has nonzero slope. The monic \(L_3,L_4\) are centered Legendre modes evaluated at \(t=y-H/2\). Their coprimality gives \(L_4(d_i)\ne0\) at every D root of \(\mathcal Q\). Fit \(F_*\) through \(L_3/L_4\) at \(d_1,d_2\) and write the exact quotient
\[
          M_3(y)=\mathcal Q(y)/[(y-d_1)(y-d_2)],\qquad E=M_3(d_3)=0 .
\]
There is no unknown graph factor choice here: on the actual mesh \(M_3\) is a nonzero scalar times \((y-d_3)R\), including any common or repeated root. Its values at \(0,s\) are nonzero because both labels are singleton and nonzero-defect. At the true observed \(s\)-row the paid graph read gives
\[
                 A=d_3 M_3(s)+2M_3(0)(s-d_3) f_s=0 .
\]
This normalization uses only the first known singleton defect and keeps any nonsplit or Hermite graph.

## One overlap product and two paid affine equations

Let \(\lambda\ne0\) be the reverse-to-original normalization of defects. The two actual roots at the single overlap \(d=d_i\) are \(f_d,\lambda\rho_i\). Their true product in \(L_4-g(A_2+Bg)=0\) fixes
\[
                     \beta=B\lambda=-L_4(d)/(f_d\rho_i).
\]
No other doubled label is treated as an overlap. Use the known reverse read at each \(d_i\) to recover the scaled quadratic \(T=\lambda A_2=U+\lambda V\) by interpolation at the three distinct D labels:
\[
        U(d_i)=L_4(d_i)/\rho_i,\qquad V(d_i)=-\beta\rho_i,
        \qquad i=1,2,3.
\]
Indeed the actual \(L_4\) equation at \(g=\lambda\rho_i\) gives \(T(d_i)=L_4(d_i)/\rho_i-\beta\lambda\rho_i\). The root product, not any extra assumption about the other two unused D stages, connects the sole front D.

At either actual original singleton \(y=0,s\) with known \(g=1/2,f_s\), respectively, \(\lambda L_4(y)=gT(y)+\beta g^2\). Thus define two affine rows \(a_y+\lambda b_y=0\) with
\[
                  a_y=g U(y)+\beta g^2,\qquad b_y=g V(y)-L_4(y).
\]
The exact necessary augmented determinant is
\[
                            K=a_0 b_s-a_s b_0=0 .
\]
This condition does not divide by a row coefficient (or presume at least one nonzero). Even rank-zero data satisfy this necessary determinant and are subjected to the same contradiction.

## Eighteen exact phase projections

For every rear phase, forward phase, and overlap index, form the guarded integer numerators of \(E,A,K\) in \(H,v\). The script audits every nonconstant denominator against actual clock differences, nonzero phase and Legendre values, and the proved nonzero slope and \(M_3\) evaluations. It removes no factor merely because of a lost specialized leading coefficient. Take separate integer resultants in \(v\) of \(E,A\) and \(E,K\), then take their gcd in \(H\), removing only guards depending on \(H\) alone. The projected degree pairs by actual overlap index \(i=1,2,3\) are:

| Rear phase | Front phase | \(i=1\) | \(i=2\) | \(i=3\) |
| --- | --- | ---: | ---: | ---: |
| arithmetic | A2 | (54,130) | (62,173) | (59,160) |
| arithmetic | A3 | (25,127) | (44,168) | (38,165) |
| arithmetic | star | (39,100) | (44,128) | (42,126) |
| star | A2 | (68,66) | (82,147) | (78,147) |
| star | A3 | (30,98) | (55,147) | (51,147) |
| star | star | (46,48) | (48,84) | (55,84) |

Every guarded gcd is a unit. The integer resultant necessity and transfer of the rational unit gcd are valid under arbitrary characteristic-zero specialization; no requirement of real roots, nonzero determinants, stage-subset sorting or sign is added. Neither trace nor actual fourth reads are needed to exclude this phase. The conclusion that the opposite end has at least one more S is limited to the exactly-one-singleton endpoint chart.

## Replay

Run `SYMPY_GROUND_TYPES=flint python check_two_s_ddd.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSFrontDdd.lean) verifies the denominator-free normalized graph equation, paid scaling and augmented minor. The rooted-order ingress and the eighteen exact projections form a mathematical proof with exact replay, not a full end-to-end Lean or finite-characteristic theorem.
