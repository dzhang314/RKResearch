# Seven distinct clocks: exclusion of the constant graph with singleton endpoints

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with no literal zero quadratic residual. Suppose there are exactly seven different clock labels. In the [all-dirty clock census](../sdirk-eight-all-dirty-clock-census/README.md) normalization, write \(x=c/\gamma\), \(2m=1/\gamma\), \(t=x-m\), \(g\) for the normalized residual. The equations for the physical pairs are
\[
 U=L_4(t)-g(A_2(t)+Bg),\qquad
 V=L_3(t)-g(D_3(t)+F(t)g),
\]
with \(B\ne0\). Put \(P=BD_3-FA_2\), \(Q=BL_3-FL_4\). Exactly three labels are doubled and four singleton. Each double is a common root of \(P,Q\). The five-double exclusion gives \(P\ne0\), so \(\deg P=3\), these three labels are its distinct roots, and \(Q=P R_2\) with \(\deg R_2\le2\). Every singleton satisfies \(g=R_2(t)\).

**Result.** If \(R_2\) is constant, the two literal endpoint clocks cannot both be singletons. In particular this excludes one full actual chronological subchart without requiring real coefficients, ordered weights, or symmetry of the tableau. It does not yet exclude a constant graph at doubled endpoints, a nonconstant graph, or a general ten-stage tableau.

## Quotient structure and exact left/right masks

Set \(H=L_4-R_2(A_2+BR_2)\) and \(\mathbf e=\mathbf g-R_2(\mathbf t)\). By the [clock-decic multiplicities](../sdirk-eight-all-dirty-clock-census/FIBRE-RESIDUES.md), \(W=P^2H\). Thus \(H\) is a degree-four polynomial with the four distinct singleton roots, disjoint from all doubles. Both copies at a double have \(e_i\ne0\), because a zero copy would give \(H=0\) there. At each double \(e_1e_2=-H/B\).

The full degree-\(j\) evaluation space splits as
\[
 E_j=\operatorname{ev}\Pi_j(t)\ \oplus\ \mathbf e\odot\operatorname{ev}\Pi_{j-2}(t).
\]
Indeed \(\mathbf e\) vanishes at the singletons, \(P\mathbf e=0\), and \(U=0\) reduces \(e^2\) to a clock polynomial and a degree-two scalar times \(e\) without raising weighted degree. Two distinct \(e\) values at each double make the two summands intersect trivially. Above degree two on the second summand one can reduce its scalar polynomial modulo \(P\).

With weights \(\nu_i=b_i g_i\) the splitting is orthogonal, with both scalar forms completely explicit. The two Cauchy numerators for \(\nu,\nu g\) from the [paired-fibre formulas](../sdirk-eight-all-dirty-clock-census/FIBRE-RESIDUES.md) become \(B H_3/(P H)\) and \(B H_3 R_2/(P H)\), where \(H_3=I(L_3^2)\). Thus the grouped \(\nu e\) is zero; at each double \(d\) the grouped \(\nu\) and \(\nu e^2\) are respectively
\[
 \frac{B H_3}{P'(d)H(d)},\qquad \frac{H_3}{P'(d)}.
\]
The second uses \(\sum\nu_i e_i^2=-e_1e_2\sum\nu_i\). At each singleton \(s\) the grouped \(\nu\) is \(B H_3/[P(s)H'(s)]\). These forms retain the actual signed weights; there is no positivity premise.

## Closing the constant graph when both endpoints are singleton

A constant \(R_2=r\) implies \(F=0\) by comparing the degrees of \(P r=Q\), since \(P\) has degree three and the nonzero \(F L_4\) would have degree at least four. The constant \(r\) is nonzero. Hence the doubled labels are exactly the centered \(L_3(t)=t(t^2-3m^2/5)\) roots \(0,\pm a m\), \(a^2=3/5\).

The literal endpoints have distinct centered labels \(\pm h\), \(h=m-1\ne0\): if \(m=1\) their shared clock would be doubled. Both singleton residuals equal \(r=1/2\) by the first normalized row. Since \(A_2\) has degree at most two, \(H=L_4-r A_2-Br^2\) is monic and has no cubic term. Its four distinct roots include \(\pm h\); the other two must therefore be \(\pm j\). Thus \(H=(t^2-h^2)(t^2-j^2)\) and \(A_2\) is even. This describes the **pair data**, not the ordering. The saturated weighted mirror exists because all weights are nonzero. It has the same residual values under reflection, as the normalized residual scale at the actual terminal stage is also \(2r=1\).

In either direction the second row has a **doubled** label. Otherwise its residual is \(1/2\), so the exact second-row relation \(\kappa=1+2u-u^2=1\) with \(u\ne0\) gives \(u=2\). The actual [first-departure lemma](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) would require a repeat of the first literal clock, contrary to its singleton status. The next arguments also exclude any repeated physical *pair* across the two disjoint prefixes, as required by the complete intersection.

### Third row doubled at either end

If the third label is doubled, both later clocks in that opener are among \(m(1+\epsilon a)\), \(m(1+\eta a)\), \(\epsilon\ne\eta\) and \(\epsilon,\eta\in\{-1,0,1\}\). For arithmetic the exact clock equation is \(x_3=2x_2-1\); for star it is \(x_2+x_3=4\). Thus \(m\in\mathbb Q(a)\), with the literal phase, simple pair and nonzero residual guards retained. In a mixed opener with a singleton third row, the next paragraph shows \(m\notin\mathbb Q(a)\), so that cannot occur at the other end. The exact table tries each ordered doubled pair in both phases, comparing the two reflected pair lists. It leaves only **opposite arithmetic** at both ends: after a sign choice of \(a\),
\[
 m=1/(1+3a),\quad x_2=m(1+a),\quad x_3=m(1-a),\quad
 (g_2,g_3)=(\kappa,q)/2,\quad \kappa\ne q .
\]
The reversed pairs use the two residuals in exchanged order at those same actual double labels. Thus both copies of each of the two noncentral doubles are already consumed. At \(d=am\), Vieta gives \(B=-L_4(d)/(g_2 g_3)\), \(A_2(d)=-B(g_2+g_3)\). Then \(H(d)=(d^2-h^2)(d^2-j^2)\) recovers \(j^2\), since a doubled clock cannot be an endpoint singleton.

### Third row singleton

Since \(\kappa\ne1\), star cannot give \(q=1\). In arithmetic \(q=q_{\rm num}(u)/D(u)\) with \(D=-2+u+4u^2-u^3\). The exact identity
\[
 q_{\rm num}(u)-D(u)=4u(u-2)(u^3-3u^2+1)
\]
forces \(u^3-3u^2+1=0\), since both prefix guards are nonzero. The cubic is irreducible over \(\mathbb Q\); an element of degree three is not in \(\mathbb Q(a)\). A central second doubled label \(x_2=m\) would place the third at the other literal endpoint \(2m-1\), which is impossible because that label is a singleton already used at the terminal row. Thus its orientation \(\epsilon\) is \(\pm1\). The two cubics in \(m\) for the two orientations have exact gcd one over \(\mathbb Q(a)\). Hence both ends choose the same normalized orientation (allow the sign choice \(a\mapsto-a\)), and the third stages consume the other two singleton labels, \(t=\pm j\). These data fix \(j^2=(1+2u-m)^2\) and \(m=(u+1)/(1+a)\). At \(d=am\) the known \(g_2\) fixes \(B\) through
\[
 B g_2(g_2-r)=L_4(d)-\frac{g_2}{r}(L_4(d)-H(d)).
\]
Its denominator is nonzero because \(g_2\ne0,r\). Using \(\theta=a+u\) gives a degree-six field checked in the replay, with inverse coordinates, so arbitrary algebraic choices are covered.

## Literal fourth reads, including singular pivots

For each remaining pair of ends, the fourth stage cannot reuse a singleton occupied by either prefix, or a physical pair already used. Let \(T_2=a_0+b_0x+c_0x^2\) interpolate the genuine first three \(g\)'s. With \(J\) the primitive based at zero, the actual \(F_3\) read on \(\mathbf g-T_2(\mathbf x)\) gives
\[
 g_4 [1-\Lambda(x_4)+b_0+c_0\Delta(x_4)]
      =T_2(x_4)-JT_2(x_4),\qquad
 \Lambda=1+(x-1)/\kappa,\quad
 \Delta=\tfrac43+\tfrac{2(\kappa+1)}{3\kappa}(x-1).
\]
This is the same actual diagonal read as in the [five-double proof](../sdirk-eight-all-dirty-clock-census/README.md#3-exact-two-ended-fourth-read-exclusion-on-every-mesh), not a stage construction or rank-only test. In the opposite double case the only remaining fourth choices are the central double and the two remaining singletons. At the center, the replay takes the gcd of the affine fourth-read polynomial in \(g_4\) and \(U(0,g_4)\); at the singletons it takes the gcd in \(x_4\) against \((x_4-m)^2-j^2\) with \(g_4=r\) substituted. In the mixed case all singletons are consumed, leaving the central double and the second unused root at each noncentral double; the latter is evaluated using Vieta. The affine read is never divided by its coefficient. If both affine coefficients vanished, its gcd would retain the full quadratic, not erroneously reject a free root. Every candidate is rejected over its exact field, and hence over every extension.

## Replay and scope

Run `python check_const_ends.py` with SymPy 1.14 (tested with flint ground types). The replay covers the exact overlap table, extension fields and inverse coordinates, and all actual fourth clock/residual choices. The [Lean source](../../lean/RKCert/Research/SDIRKEightDirtySevenClock.lean) is a staged scalar companion for the two-atom norm identity and cubic opener split; the tableau splitting and chronological exclusion are not end-to-end native Lean in this packet. Nothing here excludes remaining constant cases with doubled endpoints or asserts a new stage bound.
