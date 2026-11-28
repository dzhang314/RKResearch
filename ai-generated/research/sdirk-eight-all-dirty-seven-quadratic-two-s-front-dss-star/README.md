# A two-singleton front cannot face a D,S,S star at the doubled endpoint

Assume a strict ten-stage SDIRK method has ordinary order at least eight over a characteristic-zero field, all physical quadratic defects nonzero, exactly seven distinct clocks, and exactly one singleton physical endpoint. At the singleton end, the [opening restriction](../sdirk-eight-all-dirty-seven-quadratic-sdd-dss-arithmetic-new/README.md) leaves exactly two singleton labels in the first three rows (S,S,D or S,D,S). This packet excludes a genuine **D,S,S star** at the opposite, doubled end. If that end opens D,S,S, its third row must therefore use true arithmetic. The rear one-extra-D cases and rear arithmetic are not decided here, and the general 10–11 interval is unchanged.

## Actual front pairs and reverse star axis

Orient from the singleton, using the actual weighted mirror if necessary. Normalize the diagonal to one and write \(y=x-1\), \(m=1/(2\gamma)\), \(H=2(m-1)\), \(t=y-H/2\). The first singleton is \(y=0\), the terminal double is \(y=H\ne0\), and reversing sends \(y\) to \(H-y\). Let \(d\) be the later front D label and \(s\) the other later front singleton, with known forward physical defects \(f_d,f_s\). The [literal phase formulas](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) give
\[
\begin{array}{c|ccc}
\text{forward phase}&s&f_d&f_s\\\hline
\mathrm{A2}\ (\text{D second})&2d&\kappa(d)/2&q_{\rm ar}(d)/2\\
\mathrm{A3}\ (\text{D third})&d/2&q_{\rm ar}(d/2)/2&\kappa(d/2)/2\\
\text{star (either actual order)}&2-d&\kappa(d)/2&\kappa(d)/2 .
\end{array}
\]
Here \(\kappa(z)=1+2z-z^2\), \(q_{\rm ar}(z)=N(z)/D(z)\), \(D(z)=-2+z+4z^2-z^3\), \(N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2)\). All actual literal clock, phase and residual guards are used. In particular the first-departure guard of a singleton first clock forbids a forward gap of two. For a forward star the physical second offset can be \(s\) or \(d\); these two possibilities have the same pair data but do not require any row permutation theorem.

A genuine reverse star with actual gap \(v\) has later offsets \(v,2-v\) and equal nonzero defects \(\kappa(v)/2\) in reverse normalization. Its two later labels in original coordinates are \(c\pm(v-1)\) for \(c=H-1\). These are distinct and their original defects also coincide because reverse scaling is common. The [genuinely quadratic singleton graph](../sdirk-eight-all-dirty-seven-affine-final/README.md) consequently has that exact axis. Write
\[
 R=\frac{W}{2W_0},\qquad W=y^2-2cy+W_0,\qquad W_0=W(0)\ne0 .
\]
This uses \(R(0)=1/2\), and it does not assume the two roots of \(W\) are distinct or split. If \(H=2\), its axis is the centered origin \(H/2\), forcing a centered or antipodal root pair in the algebraic closure, forbidden by the [single-end parity lemma](../sdirk-eight-all-dirty-seven-quadratic-one-singleton-arithmetic/PARITY.md). Hence \(H\ne2\). For the rear star either actual ordering of the two observed labels produces this same axis and normalized graph equation by applying the formula to its own gap. No computation reorders an actual method.

## The gap-free normalized nodal necessity

The two disjoint physical prefixes have now consumed **all four** singleton labels \(0,s,c+(v-1),c-(v-1)\). Let \(X=(v-1)^2\), \(\Sigma=c^2-W_0\), \(\Delta=X-\Sigma\). The literal reverse defects on the singleton graph give \(\Delta\ne0\). By the [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md), the true singleton quartic \(\mathcal H=L_4-R(A_2+B R)\) has precisely those four simple roots and nonzero leading coefficient \(h_4\). Thus
\[
 \mathcal H=h_4\,y(y-s)\bigl((y-c)^2-X\bigr).
\]
Over the monic quadratic quotient, \((y-c)^2-X\equiv-\Delta\), \(y(y-s)\equiv(2c-s)y-W_0\). This remains true at a repeated root of \(W\); it is a polynomial remainder, not interpolation assuming two distinct graph roots. Write \(L_4\bmod W=l_0+l_1 y\). The equality \(L_4\equiv\mathcal H\bmod W\) implies
\[
                l_0=h_4\Delta W_0\ne0,\qquad
                W_0l_1+(2c-s)l_0=0 .
\]
The actual forward singleton graph read is \((2f_s-1)W_0=s(s-2c)\). Multiplying and cancelling only \(W_0\ne0\) gives
\[
                            s l_1-(2f_s-1)l_0=0.       \tag{N}
\]
This condition is independent of the reverse gap, and holds even if both \(2f_s-1\) and \(s-2c\) vanish. The latter possibility is handled separately below; neither is used as a universal pivot.

## Regular front amplitude: terminal reused versus terminal new

Since \(s,W_0\ne0\), the symmetric clock condition \(s=2c\) is equivalent to the half-amplitude condition \(f_s=1/2\). In the regular case both fail and the observed front pair fixes the entire graph normalization:
\[
                         W_0=\frac{s(s-2c)}{2f_s-1}.
\]
Use \(\mathcal Q=L_3-F_*L_4\) proportional to \(P R\), where \(P\) is cubic on the three D labels and \(F_*\) is affine with nonzero slope. The monic Legendre modes are evaluated at \(t=y-H/2\). Coprimality of \(L_3,L_4\) gives nonzero \(L_4\) at D labels and also that \(L_4\) is a unit modulo \(W\). This follows over the algebraic closure and remains true with a repeated graph root. These are the only Legendre pivots.

**Terminal reused (\(d=H\)).** Now \(W\) is rationally specified by \(H\) in each forward phase. Recover \(F_*=(L_3/L_4)\bmod W\) using division in the quadratic quotient, then the exact cubic \(M_3=\mathcal Q/W\). The required double is \(M_3(H)=0\), not just \(\mathcal Q(H)=0\): this keeps a possible common root of \(W,P\) at \(H\) rather than dividing by \(W(H)\). Check (N) alongside the terminal equation. Their exact guarded univariate gcds are units for all three front phases. The two row degrees are \((21,12)\) for A2, \((11,5)\) for A3 and \((10,5)\) for star.

**Terminal new (\(d\ne H\)).** Fit \(F_*\) through the actual D labels \(H,d\), and put \(M_3=\mathcal Q/[(y-H)(y-d)]\), an exact cubic. The two coefficients of \(M_3\bmod W\) must vanish, since \(M_3\) is proportional to \(R\) times the remaining D linear factor. Use those two equations and (N), with unknowns \(H,d\). This is not evaluation at just graph roots where a common label could be lost. For each front phase the replay computes each of the three pairwise integer resultants in \(d\), and then their gcd after stripping only actual \(H\)-guards. Specialized leading coefficients need not remain nonzero. The degree triples are \((82,80,84)\), \((33,23,22)\), \((32,23,22)\) for A2, A3 and star. The latter two gcds are units.

The A2 projected factors are \(H-3\) and \(H^3-6H^2+9H-3\), both simple. In their exact abstract fields the univariate \(d\)-gcd is linear. At \(H=3\) it forces \(d=2\), forbidden by first-departure. In the cubic it forces \(d=H-1\) and \(d^3-3d^2+1=0\), which is the singular half-amplitude chart below, not a regular solution. There is no rational-only or real-root assumption in either specialization.

## The half-amplitude branch independently

If \(s=2c\) and \(f_s=1/2\), A3 would have \(\kappa(d/2)=1\), so its actual gap \(d/2\) would be 0 or 2. The first is a clock collision and the second violates first-departure. In a forward star, \(\kappa(d)=1\) would give \(d=0\) or \(d=2\), making one of the actual later labels \(d,s=2-d\) equal to the first singleton. Thus these two phases are impossible.

In A2, \(s=2d=2c\) gives \(d=c=H-1\). It cannot be the reused terminal \(H\). The paid arithmetic value \(q_{\rm ar}(d)=1\) and
\[
                         N(d)-D(d)=4d(d-2)(d^3-3d^2+1)
\]
give \(d^3-3d^2+1=0\), since \(d=0,2\) are forbidden. The cubic is irreducible over \(\mathbb Q\). No division by \(2f_s-1\) or use of the regular graph formula is now made. Instead \(F_*\) is fixed by the two distinct paid D anchors \(H=d+1,d\); form \(M_3=\mathcal Q/[(y-H)(y-d)]\). The graph axis \(c=d\) forces the remaining D coordinate \(e\) by Vieta:
\[
             e=-[y^2]M_3/[y^3]M_3-2c.
\]
Only the genuinely quadratic slope is used to divide by the cubic leading coefficient. The exact cubic-field replay gives \(M_3(e)\ne0\); this contradicts the actual third D. It excludes every embedding of the cubic, without guessing a value for the half-amplitude graph scale. All regular and half-amplitude branches are exhausted.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_two_s_dss_star.py` with SymPy 1.14 and python-flint 0.8. Both regular and singular paths are exact. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoSFrontDssStar.lean) checks the nodal remainder, normalized scalar elimination and half-amplitude arithmetic factor. The full rooted-order and polynomial exclusion is a mathematical proof with exact replay, not an end-to-end native Lean or positive-characteristic theorem.
