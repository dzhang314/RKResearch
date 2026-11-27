# Three physical quadratic-zero stages are impossible at the strict SDIRK8 floor

**Result.** Let \(A,\boldsymbol b\) be a ten-stage strict SDIRK tableau of order at least eight over a characteristic-zero field. Set \(\boldsymbol c=A\boldsymbol1\), \(\boldsymbol g=A\boldsymbol c-\boldsymbol c^{\odot2}/2\) and \(U=\ker\operatorname{diag}(\boldsymbol g)\). Exactly three zero-residual rows at three distinct clocks are impossible, including with zero output weights. Combined with the [one/two-clock exclusion](../sdirk-eight-two-zero-clocks/README.md), exactly three physical zero rows are impossible. This proof does not decide larger zero sets or the zero-free case. The unrestricted stage interval remains **10–11**.

## 1. Counting active off-zero clocks

The [supported-line exclusion](../sdirk-eight-three-zero-exclusion/README.md) reduces exactly three zero rows at distinct clocks to \(d_2=0\), \(d_3\in\{1,2\}\), where \(d_j=\dim(E_j\cap U)\), with an off-zero silent stage. Use the saturated flags and \(C=\operatorname{diag}(\boldsymbol c)\), \(G=\operatorname{diag}(\boldsymbol g)\), \(B=\operatorname{diag}(\boldsymbol b)\), \(M=CA-AC-A^2\). “Active” means \(b_i\ne0\); “off-zero” means \(g_i\ne0\). Since \(d_2=0\), \(F_3=GE_1\) and \(F_4=GE_2\) vanish on \(U\).

Weighting sends \(E_2\) isomorphically onto \(W_2\): ordinary probes detect its scalar trace and at least one active off-zero stage detects the pure line \(\langle\boldsymbol g\rangle\). The [two-sided support identity](../sdirk-eight-two-zero-line/README.md) gives
\[
       \operatorname{rank}(E_2|_{\rm active,\ off})=4-\dim(W_2\cap U_{\rm row})=1+d_3 .
\]
Let \(n\) be the number of distinct active off-zero clocks. The scalar part alone has rank \(\min(n,3)\). If this is the full rank, the nonzero residual is a function of clock on those rows. Since \(n\le6\) by the required off-zero silent stage, the paid identities \(\boldsymbol b^{\mathsf T}C^j\boldsymbol g=0\), \(0\le j\le5\), then force every ordinary off-zero aggregate weight to vanish, contradicting ordinary four-site rank with only three zero clocks. Thus \(d_3=1\) forces \(n=1\), and \(d_3=2\) forces \(n=2\) (with \(n=1\) the full rank is at most two).

At one or two active off-zero clocks, the first three residual-power sums separate using \(\boldsymbol b^{\mathsf T}C^jG^\ell\boldsymbol1=0\), \(j=0,1\), \(\ell=1,2,3\). A group with nonzero ordinary aggregate weight must have at least four different nonzero residuals: otherwise the polynomial of degree at most three vanishing on those values contradicts the three paid moments and the nonzero constant term. At most one clock can have nonzero ordinary aggregate, because there are only seven off-zero physical rows. Four ordinary sites are required, so that clock \(d\) and the three zero clocks are distinct, with all three zero weights active. Ordinary moment orthogonality of the monic nodal polynomial identifies these four clocks as the fourth shifted Legendre roots. In particular \(d\ne1/2\), and no zero clock is zero.

The last weight is nonzero by trimming. The row \(\boldsymbol b^{\mathsf T}G\) is nonzero and spans the same \(Z_2\) line as \(\boldsymbol b^{\mathsf T}M\), whose terminal coefficient \(-b_{10}\gamma^2\) is nonzero. Thus the terminal stage is off-zero, and \(D(1)\) gives \(c_{10}=1-\gamma\). The first clock is \(c_1=\gamma\).

## 2. One active off-zero clock

If \(d_3=1\), then \(\gamma=1-d\). The actual row \(\boldsymbol b^{\mathsf T}(C-dI)\in W_1\) is supported on all three zero rows. Right multiplication by \(A\) reads its reflected primitive \(J^*(X-d)\), \(J^*p(X)=\int_X^1p(t)\,dt\), plus a pure part in \(Z_2=\langle\boldsymbol b^{\mathsf T}G\rangle\) that vanishes there. At the last chronological zero \(z\), the literal row reads only the common diagonal. Canceling its nonzero weight gives
\[
                 (1-z^2)/2-d(1-z)-(1-d)(z-d)=0.                     \tag{1}
\]
The exact replay excludes every distinct ordered Gauss pair \(d,z\).

## 3. Two active off-zero clocks

If \(d_3=2\), write \(e\ne d\) for the canceled active off-zero clock. Weighting \(E_3\) is injective: ordinary probes detect its cubic trace, and \(F_3=GE_1\) is detected at the two distinct active off-zero clocks. Therefore \(E_3^{\mathsf T}B=W_3\), and the silent coordinate axes lie in \(\operatorname{Ann}(W_3)=F_4\). Since \(F_4=GE_2\) and \(G\) is injective on \(E_2\), the kernel of weighting on \(F_4\) has dimension \(\dim(W_2\cap U_{\rm row})=1\). There is exactly one silent stage, off-zero. Of the six active off-zero stages, four belong to the aggregate-active \(d\), and two to \(e\); the latter have equal residual by their first paid residual sum and zero total weight.

The polynomial \(r(X)=(X-d)(X-e)\) gives the supported \(W_2\) row \(\boldsymbol b^{\mathsf T}r(C)\), nonzero at at least two zeros. The silent clock \(s\) is neither \(d\) nor \(e\), else \(r(\boldsymbol c)\) would itself be a nonzero supported \(E_2\) column. No nonzero \(W_1\) row is supported because its affine trace would vanish at both \(d,e\); hence \(W_1G=Z_3\) is clean on \(U\). The same terminal-on-support argument at the latest supported zero \(z\ne d,e\) gives
\[
        (1-z^3)/3-(d+e)(1-z^2)/2+de(1-z)-\gamma(z-d)(z-e)=0.        \tag{2}
\]

Every zero row has actual index at least five. At a zero clock \(a\ne0\), the prefix readings \(\boldsymbol e_i^{\mathsf T}A^j\), \(j=0,1,2\), of \(\boldsymbol1,\boldsymbol c,\boldsymbol c^{\odot2}\) have determinant \(-a^6/72\) by \(F_4\)-cleanness, and kill \(\boldsymbol g\). The four prefix columns are independent because \(g_1\ne0\). The nonzero row \(\boldsymbol e_i^{\mathsf T}M\) annihilates those columns, forcing prefix width at least five.

The [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) give \(c_3+c_2=4\gamma\) (star) or \(c_3=2c_2-\gamma\) (arithmetic). The first two clocks differ. In the star, the third has only the first strict predecessor, so equality with either earlier clock makes a literal twin; in the arithmetic case either equality also forces \(c_2=\gamma\). Thus these first three distinct off-zero clocks exhaust \(d,e,s\). The terminal clock is in \(\{d,e\}\). Combining \(c_1=\gamma,c_{10}=1-\gamma\) gives the eight cases below. The only unlisted arithmetic case, with \(c_1=s,c_{10}=e,c_2=d\), would force \(2d=1\).

| Case | Chronology | \(e\) | \(\gamma\) |
|---|---|---:|---:|
| 1 | \(c_1=d\) | \(1-d\) | \(d\) |
| 2 | \(c_1=e,c_{10}=d\) | \(1-d\) | \(1-d\) |
| 3 | \(c_1=e,c_{10}=e\) | \(1/2\) | \(1/2\) |
| 4 | \(c_1=s,c_{10}=d\), star | \(4-5d\) | \(1-d\) |
| 5 | \(c_1=s,c_{10}=d\), arithmetic, \(c_2=d\) | \(3d-1\) | \(1-d\) |
| 6 | \(c_1=s,c_{10}=d\), arithmetic, \(c_2=e\) | \(1/2\) | \(1-d\) |
| 7 | \(c_1=s,c_{10}=e\), star | \((4-d)/5\) | \((1+d)/5\) |
| 8 | \(c_1=s,c_{10}=e\), arithmetic, \(c_2=e\) | \((1+d)/3\) | \((2-d)/3\) |

## 4. Exact replay and domain

The [standalone Python replay](check_silent.py) uses exact interval arithmetic on four certified rational Gauss brackets. Its twelve lines give the sign of (1), then the eight signs of (2), in the table order. Each of the 108 tests is nonzero. All four roots of the relevant quartic are real and simple by the four disjoint sign-changing brackets, so an embedding of \(\mathbb Q(d,z)\) into \(\mathbb C\) establishes these nonvanishings in any ambient characteristic-zero field. A global order on that field is not needed.

The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8ThreeZeroSilentScalarReceipt.lean) checks the eight-case chronology from scalar hypotheses over characteristic-zero fields, the Gauss bracket signs, and the two explicit field gates over ordered fields. It compiled on Lean/Mathlib 4.36.0 with only standard axioms. The actual graded-tableau reduction and transfer from the brackets to arbitrary characteristic-zero fields are the proof above, not a single Lean nonexistence theorem.
