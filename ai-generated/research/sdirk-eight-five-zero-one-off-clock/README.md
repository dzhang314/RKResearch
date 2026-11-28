# Exactly five quadratic zeros rule out one physical off-zero clock

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight over a field of characteristic zero or greater than seven. Write $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, and $\gamma\ne0$ for the common diagonal. A physical zero means $g_i=0$, irrespective of $b_i$.

**Result.** If exactly five physical stages have $g_i=0$, then the five other physical stages cannot all have the same clock. This excludes the entire one-off-clock stratum over every paid field. It is not a general ten-stage exclusion.

## 1. A one-clock support forces a midpoint and four end zeros

Suppose the five off-zero clocks all equal $d$, so $d=c_1=\gamma$. Put $U=\ker G$, and $r(X)=X-\gamma$. The supported columns $r(\mathbf c),r(\mathbf c)^{\odot2}$ are independent in the forward grade-two space $E_2$: ordinary quadrature has at least four different nonzero clock masses by the size-four Hilbert moment rank, of which at least three are away from $d$. Thus $d_2=\dim(E_2\cap U)\ge2$.

If $\mathbf b^{\mathsf T}G=0$, every off-zero weight is zero. Then $\mathbf b^{\mathsf T}C^j$, $0\le j\le3$, furnish four independent supported rows in $W_3$, contrary to the [support restriction identity](../sdirk-eight-two-zero-line/README.md)
$$
\dim(W_3\cap U_{\rm row})=5-d_2\le3.
$$
So $\mathbf b^{\mathsf T}G$ spans the pure grade-two reverse line paired with $\mathbf b^{\mathsf T}M$, $M=CA-AC-A^2$. The final physical weight and hence the final entry of that pure line are nonzero. Thus $g_{10}\ne0$ and $c_{10}=d=\gamma$; $D(1)$ also gives $c_{10}=1-\gamma$, so $\gamma=1/2$.

The first two clocks differ, so $g_2=0$ and the normalized front gap $u=(c_2-\gamma)/\gamma$ satisfies $u^2-2u-1=0$. The [actual first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) distinguish the star and arithmetic phase; the third physical clock differs from $d$, and hence $g_3=0$. The two last weights are nonzero and the two last clocks differ; hence $g_9=0$, and the normalized reverse gap $v=(c_{10}-c_9)/\gamma$ also satisfies $v^2-2v-1=0$ by proportionality of the actual reverse quadratic row to $\mathbf b^{\mathsf T}G$. The [literal reverse ghost gate](../sdirk-eight-four-zero-gaussian-rear/README.md) rules out silent stage 8 when its second reverse gap makes the quadratic defect zero. Thus stage 8 is live, its clock differs from $d$ by the literal reverse three-row identities, and $g_8=0$. Neither argument tries to divide by an off-zone or front silent weight.

Four physical zero clocks are therefore explicit. In chronological order with the one remaining zero clock $a$ placed between them, the five-zero block has clocks
$$
a_2=(1+u)/2,\quad
a_3=\begin{cases}(3-u)/2&\text{star}\\(1+2u)/2&\text{arithmetic},\end{cases}
\quad a,\quad
a_8=\begin{cases}(v-1)/2&\text{star}\\(1-2v)/2&\text{arithmetic},\end{cases}
\quad a_9=(1-v)/2.
$$

## 2. Exact six-site scalar projection

Put $P(X)=(X-1/2)(X-a_2)(X-a_3)(X-a_8)(X-a_9)$ and use the ordinary polynomial mean $I(X^j)=1/(j+1)$. Every actual stage annihilates $(X-a)P(X)$, whether or not clocks repeat or weights vanish. Hence the degree-six and degree-seven quadrature equations give
$$ m_1= a m_0,\quad m_2=a m_1,\quad m_0m_2-m_1^2=0,\qquad m_j=I(X^jP(X)).$$
Both gaps satisfy the same separable monic quadratic, so $v=u$ or $v=2-u$. Compute the norm of the determinant in the quadratic $u$ algebra separately for every phase and both cases. All denominators are paid. The nonpaid numerator factorizations are:

| Forward/reverse phase | $v=u$ | $v=2-u$ |
| --- | ---: | ---: |
| Star/star | $19^4$ | $19^4$ |
| Star/arithmetic | $19^2\cdot23$ | $19^2\cdot23$ |
| Arithmetic/star | $19^2\cdot23$ | $19^2\cdot23$ |
| Arithmetic/arithmetic | $23^2$ | $2281^2$ |

Thus only the prime characteristics 19, 23, 2281 can arise. Trial division verifies those primes. The replay uses the full splitting field of the gap quadratic in each characteristic, so a gap in a larger algebraic extension is not omitted. If $m_0\ne0$, the fifth clock is $a=m_1/m_0$; if $m_0=0$ both other moments must vanish. The fixed fibers all have six distinct ordinary clock positions, and their aggregate weights follow from the ordinary Lagrange cardinal rule.

## 3. The paid supported block is impossible

Let $A_U$ be the principal five-zero chronological block (diagonal $\gamma=1/2$), and $\mathbf b_U$ its **literal** weights, not sums except where specified by ordinary quadrature. All positive powers of $r(\mathbf c)$ are supported there. Forward $F_2$ vanishes on $U$ because $F_2$ is spanned by $\mathbf g$, so
$$A_U r(\mathbf c_U)=(Jr)(\mathbf c_U).$$
Reverse $Z_2$ vanishes on those columns because it is spanned by $\mathbf b^{\mathsf T}G$, so also
$$\mathbf b_U^{\mathsf T}r(C_U)A_U=\mathbf b_U^{\mathsf T}(J^*r)(C_U).$$
Here $J,J^*$ are polynomial primitives from zero and to one. For every positive $i,j$ with $i+j\le6$, ordinary grade-seven pairing further gives
$$\mathbf b_U^{\mathsf T}r(C_U)^i A_U r(\mathbf c_U)^{\odot j}=I(r^i J(r^j)).$$
These are linear equations in the ten strict entries of the ordered principal block; the support identities justify omitting all other physical stages even if they intervene between the five zeros.

In characteristic order 19, 23, 2281, the fixed geometric controls comprise respectively 4, 3, 2 inconsistent augmented linear systems and 4, 1, 0 additional cases where row 8 is silent, already impossible. The exact row reductions, including the quotient-field mismatches, are printed by the fixed replay. This does not discard untested degrees of algebraic extension; all the fixed control data lie in the complete quadratic splitting field.

The remaining free fifth clocks are star/star at 19 (four ordered gap pairs) and arithmetic/arithmetic at 23 (one ordered gap pair). The already-known five clock positions are distinct in each. If $a$ differs from all five, then evaluating $I(P)=0$ against quadrature forces its weight to be zero. The other four zero weights are fixed and the polynomial block system must be solved at the univariate clock $a$. If it is any one of the known five clock positions, there is instead a univariate free literal weight at that additional row, with the known site's aggregate kept fixed. If it is the midpoint, the unknown off-zero midpoint mass can be adjusted arbitrarily in this overapproximation; all possible fifth-row weights are allowed. If it is another zero clock, the original literal zero-row weight is adjusted by subtracting the new weight. The two actual rear zero weights must remain nonzero.

The exact polynomial replay eliminates each of these six alternatives for every ordered gap pair, **24 univariate systems at 19 and six at 23**. It row-reduces over the rational function field, records every selected pivot zero as exceptional, and computes a gcd of the remaining inconsistency numerators. Every irreducible factor of the remaining possible parameter polynomial is then checked against the *entire original matrix* over its exact residue field, except a factor on which a stated distinctness or weight guard fails. This proves inconsistency in arbitrary extensions even at a rank drop and does not bound the degree of a proposed fifth clock or split weight. There are no survivors. This completes the one-clock case.

## 4. Domain and replay

The proof holds over all fields of characteristic zero or greater than seven. Over a nonzero commutative ring with $8!$, the common diagonal, and the five off-zero residuals units, if those five physical clocks already agree in the ring, maximal-ideal reduction preserves this one-clock pattern and the zero count and is likewise impossible. This is a unit-guarded corollary, not a claim about nonunit residuals or different off-zero clocks.

Run `python check_norms.py`, `python check_fixed.py`, and `python check_free.py` with SymPy 1.14 and Python-flint 0.8. The stock Lean/Mathlib 4.36.0 module `RKCert.Research.SDIRKEightFiveZeroOneOffClock` verifies the moment elimination, guarded fifth clock recovery, and the literal numerator products. The complete stage-flag reduction and finite geometric block exclusions are the source proof and exact replays, not one native `HasOrder` theorem. No stage interval changes.
