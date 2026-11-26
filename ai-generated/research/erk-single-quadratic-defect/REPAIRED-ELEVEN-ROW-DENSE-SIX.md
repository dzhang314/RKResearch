# An alternate eleven-row explicit dense chart through tree size six

This construction keeps the first seven physical rows of the sharp eight-row grade-five chart. It modifies the eighth row before appending three stages. Preserving the former eighth row would require twelve stages; the modified row still pays every grade-five input and allows a compensated grade-six observation without the extra defect.

## Literal change and resulting decoder

Use the first seven rows and the map \(\Pi_4\) from [the sharp grade-five chart](../erk-signed-reverse/SHARP-PAID-ERK-GRADE-FIVE.md). Let \(E_i\) read the raw derivative coordinate of stage \(i\). Let \(x\coloneqq1/3\), \(z\coloneqq1/4\), and write \(I_y\) for the primitive from zero at \(y\). The actual row-seven incoming row is \(I_x\Pi_4\) on the first six coordinates. Define
\[
 \ell\coloneqq E_7-\operatorname{ev}_{x}\Pi_4
             = E_7-E_6+\tfrac4{27}(E_5-E_4).
\]
The latter equality follows by evaluating the explicit coefficient formula for \(\Pi_4\) on arbitrary raw data. It is not just agreement at sampled trees.

The replacement eighth row is
\[
 I_z\Pi_4-\tfrac{243}{4096}\ell
       =(1400,0,-1312,212,-144,3645,-729)/12288.
\]
Its clock is \(z\), since \(\ell\mathbf1=0\). Both \(E_7\) and \(\operatorname{ev}_{x}\Pi_4\) are exact through size four on their respective inputs, so the contrast annihilates these actual columns. Thus the new eighth row, just like the previous one, gives exact raw derivative data at \(z\) through size five. The same formula for \(\Pi_5\) on the first eight coordinates still works: its data are the exact origin and endpoint, \(E_7,E_8\), and the same mixed midpoint coordinate.

Append three stages with literal incoming rows
\[
                    I_1\Pi_5,\qquad I_{1/2}\Pi_5,\qquad I_{2/3}\Pi_5
\]
on those first eight coordinates. This specifies their entire rows and all their clocks. Each is an exact derivative read through size six. At the six clocks \(0,1,1/2,2/3,x,z\), interpolate using the respective reads
\[
   E_1,quad E_9,quad E_{10},\quad E_{11},\quad
   E_7-\tfrac{17}{81}E_5+\tfrac{17}{81}E_9,quad
   E_8-\tfrac{49}{256}E_5+\tfrac{49}{256}E_9.
\]
This gives an exact \(\Pi_6\) once the last two reads have been checked. The interpolation nodes on the twelfth grid have indices \(0,3,4,6,8,12\), and the pairwise differences are paid over \(\mathbb U_6\).

## Why the correction works at every size-six tree

For a size-five child write \(g_t(X)=aX^4\) and let \(e\) be its actual mean discrepancy on the ordinary four-stage output. Let \(v\coloneqq2X-1,d\coloneqq-1/3\), and set
\[
 \begin{aligned}
 H&\coloneqq-\tfrac1{16}(1-v^2)(v^2-\tfrac45dv-\tfrac15),\
 S&\coloneqq\tfrac32(1-v^2)(1-dv).
 \end{aligned}
\]
The first is monic of degree four in \(X\) with mean zero. The second has degree at most three and mean one. Both are annihilated by the two endpoint conditions and the exact mixed read \(\mathcal R\) of the grade-four chart. Therefore, by uniqueness,
\[
                   \Pi_4\boldsymbol\Phi_t-g_t=eS-aH .
\]
For reference, the lower primitive of \(-16H\) is \((d-v)(1-v^2)^2/10\). It follows that \(I_xH=0\), \(I_zH=-3/5120\), and \(H(x)=4/405\). Thus \(-243/4096=I_zH/H(x)\).

The fifth row is the old order-four endpoint. At a unary root above this child its derivative discrepancy is precisely \(e\). The discrepancy of row seven there is \(e I_xS\), since \(I_xH=0\). The contrast \(\ell\) on that child's actual column has value \(-eS(x)+aH(x)\), because row seven itself is true through child size five. Consequently row eight's unary discrepancy is
\[
 e\bigl(I_zS-\tfrac{I_zH}{H(x)}S(x)\bigr)=\tfrac{49}{256}e .
\]
Here \(I_xS=17/81\), \(I_z S=31/256\), and \(S(x)/H(x)=120\). A size-six tree with two or more children has every child of size at most four, so all three rows have zero discrepancy in it. Their earlier discrepancies are also zero. This proves both of the compensated reads through every tree of size at most six. The fourth grade-five observation has changed only its future grade-six defect, not any old permitted profile.

The same cancellation works with physical clock \(z\) left variable: \(I_z\Pi_4+(I_zH/H(x))\ell\) has discrepancy \(\kappa(z)e\), where \(\kappa=I(S-120H)\). In the centered variable \(v=2z-1\),
\[
 \kappa(z)=\tfrac12+\tfrac{15d}{16}(1-v^2)^2+\tfrac14(5v^3-3v^5).
\]
This identifies the actual family of subsequent mixed reads and their individual payment requirements. The eleven-row count is sharp for any continuation retaining the first six of these rows, which already have five independent pure directions through size six, as proved in the frozen prior cost note. It matches rather than improves the distinct existing eleven-row chart.
