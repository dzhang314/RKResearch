# Eleven explicit stages suffice for order eight over the factorial localization

There is a single strictly lower triangular eleven-stage tableau with coefficients in \(\mathbb Z[1/210]\) and exact order eight. Thus every nontrivial commutative ring in which \(8!\) is a unit admits an exact eleven-stage method, even in characteristic zero without a field hypothesis. The result does not require selecting a chart or patching local solutions. The same factorial condition is necessary for order eight by the tall tree.

The [literal tableau](tableau.json) uses seven distinct nonzero-output clock sites. In physical stage order its clocks and weights are
\[
 \boldsymbol c=(0,\tfrac18,\tfrac14,\tfrac12,\tfrac12,\tfrac27,-1,2,\tfrac57,\tfrac12,1)^{\mathsf T},
 \qquad
 \boldsymbol b=(\tfrac7{80},0,0,0,0,\tfrac{16807}{38880},-\tfrac1{38880},
            -\tfrac1{38880},\tfrac{16807}{38880},-\tfrac{16}{405},\tfrac7{80})^{\mathsf T}.
\]
This is a signed witness for stage count, not a stability or positive-weight claim.

The common positive denominator is
\[
       746807040 = 2^8 3^5 5\,7^4 \mid (8!)^4 .
\]
For a rooted tree \(t\), write \(e_t=t!\,\boldsymbol b^{\mathsf T}\boldsymbol\Phi_t(A)-1\). The ninth-order bush and tall-tree failures obey the exact identity
\[
 e_{\rm bush}=-263/27440,\qquad e_{\rm tall}=551/210,\qquad
 -44\cdot27440\,e_{\rm bush}-21\cdot210\,e_{\rm tall}=1 .
\]
Consequently they cannot both vanish after any paid specialization, including characteristic 263.

## Independent checks

Run **python3 replay.py** in this directory. The script uses standard-library integer arithmetic to replay the 200 nonplane rooted conditions, matches the Lean literal numerators against the JSON, verifies the two ninth-order failures and their Bézout identity, and separately computes the actual defect ranks. In particular \(V_4\) has rank 2 with support \(\{2,3,4\}\), \(V_5\) has rank 4 with support \(\{2,3,4,6,7,8,9,11\}\), and \(V_6\) has rank 6. There are seven distinct active scalar clocks. Unlike the earlier rational six-site chart, this witness uses genuine dispersed defects.

The [native Lean certificate](../../lean/RKCert/ReviewedNative/ERK8FactorialEleven.lean) proves **RKResearch.Certified.ERK8FactorialEleven.exact_order_eight_iff**, with the reviewed **ERK** and **HasOrder** predicates. Run **lake build RKCert.ReviewedNative.ERK8FactorialEleven** from the configured ai-generated/lean project. All 626 reviewed constructor trees through size eight are checked with integer receipts, and the specialization proof is denominator-cleared.

Together with the [ordered-field order-eight stage floor](../erk-eight-stage-floor/README.md), this proves the minimum is eleven over \(\mathbb Q\) and every ordered field. The witness alone does not upgrade the unrestricted ten-stage lower bound over arbitrary nontrivial rings.

## How the seventh scalar site is paid

The earlier universal twelve-stage witness supplied a seven-site scalar rule. Here the repeated clock is instead \(f=\tfrac12\), present at an unweighted early stage 5 and the weighted penultimate stage 10; a linearly determined difference in their full rows permits the needed reverse tests. The actual fifth-order defects leak onto five weighted rows, including the terminal row, rather than staying at a pure head.

Start with \(\boldsymbol b\) and \(\boldsymbol c\) above. Write \(C=\operatorname{diag}(\boldsymbol c)\), \(\boldsymbol y=\boldsymbol1-\boldsymbol c\), and use the reflected reverse rows
\[
 \boldsymbol J_k=(k+1)A^{\mathsf T}(\boldsymbol b\odot\boldsymbol y^k)
                   -\boldsymbol b\odot\boldsymbol y^{k+1}.
\]
A graded rank-four terminal-coefficient argument suggests the quadratic \(P(X)=7X^2-7X+1\). The scalar identity used here is particularly simple: the degree-five moments of \(P(X)\,dX\) are exactly paid on \(0,\frac12,1\) with weights \(1/20,-4/15,1/20\). Thus the degree-four moments of \((1-X)P(X)\,dX\) are paid on \(0,\frac12\) with weights \(1/20,-2/15\).

Define the row difference \(\boldsymbol\delta\) between stages 10 and 5 from the seven-site coefficient \(b_i(1-c_i)P(c_i)\), canceling these two scalar masses on \(0,\frac12\), and placing the combined midpoint coefficient at stage 5 rather than stage 10. It has zero polynomial moments through degree four and vanishes on physical rows 2,3,4,10,11. Its scale is fixed by the second reverse equation on donor stage 9.

Let \(\boldsymbol r=\boldsymbol e_{10}-\boldsymbol e_5\) and \(y_i=1-c_i\). The stipulated reverse equations are
\[
 \boldsymbol J_0=\boldsymbol0,\qquad
 \boldsymbol J_1=-b_{10}y_{10}^2\boldsymbol r,\qquad
 \boldsymbol J_2=y_{10}\boldsymbol J_1+
      b_{10}y_{10}(3y_{10}-2y_9)\boldsymbol\delta .
\]
With stage 10 equal to stage 5 plus \(\boldsymbol\delta^{\mathsf T}\), the compatibility at donor 8 requires
\[
 y_8=\frac{y_9}{21y_9^2-14y_9+2}.
\]
The values \(y_8=-1,\ y_9=2/7\) meet that condition exactly, with no new denominator prime. The first five rows use the simple rank-two lower-defect prefix with \(c_3=f/2,\ c_4=c_5=f\), stage 5 exact through size five. The sixth through ninth rows then solve a linear system: their first three forward primitive moments, the specified reverse rows, and the paid next checks on the head defect and the cubic power. Exact \(\boldsymbol J_0=\boldsymbol0\) fixes the terminal row.

The optional **seven_site_head.py** performs that rational linear solve and checks actual rooted order; with its one free parameter set to zero, the first output in candidate-family.json is the frozen witness. It uses SymPy and the neighboring rational generator's checker. The authoritative certificate is the independent literal replay and reviewed Lean verification, not a numerical search or the simplification ansatz.
