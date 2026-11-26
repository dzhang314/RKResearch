# The archived 33-stage order-twelve method has no grade-ten decoder

The obstruction is already over the rationals, so in particular it rules out a decoder over \(\mathbb Z[1/14!]\). It concerns the actual archived tableau, not just a residual-space model. The certificate uses a block elimination of formal-zero tree columns and no tableau replay.

The relevant source tableaux are the [16-stage paid order-nine witness](paid9-seed.json) and the [archived 33-stage order-twelve witness](tableau-12.json). We use their proved literal row identities, including all documented mergers. The order-nine witness consists of the original seven-stage order-six method, an inner bank of nine other physical rows, and no more. The order-twelve witness retains those 16 rows and appends the actual old order-nine output endpoint, two primitive rows at \(1/3,2/3\), four primitive rows at \(1/12,1/4,1/3,1/2\), and ten final suffix rows. The four sources of primitives in this description are the actual charts specified in the archived proofs.

## The rank criterion

For a tree \(t\), its exact derivative polynomial is \(g_t(x)\coloneqq |t|x^{|t|-1}/t!\). A stage column is **formal-zero through grade \(j\)** if it is the evaluation of a linear combination of trees of order at most \(j\) whose exact derivative polynomial is zero. Its stage coordinates need not vanish. Let \(Z_j\) be the span of these numerical columns. A linear decoder exact through grade \(j\) would annihilate \(Z_j\). It would also map the bushy-tree columns \(\mathbf1,\mathbf c,\ldots,\mathbf c^{\odot(j-1)}\) to the independent monomials. It therefore requires
\[
 \dim Z_j\le s-j
\]
for \(s\) physical stages.

The operations used below control the grade directly. Multiplication by \(A\) extends the tree and acts on the exact polynomial by integration from zero. The diagonal matrix \(C\coloneqq\operatorname{diag}(\mathbf c)\) acts by multiplication by \(x\), or rooted sum with \([\bullet]\). Coordinatewise product is rooted sum. Thus \(A\) and \(C\) each add at most one to the grade of a formal-zero column. A product of formal-zero columns of grades \(r,s\) has grade at most \(r+s-1\). These statements follow on formal tree expressions before passing to numerical columns, so they do not presume a decoder.

We exhibit independent formal-zero projections on successive literal row blocks, of ranks
\[
 6,\quad 7,\quad 2,\quad 4,\quad 5.
\]
Each selected packet is zero on all later blocks, except the last packet, which uses independent projections on the final suffix itself. This is a block-triangular rank certificate and gives \(\dim Z_{10}\ge24\).

## 1. Eliminate the six original nonorigin rows

On the original seven-stage order-six seed the clocks are
\[
 0,\quad 1/3,\quad 2/3,\quad 1/3,\quad 1,\quad 1/2,\quad 1.
\]
Let \(d\coloneqq\mathbf c^{\odot2}-2A\mathbf c\). Its exact derivative polynomial is zero at grade three. On the actual tableau \(d\) is \(1/9\) times the second coordinate vector. This is immediate from the seven literal rows; every later row is of stage order at least two, so has zero second-stage defect. All later rows also have zero incoming coefficient on column two. For the inner chart this follows from the zero second coordinate of the order-six output and its first clock-weighted read. For the outer charts the order-nine output is zero on all six original nonorigin rows, and their other readouts do not read those coordinate vectors.

It follows that \(Ad\) is supported on original rows three through seven. In that order its entries are
\[
 2/27,\quad 1/27,\quad -1,\quad 1/8,\quad 9 .
\]
Its four distinct clock groups can be isolated by multiplying by scalar Lagrange polynomials in \(C\) of degree at most three. This gives singleton axes at rows three, four and six, and the pair \((-1,9)\) on rows five and seven. The square \((Ad)^{\odot2}\) has grade seven; subtracting its already isolated singleton coordinates leaves the pair \((1,81)\). The determinant of the two endpoint pairs is \(-90\). With \(d\) this gives all six nonorigin coordinate axes as actual formal-zero columns through grade seven. The calculations use only paid divisors.

## 2. Seven independent directions in the inner order-nine bank

Write \(u\coloneqq2x-1\) for the centered clock variable and \(\omega(u)\coloneqq(1-u^2)^2\). The order-nine forward chart of grade five uses the origin and the actual order-six endpoint, the order-six zeroth and first moments, and the midpoint. On data supported on the original nonorigin rows, the three point reads are zero. Such data can therefore prescribe the two-dimensional polynomial shape \(u(1-u^2)(\alpha+\beta u)\) by the two moment reads.

There are two specific choices. The original formal-zero column \(C^2Ad\) has order-six mean zero and order-six first moment \(-1/1080\). For example the grouped weighted values of \(Ad\) at clocks \(2/3,1/3,1/2,1\) are \(1/20,1/40,-1/15,-1/120\), and their cubic moment is \(-1/1080\). Thus \(w_O\coloneqq-72 C^2Ad\) is a grade-six column on which the inner chart returns \(f_O\coloneqq u(1-u^2)\). Taking \(w_E\coloneqq(8/81)(e_3+e_4)\) returns \(f_E\coloneqq u^2(1-u^2)\): the two order-six weights there are each \(27/40\), and the clocks are \(2/3,1/3\). The latter column is available through grade seven.

Apply the full \(A\) to these two columns and subtract their original nonorigin coordinate contributions, which are formal-zero by the preceding section. Denote the resulting columns by \(V_O,V_E\); they are available through grades seven and eight, respectively. They have support only in the inner bank. In fact all later outer rows have zero direct incoming coefficients on the original nonorigin axes: the order-nine moment rows have zero coefficients there, and the outer point reads use the origin, its appended endpoint and the new preparatory stages. Inside the inner bank, the literal row formulas give
\[
 V_O=(I-T E)f_O,\qquad V_E=(I-T E)f_E,
\]
where \(T\) is the inner weighted transpose, \(E\) reads at its suffix clocks, and \(I\) is the primitive from zero at those clocks. This formula applies also to the existing pure endpoint and midpoint, by the literal mergers proved for the order-nine witness.

The five pure rows of the inner bank have centered clocks \(1,-1/2,0,1/2,2\). On them these columns are the primitive polynomials
\[
 p_O=-\omega/8,\qquad
 p_E=1/15+u^3/6-u^5/10 .
\]
The four corrected donors have reverse clocks \(1,-1/2,1/3,2/3\). Write \(y=1-x\), and denote the inner reverse \(u\)-defect profile by \(\mathsf u\), distinct from the centered coordinate \(u\). Its values on these four donors are \(0,-9/8,3/14,3/14\). Indeed, the ratio of the inner seven-site nodal derivatives at the outside site and at \(1/3\) is \(972\); the corresponding ratio of \(x(1-x)\) is \(-27/8\); and the ratio of selected masses is \(8/(3^9\cdot7)\). Their product is \(-4/21\). Symmetry gives the same ratio at \(2/3\).

For either primitive \(p_f\), let \(M_j(p_f)\coloneqq\int_0^1 y^j p_f\,dx\). The weighted coordinates of \(TE f\) on the four corrected donors, when paired with \(\mathbf1,\mathbf y,\mathbf y^{\odot2},\boldsymbol{\mathsf u}\), give
\[
 \bigl(M_0(p_f),M_1(p_f),M_2(p_f),0\bigr).
\]
This is the inner weighted transpose identity, the annihilation of endpoint-zero degree-four polynomials by its three residual modes, and integration by parts. For \(p_O\) the first four moments are
\[
 (-1/15,-1/30,-2/105,-1/84),
\]
and for \(p_E\) the first three are \((1/15,1/42,4/315)\). These can be checked by integrating even powers of \(u\). On the corrected donors the endpoint indicator equals \(1-15y+15y^2\) modulo \(\boldsymbol{\mathsf u}\), and the outside-donor indicator equals \(12(y-y^2)/5\) modulo \(\boldsymbol{\mathsf u}\). Therefore the corrected endpoint value of \(V_O\) is \(-31/210\). At the outside donor the weighted \(TE f_O,TE f_E\) values are \(-6/175,2/75\); dividing by its weight \(-1/23625\) gives \(810,-630\). With the primitive values at \(u=-2\), the actual \(V_O,V_E\) values there are
\[
 -6489/8,\qquad 9479/15.
\]

Consider the seven-dimensional prospective packet \(V_OP(u)+V_EQ(u)\) with \(\deg P\le3,\deg Q\le2\), where multiplication by the centered clock means applying \(2C-1\) coordinatewise. Every such column is formal-zero through grade ten. To prove independence, suppose it vanishes. At the pure endpoint \(p_O(1)=0\), \(p_E(1)=2/15\), so \(Q=(u-1)(\alpha+\beta u)\). At the four other pure nodes \(P=-Qp_E/p_O\). If
\[
 S(u)\coloneqq u(u^2-1/4)(u-2),\qquad
 R(u)\coloneqq\frac{1-S(u)/S(1)}{u-1},
\]
then \(R\) is a polynomial and interpolates \(1/(u-1)\) there. Since \(30p_E=(u+1)^2(-3u^3+6u^2-4u+2)\), the resulting polynomial is
\[
 P(u)=\frac4{15}\bigl[(-3u^2+3u-1)(\alpha+\beta u)+\beta+(\alpha+\beta)R(u)\bigr].
\]
At the corrected endpoint, \(V_O\ne0\) and \(Q(1)=0\), so \(P(1)=0\). Since \(R(1)=-8/3\), this is \(11\alpha+8\beta=0\). If \(\alpha\ne0\), normalize it to one, so \(\beta=-11/8\). At the corrected outside donor, \(P(-2)=-18\), \(Q(-2)=-45/4\), and the resulting combination of actual values is \(7491\ne0\). If \(\alpha=0\), also \(\beta=0\), so \(Q=0\) and the four pure values force \(P=0\). This proves rank seven.

We also require one moment of \(V_O\) as a grade-seven source for the outer blocks. Its order-nine moments in \(x\) through degree two vanish. At degree three, on the inner donors one has the actual identity
\[
 \mathbf y^{\odot3}=(59/18)\mathbf y-(5/2)\mathbf y^{\odot2}
                    -(98/27)\boldsymbol{\mathsf u}.
\]
Substitution of the four values above verifies it. Thus the degree-three \(y\)-moment of \(V_O\) is \(-1/84+59/540-1/21=47/945\), and its degree-three \(x\)-moment is \(-47/945\). This last number is not a unit in the paid ring, but it is nonzero over the rationals, which is sufficient for this obstruction.

## 3. Both outer grade-six preparatory rows

Denote the three outer preparatory charts by \(\Pi_6,\Pi_7,\Pi_8\), according to the grade through which they are exact. All of them use the origin and the order-nine output endpoint, whose derivative read is exact through grade ten. On \(V_O\), the degree-five chart \(\Pi_6\) has zero endpoint reads, zero first three old moments, and nonzero third-clock-power moment \(-47/945\). Its polynomial is therefore a nonzero multiple of the odd polynomial
\[
 (1-u^2)u(u^2-3/7).
\]
One checks the zero moments by parity and \(\int u^2(1-u^2)(u^2-3/7)=0\). The even part cannot survive: for degree at most five it has form \((1-u^2)(a+bu^2)\), with the zeroth and second moments giving a nonsingular two-by-two system.

The column \(A V_O\) is formal-zero through grade eight. It evaluates to the primitive of this odd polynomial at the two grade-six preparatory clocks, so the two entries are equal and nonzero. Indeed, the primitive in the \(u\)-coordinate starting at \(-1\) is
\[
 \frac{(1-u^2)^2(1-7u^2)}{42},
\]
whose values at \(u=\pm1/3\) are equal and nonzero. The factor \(1/2\) for the \(x\)-primitive does not matter for the rank. The actual column is zero on all later rows, because their stage-derivative reads are exact through grade eight. Multiplication by \(C\) gives a second independent projection on the two distinct third clocks, with no new support. This gives rank two on that block.

## 4. All four outer grade-seven preparatory rows

Use the two grade-eight formal-zero inputs
\[
 r_1\coloneqq C V_O,\qquad r_2\coloneqq A V_O .
\]
On both, \(\Pi_7\) gives a polynomial of degree at most six, with zero endpoint reads and zero zeroth and first moments. Its values at the thirds are equal: for \(r_1\) they are zero, and for \(r_2\) they are the equal values just proved. The odd part of such a polynomial is zero. Indeed it is \((1-u^2)u(Au^2+B)\); equality at the thirds gives \(B=-A/9\), while its first centered moment is \(A(8/189)\) up to the common normalization. Thus it is even. These two \(\Pi_7\) images are independent. The third-clock-power moment calculation for \(V_O\) gives a nonzero \(x^2\)-weighted read on \(r_1\), whose third-point reads are zero. The third-point reads of \(r_2\) are nonzero.

Their primitives span \(\omega\) times the two odd polynomials \(u,u^3\): the primitives have degree at most seven, double endpoint zeros and odd parity. The projections of \(A r_1,A r_2,C A r_1,C A r_2\) on the four grade-seven rows thus have rank three, exactly the three nonmidpoint clocks. The usual monomials \(u,u^2,u^3\) already span values on those three distinct nonzero centered clocks after division by \(\omega\). All of these numerical columns are zero on the final suffix, since \(A r_j\) has grade nine and the suffix is exact there through grade nine.

For the missing midpoint direction, let \(v_j\coloneqq[\bullet]^{\#(j-1)}\) and use the grade-eight formal-zero input
\[
 r_X\coloneqq\boldsymbol{\Phi}_{[v_7]}-\boldsymbol{\Phi}_{v_8}/7 .
\]
The two grade-six reads of \(r_X\) are the negatives of the primitive of \(g_{v_7}-\Pi_6\boldsymbol{\Phi}_{v_7}\) at the thirds. That residual has degree six, with leading centered coefficient \(1/64\), both endpoint zeros, and zero moments of degrees zero, one and two. Its even part is
\[
 -\frac1{64}(1-u^2)(u^4-2u^2/3+1/21).
\]
The displayed polynomial has the stated leading coefficient and vanishing even moments; uniqueness follows from the nonsingular weight-\((1-u^2)\) moment system on degrees zero and two. Before multiplication by \(-1/64\), its primitive in \(u\) is \(u(1-u^2)^2(1-3u^2)/21\), nonzero at \(1/3\). The odd part of the residual has equal primitive values at the two thirds, so the actual \(r_X\) reads differ there.

Consequently the odd part of \(\Pi_7 r_X\) is a nonzero multiple of \((1-u^2)u(u^2-3/7)\), by the same endpoint and first-moment constraints. Its primitive is nonzero at the midpoint, while the primitive of the even part is zero there. Thus \(A r_X\) supplies the fourth independent preparatory projection. It has grade nine and is zero on the final suffix. This section uses the pure midpoint as an actual numerical row, not as an assumed extra exact high-grade reading.

## 5. Five independent directions on the final order-twelve suffix

For a grade-at-most-nine formal-zero numerical column \(w\), \(\Pi_8 w\) is read by the four grade-seven preparatory stages and the \(x\)-weighted order-nine output; its endpoint and zeroth moment reads are zero. From the preceding construction, \(A r_1,A r_2,A r_X\) give three independent projections on the four preparatory coordinates. The grade-nine column \(C^2 V_O\) is zero on those four rows and has nonzero \(x\)-weighted output read, namely \(-47/945\). The four \(\Pi_8\) images are therefore independent.

Their negatives are four source residuals for formal-zero data. A fifth source is \(g_{v_9}-\Pi_8\boldsymbol{\Phi}_{v_9}\), which has leading term \(x^8\) and hence lies outside those four degree-at-most-seven images. All five sources have endpoint zeros and mean zero: the archived endpoint is derivative-exact through grade ten and the seed output is exact through grade nine.

For each formal-zero child column \(w\), apply \(A\) to obtain its grade-ten formal-zero column. For the fifth child use \(\boldsymbol{\Phi}_{[v_9]}-\boldsymbol{\Phi}_{v_{10}}/9\), also formal-zero. Their projections on the final suffix are the usual source corrections \((T E-I)\rho\), because all child data are exact on that suffix through grade nine. At the six actual pure suffix clocks
\[
 1/4,\quad 1/3,\quad 1/2,\quad 2/3,\quad 3/4,\quad 11/12
\]
the correction is simply minus the primitive. Each primitive has degree at most nine and double endpoint zeros, so dividing by \(x^2(1-x)^2\) leaves degree at most five. Six distinct nonendpoint evaluations are injective on this space. The five formal-zero projections are therefore independent.

## Conclusion and the literal endpoint

The successive ranks \(6+7+2+4+5=24\) all occur through grade ten, with supports ordered exactly as required for block elimination. Thus the 33-dimensional physical stage space has quotient dimension at most nine after killing formal-zero columns through grade ten. A grade-ten decoder would require ten independent model directions. No such decoder exists even over \(\mathbb Q\).

The order-twelve output row still has to be appended if using the audited paired-output affine lift: the last archived stage carries output weight one, so none of the existing strict rows equals the output. This added endpoint does not improve the grade-ten decoder rank, since its reads through grade ten equal those of the already present order-nine output endpoint. Its charge is separate from the obstruction above. Consequently the proposed 49-stage order-fourteen construction cannot be obtained by giving this fixed order-twelve tableau its one charged endpoint and applying the counted affine suffix. This does not exclude a differently constructed order-twelve seed, further mergers beyond the counted suffix, or a different order-fourteen construction.

The reusable method is to construct actual zero-polynomial tree columns in increasing grade, eliminate early supported columns, and propagate them through each literal primitive chart. At each new block one charges only independent actual coordinates at that grade; in the final block the six pure evaluations make the primitive map injective. The otherwise tempting strategy of declaring independent formal residual parameters would not give this obstruction.
