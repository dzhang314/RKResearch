# Paying the degree of an omitted column response

Let \(A\), \(\mathbf b\), \(H=p-1\), and \(E_h\) be as in the named row note. Write \(N\coloneqq A^\mathsf T\). For \(r\ge0\), let \(\mathcal C_r\) be the span of all vectors obtained from \(\mathbf b\) by applying \(N\) at cost one and \(\operatorname{diag}(\boldsymbol\Phi_t(A))\) at cost \(d(t)=|t|-1\), with total cost at most \(r\). One can equivalently use diagonal multipliers from \(E_k\) at cost \(k\), by linearity. Set \(\mathcal C_{-1}\coloneqq0\).

Choose a set \(D\) of omitted indices with \(\mathbf b|_D=0\). Let \(R\) restrict to the retained set \(S=D^c\), and let \(P_D\) insert a vector supported on \(D\). Suppose there is a chronological family of relations, written as the rows of \(Q\), with
\[
 QP_D=I,
 \qquad QE_h=0,
 \qquad (Q\mathbf x)_i=x_i-\sum_{j<i,\ j\in S}\lambda_{ij} x_j\quad(i\in D),
\]
where \(0\le h<H\). The matrix \(I-P_DQ\) then restores each omitted coordinate from surviving earlier coordinates. In a proof before physical deletion, the effect of all omitted columns can be represented by a matrix \(U\) satisfying
\[
 RU=RAP_D.
\]
The entries of \(U\) at omitted rows are arbitrary; they do not affect any retained recursion. Indeed, set \(\widehat A\coloneqq A-UQ\). Its omitted columns have zero entries at every retained row because \(QP_D=I\). Its retained rows and output give exactly the chronological deletion with unchanged surviving diagonals. Even if a freely chosen omitted row no longer satisfies the triangular constraint, that row does not enter this reduced tableau.

## An exact visibility bound for the chosen response

Suppose the columns of \(U\) lie in \(E_g\). Set
\[
 \delta\coloneqq\max(0,g-h-2),\qquad
 \ell\coloneqq H-h-2.
\]
If \(\ell<0\), no propagated error can reach degree \(H\); the old output has zero weight on \(D\), so the deletion is safe. Otherwise, put
\[
 L\coloneqq \ell+\delta\left\lfloor\frac{\ell}{h+2}\right\rfloor.
\]
A sufficient condition to preserve order \(p\) is
\[
 U^\mathsf T\mathcal C_L=0. \tag{6}
\]
In particular, with no selector gap (\(g\le h+2\)), the ordinary visibility condition is enough even if two changed branches can occur in the same root product. For a single stage, an easy zero-gap sufficient condition is \(\mathbf e_i\in E_{h+1}\), since then \(A\mathbf e_i\in E_{h+2}\). The actual test on \(R A \mathbf e_i\) permits a lower-degree lift even when \(\mathbf e_i\) itself is not yet in the flag.

Here is the degree calculation. Put \(\boldsymbol\Delta_t\coloneqq\boldsymbol\Phi_t(\widehat A)-\boldsymbol\Phi_t(A)\). Its extension identity is
\[
 \boldsymbol\Delta_{[t]}=\widehat A\boldsymbol\Delta_t-UQ\boldsymbol\Phi_t(A).
\]
It gives \(\boldsymbol\Delta_t=0\) through degree \(h+1\). Induction also gives, for every \(k=d(t)\),
\[
 \boldsymbol\Phi_t(\widehat A)\in E_{k+\delta\lfloor k/(h+2)\rfloor}. \tag{7}
\]
For an extension, the \(A\) term raises the bound by one. The \(UQ\) term vanishes for children of degree at most \(h\), since those retain their old values. In any other extension the new degree is at least \(h+2\), so the right-hand bound already includes \(E_g\). For a rooted sum, add the two degree bounds and use superadditivity of the floor in (7).

For each difference of root products use the exact identity
\[
 \bigodot_{j=1}^m\widehat{\mathbf x}_j-\bigodot_{j=1}^m\mathbf x_j
 =\sum_{j=1}^m\left(\bigodot_{k<j}\widehat{\mathbf x}_k\right)\odot
 (\widehat{\mathbf x}_j-\mathbf x_j)\odot\left(\bigodot_{k>j}\mathbf x_k\right),
\]
with empty products equal to \(\mathbf1\). Recursively applying this identity and the extension identity expresses any discrepancy as a sum over paths from occurrences of \(-UQ\boldsymbol\Phi_t(A)\) to the output. Every nonzero occurrence consumes at least \(h+2\) degrees, for a child of degree at least \(h+1\) and its extension. Therefore the remaining original cost through degree \(H\) is at most \(\ell\). Some siblings on the path may be evaluated with \(\widehat A\). By (7) the total extra cost to use them as ordinary numerical multipliers is at most \(\delta\lfloor\ell/(h+2)\rfloor\). This estimate is on sibling products, not on the number of recursive occurrences.

Move these path operations onto \(\mathbf b\). Within the new total cost \(L\), every intermediate dual vector is still an ordinary context: when applying the modified operator, the difference
\[
 \widehat A^\mathsf T\mathbf z-N\mathbf z=-Q^\mathsf T U^\mathsf T\mathbf z
\]
is zero by (6). The pairing at the occurrence is also zero by (6). The output has no separate deleted-coordinate correction because \(\mathbf b|_D=0\). This proves exact preservation.

## A rank test on the named cut

For fixed \(g\) and the corresponding \(L\), solvability of the compensator constraints is exactly
\[
 \operatorname{im}(RAP_D)\subset R(E_g\cap\mathcal C_L^\perp). \tag{8}
\]
Equivalently, every \(\mathbf z\in(E_g^\perp+\mathcal C_L)\cap K^S\) satisfies
\[
 (A^\mathsf T\mathbf z)|_D=0. \tag{9}
\]
Indeed, the annihilator in the retained coordinates of \(R(E_g\cap\mathcal C_L^\perp)\) identifies with \((E_g^\perp+\mathcal C_L)\cap K^S\). Pairing with each omitted column gives exactly (9).

In a stage-minimal tableau, whenever the specified low-order relations \(Q\) exist for a nonempty inactive \(D\), (8) must fail for each tested \(g\) whose visibility budget applies. Thus some actual retained-supported combination \(\mathbf z\) in (9) sees an omitted column. In particular, since \(E_H=K^s\) in a stage-minimal tableau, choosing \(g=H\) removes the \(E_g^\perp\) term and forces a witness from the actual backwards context space, supported on the retained rows. This is more specific than showing that some unrestricted output context reaches the removed row. If \(\mathcal C_{L+1}|_D=0\), then (6) follows for **any** matching \(U\): a context in \(\mathcal C_L\) has no mass on \(D\), and its pairing with \(U\) is the same as with the original omitted columns. Conversely, since \(\mathbf b|_D=0\), (6) itself implies \(\mathcal C_{L+1}|_D=0\), by induction over the ordinary context operations. The freedom in \(U\) lowers the degree cost; it does not turn a genuinely visible cut into an invisible one at the same measured order.

## Why arbitrary ordinary invisibility is insufficient without a degree argument

Take any exact order-seven lower-triangular base, keep its outputs, and append two zero-weight probe rows with distinct clocks. They can read the first old stage with an appropriate coefficient to set their row sums. Choose a vector \(\mathbf v\) supported on those probes with \(\mathbf1\cdot\mathbf v=0\) and \(\mathbf c\cdot\mathbf v=1\), where \(\mathbf c=A\mathbf1\). Append three zero-weight rows \(j<i<i'\) with the same diagonal and no mutual feeds. Row \(j\) reads a fixed prefix vector \(\mathbf a\); rows \(i,i'\) both read \(\mathbf a+\mathbf v\). Thus the three clocks agree. The rows at \(i,i'\) agree for every tree, while row \(j\) first differs from them on the chain vector \(A\mathbf c\) of degree two, by exactly one.

Append three receiver rows, labeled \(\theta=0,1,2\), at a common diagonal \(\gamma\) and with no reads between receivers. Their only varying reads are coefficients \(\theta\) at \(i\) and \(-\theta\) at \(i'\); their other reads are common and avoid \(j,i,i'\). Give them the additional output weights \(\mathbf w=(1,-2,1)\), extended by zero off the receiver rows. Their original tree values are identical at every order, because the read of the contrast is always zero. The receiver outputs contribute zero, so the original method still has order seven. The vector \(\mathbf w\) is an eigenvector of \(A^\mathsf T\) with eigenvalue \(\gamma\), and every original tree multiplier preserves its line. The older output contexts are supported on original old rows. Thus every ordinary original output context has zero coordinate at \(i\), at every cost.

Nevertheless, delete \(i\) by its true low-order relation with \(j\) through degree one. The new receivers see the nonzero contrast between \(j\) and \(i'\) at degree two. Their extension values at degree three are affine in \(\theta\) with slope \(-1\). The rooted sum of two copies of that extension has degree six; its receiver contribution is \(\sum_\theta w_\theta(B-\theta)^2=2\), where \(B\) is the common constant term. This violates the order-seven weight, which was unchanged in the original. This tests a specified premature restoration, not minimality or the existence of other deletions: for example, the original base alone already has the required order. It shows exactly where a proof relying on only ordinary invisibility and disregarding changed sibling degrees can fail.
