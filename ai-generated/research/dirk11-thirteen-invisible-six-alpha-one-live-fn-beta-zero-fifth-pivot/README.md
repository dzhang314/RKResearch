# The fifth reverse diagonal is zero in the direct Fn beta-zero chart

**Result.** In the normalized no-late invisible-six DIRK11/13 chart
over a characteristic-zero field, assume live reciprocal multiplier,
\((\alpha,\beta,\gamma)=(1,0,5)\), and the direct noncontact old
\(F_n\) fit. The fifth regular reverse diagonal \(d_B\) is zero.
The matched column's first possible regular defect \(D_B\) is nonzero.
This is not by itself a closure of the zero-diagonal chart, any alternate
old-profile chart, or the unrestricted real stage interval **13–14**.

## 1. Literal pivot at the ordinary row, not a middle ghost

Use reverse \(Y=1-c\), \(N=A^{\mathsf T}\), \(W(f)=b_{\rm wt}f(Y)\),
and the physical prefix \(T,v,u,w,z,V,B,x\), where \(x\) is the
first of the five ghosts after \(B\), not a middle ghost.
The old cubic hull is \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\),
and \(P=Ym\) with \(m=Y^2+rY+s\) in its monic gauge.
Write \(k=G_V/b_V\), and
\[
 K_*=(V-z)(k-P(V))/P_0(V),\qquad
 Q_4=(Y-z)P+K_* P_0,\qquad D=(Y-z)G-W(Q_4).
\]
There is no division by \(V-z\). The five regular clocks are distinct
and nonendpoint with live weights; the true old \(m\) values are live.
Each ghost has zero weight and live \(G\) and reciprocal carrier \(U_r\).
All six ghost clocks are distinct but need not differ from ordinary
clocks.

The prefix-through-\(V\) part of the
[gap-column argument](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md#1-a-true-reverse-column-and-its-first-literal-pivot)
uses no middle ghost. Specifically, \(D=0\) through \(V\), and
\(\mathcal C D\in Z_6=G\mathcal P_3+H\mathbb K\),
where \(\mathcal C=YN-NY-N^2\). Its true grade-six payment uses the
weighted quartic input and the one mark on \(G\in E_7^\perp\),
as in that source. Evaluation through \(V\) is injective on \(Z_6\):
the three old clocks and \(V\) first force \(Q+\theta U_r=0\) as a
degree-at-most-three identity, then the ghost \(z\) with live
\(U_r(z)\) forces \(\theta=0\). Since the physical transpose is
lower triangular, \(\mathcal C D\) vanishes there, hence globally.
At \(B\), the immediate successor of \(V\) in this chart, its literal
value is \(-d_B^2D_B\).

Suppose \(D_B=0\). Now \(D,ND\) vanish through \(B\) by triangularity.
At \(x\), \(D_x=(x-z)G_x\ne0\) and the commutator's literal
value is \(-d_x^2D_x\), so \(d_x=0\), and thus \((ND)_x=0\).
The same whole-row fits as in the referenced gap argument, which
pay for at most one marked \(G\) and its matched weighted polynomials,
give
\[
 ND=GL-W(IQ_4),\qquad
 L=(Y-z)\ell-\rho+K_*W_0
\]
of degree at most two. Its reads at the distinct actual ghosts
\(z,x\) give both roots. If \(L=0\), then \(IQ_4\) vanishes at
all five regular clocks and at the polynomial origin. Its degree is
at most five, so \(Q_4=0\), contrary to the values
\(Q_4(r_i)=(r_i-z)P(r_i)\) on the three distinct old roots of \(R\).
Therefore \(L=\lambda(Y-z)(Y-x)\) with \(\lambda\ne0\).
At all five ordinary sites \(D=ND=0\), so
\(IQ_4-\lambda(Y-x)Q_4\) vanishes there. It also vanishes at zero
and has degree at most five. Hence
\(IQ_4=\lambda(Y-x)Q_4\) exactly. A nonzero polynomial with zero
constant coefficient gains one origin valuation under primitive;
this forces \(x=0\). Comparing nonzero coefficients of the now
identity \(IQ_4=\lambda YQ_4\) forces \(Q_4\) to be a monomial.

## 2. Excluding the old monomial, including the ungauged contact

The direct noncontact condition gives live
\(rs(c_2s-c_0)(c_1+6s)\) and
\(r(c_1+6s)=6c_2s\) for
\(R=Y^3+c_2Y^2+c_1Y+c_0\). The old affinity and actual first-gap
root formula give
\[
 c_1=6s(c_2-r)/r,\qquad
 c_0(r^2-3s)=s^2(3c_2-4r),\qquad
 q=3s c_2-4rs-3c_0,\qquad z=r c_0/q .
\]
In particular \(s q=c_0(r^2-6s)\), so \(r^2-6s\) is live even
before splitting the \(r^2=3s\) exceptional chart.

* If \(r^2\ne3s\), the old scalar coefficient calculation in
  [small contacts, §4](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-small-contacts/README.md#4-the-remaining-two-small-contacts-have-symbolic-proofs)
  rules out a monomial \(Q_4/Y=(Y-z)m+K_*R\) from exactly
  these old identities and the live determinant of \(m\bmod R\).
  That scalar computation does not use the middle count or divide
  by a regular diagonal. For a constant monomial, \(K_*=-1\)
  and its quadratic and linear coefficients are both live. For a
  nonconstant monomial, \(K_*=zs/c_0\) and all three positive-degree
  coefficients are live. This transfers only the monomial calculation,
  not the \(\beta\ge1\) proof of any chronological fact.
* If \(r^2=3s\), the old identities now give
  \(c_2=4r/3, c_1=2r^2/3, z=-r/3\), with no division by
  \(r^2-3s\). In \(Q_4/Y\) the positive-degree coefficients in
  descending order are \((1,4r/3,2r^2/3)(1+K_*)\).
  Thus a monomial requires \(K_*=-1\), then
  \(Q_4=-C Y\) with \(C=c_0-r^3/9\ne0\).
  Nonzero \(C\) also follows from \(R=(Y+r/3)m+C\)
  and the old live \(m\) values.

In the exceptional case all five ordinary reads of \(D=0\) give
\((Y-z)G/b=-C Y\). The live reciprocal identity
\(G/b=YJ_4/U_r\) then gives
\((Y-z)J_4+C U_r=0\) at the same five clocks.
Since \(\deg U_r\le3\) and the leader is 42, we have the
polynomial identity
\((Y-z)J_4+C U_r=42T_5\), where
\(T_5=(J_5+\mu J_4)/132\) is their actual monic Jacobi pencil.
Its degree-four coefficient forces \(\mu=(11/7)(1-2z)\).
The sum and pair sum of the five pencil roots then give
\[
 V+B=2-3z,\qquad VB=14/11-6z+6z^2 .
\]
Here \(R=Y^3-4zY^2+6z^2Y+c_0\). Comparing
\(R[Y^2-(V+B)Y+VB]=T_5\) first recovers \(c_0\)
from the coefficient of \(Y^2\), and then gives
\[
 \begin{split}
 3564z^4-5544z^3+2832z^2-566z+33&=0,\\
 182952z^5-548856z^4+519288z^3-199584z^2+31817z-1590&=0 .
 \end{split}
\]
**contact.py** verifies all coefficients and their exact Bézout
identity with nonzero integer right side \(26396875886920749\).
Thus this contact is impossible over any characteristic-zero field,
not just from the sign of the old real variance.

The contradiction proves \(D_B\ne0\), so
\(-d_B^2D_B=0\) forces \(d_B=0\).
In fact \((ND)_B=0\) also holds, since its only possible nonzero
donor is \(D_B\) and the diagonal there is zero. This last
ordinary primitive read stays available for the remaining branch.

Run `python3 contact.py` with SymPy. The accompanying
`DIRKOrderElevenInvisibleSixAlphaOneBetaZeroFifthPivot` Lean
module checks the literal squared-diagonal implication and the
polynomial Bézout contradiction with Lean 4.36.0 and standard axioms.
The actual rooted and polynomial ingress above is an exact written
argument, not a global kernel-checked DIRK stage exclusion.
