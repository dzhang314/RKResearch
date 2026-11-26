# Seven local arithmetic clocks exclude cyclic equality and give a p>=15 stage floor

This proof uses the [arithmetic-gap contradiction](../../research/strict-sdirk-dependency-depth/PAID-ARITHMETIC-GAP-EXCLUSION.md) with a local run of consecutive physical clocks. It does not assume that the whole tableau has arithmetic clocks.
A rooted order statement here means all orders through \(p\), not
order exactly \(p\) and no higher. The stages and clocks are literal
physical stage indices and \(c=Ae\).

**Local theorem.** Let \(A=\gamma I+B\) be lower triangular over a field
of characteristic zero, with \(\gamma\ne0\), \(B\) strictly lower
triangular, and \(p=s\ge7\). If order through \(p\) holds and
\(L=b^TB^{s-1}e\ne0\), then there cannot be seven consecutive physical
clocks of the form
\[
             c_{r+j}=c_r+j\delta\quad(0\le j\le6),\qquad
                                    \delta\ne0.                \tag{1}
\]
The offset \(c_r\) is unrestricted. No arithmetic, support, or constant
normalized skip weights outside this run are assumed.

**Stage-floor synthesis.** For every \(p\ge15\), a common-diagonal
triangular tableau over any characteristic-zero field satisfying order
through \(p\) has at least \(p+1\) physical stages. The diagonal may be
zero, real or non-real, rational or irrational, and no signs or
stability are assumed. This is not a claim for differing-diagonal
DIRK, a claim below \(p=15\), or an attainment result.

## 1. Exact local placement and strict product

Write \(a_i=B_{i,i-1}\) for \(2\le i\le s\). By strict triangularity
\(L=b_s\prod_{i=2}^s a_i\), so \(L\ne0\) makes every \(a_i\) and \(b_s\)
nonzero. For any physically indexed strict path on \(m=s-h\) retained
stages \(v_1<\cdots<v_m\), its weight is
\(b_{v_m}\prod_i B_{v_{i+1},v_i}\). The number of omitted indices is
\(h\), and at every occupied slot \(j\) one has
\[
                           j\le v_j\le j+h.                    \tag{2}
\]

Fix positive desired internal gap counts \(d_1,\ldots,d_q\) and let
\(h=\sum_j d_j\), with \(h+q\le6\). Mark the \(q\) consecutive occupied
links from slot \(r+j-1\) to slot \(r+j\), for \(1\le j\le q\).
These slots exist: \(r+q+h\le r+6\le s\) gives \(r+q\le m\).
On every \(h\)-hole candidate path, not just on the path selected
below, (2) puts all actual endpoints of these links in
\([r,r+q+h]\subseteq[r,r+6]\). Therefore each marked clock difference
is exactly \(\delta(1+g_j)\), where \(g_j\) is the nonnegative number
of omitted physical stages in that link.

On link \(j\) use the polynomial mark
\[
                 P_{d_j}(w)=\prod_{t=1}^{d_j}(w-t\delta),
                 \qquad w=c_{v_{r+j}}-c_{v_{r+j-1}} .
\]
This vanishes if \(g_j<d_j\), and is \(\delta^{d_j}d_j!\) if
\(g_j=d_j\). If every factor can survive, the sum of all \(g_j\)
is at least \(h\). There are only \(h\) omissions, so equality
holds at each link and no omissions occur before, after, or
between the marked runs. Exactly one retained list is possible.
Its physically indexed donor and receiver for link \(j\) are
\[
    u_j=r+j-1+\sum_{t<j}d_t,\qquad v'_j=u_j+d_j+1.              \tag{3}
\]
These endpoints lie in the run. The list may have zero weight,
which the following argument permits.

For \(u<v\) define the normalized skip
\[
               \theta_{u,v}=
                  B_{v,u}/(a_{u+1}\cdots a_v).
\]
Only the physical adjacent products in the denominator are assumed
nonzero. On the surviving retained list the path weight is
\(L\prod_j\theta_{u_j,v'_j}\). Indeed the full chain begins at
physical stage 1 and ends at physical stage \(s\) with output \(b_s\);
each isolated omitted run replaces its own consecutive block of
adjacent \(a_i\)'s by the actual skip \(B_{v'_j,u_j}\).
Their edge blocks are disjoint even when two replacements share a
retained endpoint \(v'_j=u_{j+1}\). This is a statement about
position-dependent actual skips, not a Toeplitz assumption.

## 2. Each selected position-dependent skip is calibrated locally

For the particular pair \(u_j,v'_j\) in (3), use a separate
\(d_j\)-hole word with one mark at occupied link \(u_j\) to \(u_j+1\).
It exists because \(u_j+1+d_j=v'_j\le s\). By (2) for this smaller
hole number, both endpoints on every such path lie in
\([u_j,u_j+d_j+1]=[u_j,v'_j]\), wholly inside (1). The polynomial
\(P_{d_j}\) now survives only when all \(d_j\) omissions are in this
one gap, which is exactly the physical interval
\(\{u_j+1,\ldots,v'_j-1\}\). Hence its actual output is
\[
                    \delta^{d_j}d_j! L\theta_{u_j,v'_j}.       \tag{4}
\]
This separate calibration is essential: it does not divide by
a zero skip or infer equal weights for intervals outside (1).

To evaluate both types of word, let \(J\) be formal integration from
zero, \(T=J-\gamma I\), \(X\) multiplication by the clock variable, and
\(\ell\) formal integration from 0 to 1. A stage tree \(t\) has exact
clock polynomial \((|t|/\rho(t))x^{|t|-1}\), with \(\rho(t)\) its
rooted factorial. Thus \(B\) is modeled by \(T\) after expanding the
scalar diagonal shift, and a clock multiplier by \(X\). In a word
with \(s-h-1\) strict hops and total mark degree \(h\), the leaf,
hops and marks cost at most \(1+(s-h-1)+h=s\) vertices.
Specifically \(\mathrm{ad}_C^j(B)\) with
\(C=\operatorname{diag}(c)\) multiplies a skip by the \(j\)-th power
of its clock difference. Its model for \(j\ge1\) is
\(j!J^{j+1}\), by \([X,J]=J^2\) and induction
\([X,J^j]=jJ^{j+1}\); its zeroth model is \(T\).
A mark of degree \(d\) therefore corresponds to a polynomial
\(Q_d(T)\) obtained by these replacements in \(P_d\).

Let \(\lambda_j=b^TB^je=\ell(T^j1)\) for \(j+1\le s\) be the paid
tall values. Put \(t=\delta/\gamma\) and let \(\mu\) be the
reverse tall functional
\[
               \mu(y^i)=m_i=\gamma^i\lambda_{s-1-i}/L,
                          \quad 0\le i\le s-1 .
\]
Equivalently \(\mu(G)=L^{-1}\ell(T^{s-1}G(\gamma/T)1)\);
the indicated range has no actual negative power of \(T\).
Normalize \(Q_d(T)=d!\,T^{d+1}F_d(\gamma/T)\). The first three
polynomials are, for \(w=1+y\),
\[
 \begin{aligned}
 F_1&=w^2-ty,\\
 F_2&=w^3-\tfrac32ty w^2+t^2y^2,\\
 F_3&=w^4-2ty w^3+\tfrac{11}{6}t^2y^2w^2-t^3y^3 .
 \end{aligned}
\]
The single word in (4) has \(s-d_j-2\) unmarked strict hops.
Because all \(Q_d\) and \(T\) commute as polynomials of \(J\),
its formal output is \(d_j!L\mu(F_{d_j})\). Hence
\[
               \delta^{d_j}\theta_{u_j,v'_j}=\mu(F_{d_j})
\]
for that calibrated physical skip.

For the multi-mark word, the unmarked hop count is \(s-h-1-q\)
and \(\sum_j(d_j+1)=h+q\). Its formal product factors as
\(T^{s-1}\prod_j(d_j!\,F_{d_j}(\gamma/T))\). The actual expression
from (3)--(4) is \(L\prod_j d_j!\mu(F_{d_j})\). Thus
\[
                  \mu\!\left(\prod_j F_{d_j}\right)
                       =\prod_j\mu(F_{d_j})
               \qquad\text{for }\sum_j(d_j+1)\le6.             \tag{5}
\]
The cancellation uses only characteristic zero, \(L\ne0\), and
the nonzero arithmetic step. This proves exactly the same grade-six
moment identity as the globally arithmetic calculation, now with
no global clock hypothesis.

## 3. The arithmetic contradiction uses only (5)

The companion arithmetic proof, Sections 2 and 3, is reused without
change. For precision, its complete input is (5), \(t\ne0\),
\(m_0=1\), \(\xi=1/\gamma\ne0\), and the reverse tall recurrence
\[
 (s-k)m_k=(\xi-2(s-1-k))m_{k+1}-(s-2-k)m_{k+2}
                                  \quad(0\le k\le s-3).
 \tag{6}
\]
It follows from the paid binomial tall values and their polynomial
recurrence. Since \(s\ge7\), all \(m_0,\ldots,m_6\) and rows
\(k=0,\ldots,4\) used there are paid. Here are the exact uses,
so that no global arithmetic or Hankel assumption can enter:

* For \(t\ne1,2\), shift \(u=y+1-t/2\) and put \(k_0=t/2\).
  The odd parts of \(F_2,F_3\) in \(u\) have coefficient determinant
  \(\tfrac43 k_0^3(k_0-1)(2k_0-1)^2\ne0\).
  The even parts lie in the span of \(1,F_1,F_1^2\).
  Hence these graded elements represent every polynomial through
  degree four at cost at most grade four. Equation (5) makes the
  monic quadratic \(F_1-\mu(F_1)\) orthogonal to those polynomials,
  giving a fixed quadratic recurrence for \(m_0,\ldots,m_6\).
  The fixed-recurrence lemma in the core excludes this using
  (6): for a geometric mode \(r^k\), the scaled residual is affine
  with slope \(-(1+r)^2\) and value \(\xi\) when \(r=-1\).
  Two distinct nonzero modes give an exponential-affine residual
  satisfying a fixed fourth-order recurrence, and four consecutive
  zero residuals force both modes to vanish. Repeated and zero
  roots reduce as in the core; each still contradicts \(m_0=1\).
* At \(t=2\), \(F_1-1=y^2\), \(F_1-F_2=2y^3\).
  Equation (5) gives \(m_4=m_2^2\), \(m_5=m_2m_3\),
  \(m_6=m_2^3=m_3^2\). The zero case contradicts rows \(k=1,0\)
  of (6); otherwise \(m_2,\ldots,m_5\) are nonzero consecutive
  geometric moments and rows \(k=2,3\) are impossible.
* At \(t=1\), \(z=y+y^2\) and \(v=yz\) have grades two and
  three from \(F_1,F_2\). The identity \(v^2+zv=z^3\) and
  (5) give \(\mu(v)^2+\mu(z)\mu(v)=\mu(z)^3\).
  The zero case gives the alternating sequence through \(m_3\)
  and is excluded by (6). Otherwise write \(r=\mu(v)/\mu(z)\);
  \(r(r+1)=\mu(z)\ne0\), and (5) gives
  \(m_j=r^j+\eta(-1)^j\) for \(1\le j\le5\).
  Rows \(k=1,2,3\) of (6), after division by \(r^k\)
  and second differencing, eliminate the alternating coefficient
  \(\eta\); the remaining geometric mode is impossible.

This excludes (1) in every case. The genuine order-five fork
diagnostic is neither invoked nor needed for this join.

## 4. Literal degenerate prefix/tail, including the zero-slope test

We now check the exact stage-count coverage; these are consequences
of the established paid rectangle identity. For \(p=s\ge8\) and
\(L\ne0\), let \(N=s-3\), \(x_i=c_i-\gamma\),
\(u_a=x_{a+1}/a\). The rectangle gives
\[
 (D u_a+E)x_{b+3}+(E u_a+F)b+H u_a+G=0
                      \quad(1\le a\le b\le N).
 \tag{7}
\]
Put \(\Delta=DF-E^2\). The nondegenerate case gives all clocks
arithmetic with step \(x_2=B_{21}\ne0\): the affine slope of the
tail in (7) is injective as a function of \(u_a\), and the literal
prefix through \(s-3\) overlaps the literal tail from 4 at two
indices. This is the separately established nondegenerate rectangle
rigidity and directly provides a seven-clock run.

For the degenerate case \(\Delta=0\), the preceding rectangle proof
first gives \(D\ne0\) at \(\gamma\ne0,L\ne0\); otherwise \(D=E=0\)
would make four consecutive tall values geometric, incompatible
with their scalar recurrence. We get \(F=E^2/D\).
If \(DG-HE\ne0\), then \(Du_a+E\ne0\) for every \(a\);
otherwise (7) has only its nonzero constant left. All the tails
then have slope \(-E/D\), and at the common last slot \(b=N\)
the injective fractional map \((Hu+G)/(Du+E)\) makes every
\(u_a\) equal. The prefix through \(s-2\) overlaps the tail at
two physical indices, forcing \(u_a=-E/D\), a contradiction.
Thus \(DG-HE=0\) and the actual factorization is
\[
          (Du_a+E)\big(x_{b+3}+(E/D)b+H/D\big)=0 .            \tag{8}
\]

The possible run step \(\delta=-E/D\) is nonzero. To check the
only zero-step alternative, if \(E=0\) then \(F=G=0\).
Cyclicity gives \(u_1=x_2\ne0\), so (7) forces
\(x_4=\cdots=x_s=-H/D\). In the one-hole identity
\[
 Mx_j+T'_j(x_{j+1}-x_j)=L+(j-1)\kappa,\qquad H=M\kappa,
\]
the equal adjacent pairs at \(j=4,5\) both exist. Their difference
forces \(\kappa=0\), hence \(H=0\), and either identity then
gives \(L=0\). This is impossible. No positivity or nonzero
assumption on \(M\) was used for this step.

If every \(u_a=\delta\), physical stages \(1,\ldots,s-2\)
form an arithmetic run of step \(\delta\). Otherwise let \(a_0\)
be the first \(a\) with \(u_a\ne\delta\). Then the literal
prefix \(1,\ldots,a_0\) is arithmetic, and its slope is \(\delta\);
(8) makes the literal tail \(a_0+3,\ldots,s\) arithmetic with
the same step, possibly a different offset. There is no inference
about the two boundary clocks \(a_0+1,a_0+2\).
The two lengths are \(a_0\) and \(s-a_0-2\), both positive
and summing to \(s-2\). At \(s\ge15\) their sum is at least
13, so at least one has length at least seven. This is a
consecutive physical run, not a rearranged or coalesced clock list.
The offset freedom of the local theorem handles either run.

## 5. All-branch stage count and exact dependency scopes

Let \(p\ge15\), and suppose for contradiction \(s\le p\).

1. The previously established nonlinear scalar-cap theorem for
   common diagonal gives \(s\ge p\) at \(p\ge5\), hence \(s=p\).
   This result excludes saturation of the scalar cap in the
   nonzero common-diagonal case; for zero diagonal the usual tall
   nonvanishing already gives it.
2. If \(\gamma=0\), the established ERK rectangle exclusion at
   \(s=p\ge5\) applies: the two-hole identity forces
   \(c_4=\cdots=c_s=1\), and the one-hole identity at \(j=4\)
   would require \(M=4L\) although \(M=sL\).
3. If \(\gamma\ne0\), the previously established \(s=p\ge7\)
   common-diagonal no-cancellation theorem gives the actual
   \(L\ne0\). Thus the literal rectangle charts above apply.
   Nondegenerate and degenerate cases both exhibit the local
   arithmetic run of seven clocks, which contradicts Sections 1--3.

There are no other branches under these hypotheses, proving
\(s\ge p+1\) for this range. This uses no fixed-positive diagonal
hypothesis, stability condition, topological layer assumption, or
held finite-order case result. No boundary below \(p=15\) or method
existence at the new lower bound is claimed here.

Exact frozen mathematical dependencies, all unchanged:
- Common diagonal nonlinear cap: COMMON-DIAGONAL-PAID-NONLINEAR.md,
  SHA-256 0d7890b60dcf139637a7f9dc148d12b75a854f47f0005c74b6fd1ed1ebaea86b.
- Equality no-cancellation: COMMON-DIAGONAL-ONE-SLACK.md,
  SHA-256 2e0cc583dfcd15df4c491539198a06457054c5825c6ba9d81976d7171ca59936.
- Literal rectangle, ERK equality and degenerate charts:
  CYCLIC-PAID-RECTANGLE.md,
  SHA-256 b9ee35a0ac94c1ad346a2b3b0b451ebd525aa2e353bfc2d2193e30aac044711d.
- Grade-six arithmetic algebra, used only via (5)--(6):
  PAID-ARITHMETIC-GAP-EXCLUSION.md,
  SHA-256 0ec9a1ff481ec6b8c7946e86d7afe79c3ea9991e88c4aba1315a8ef6285b12ed.

This independent proof route does not replace the sharper numerical lower entries already known through order 20.
