# No cyclic common-diagonal p=s tableau has distinct arithmetic clocks (s>=7)

Work over an arbitrary
characteristic-zero field. Let \(A=\gamma I+B\) with \(\gamma\ne0\)
and \(B\) strictly lower triangular on \(s\) physical stages, and suppose
all rooted order conditions through \(p=s\ge7\) hold. Put \(e=1\),
\(c=Ae\), \(C=\operatorname{diag}(c)\). Assume both
\[
            L=b^TB^{s-1}e\ne0,\qquad c_i=\gamma+(i-1)\alpha
                          \quad\text{for }\alpha\ne0.
\]
These assumptions give a contradiction. In particular, combining with
the separately proved nondegenerate rectangle rigidity (which forces
cyclic arithmetic clocks for its \(p=s\ge8\) branch), the entire
nondegenerate branch is impossible. The present theorem also permits
a degenerate tall Hankel determinant if arithmetic clocks are known
independently. It does not exclude nonarithmetic degenerate tableaux
or imply a new all-common-diagonal stage floor.

Although a true order-five fork provides a separate explicit check,
the actual exclusion below is stronger: it only needs paid single-spine
clock words with selected internal gap products of total reverse grade
at most six, and the paid tall values. No signs, real embedding, or
Laguerre-root assumption is used.

## 1. Paid internal gap tests force multiplicativity

Let \(J\) be formal integration from 0 to the variable, \(T=J-\gamma I\),
\(X\) multiplication by the variable, and \(\ell\) the formal integral
from 0 to 1. A stage tree \(t\) has exact clock polynomial
\((|t|/\rho(t)) x^{|t|-1}\), where \(\rho\) is the rooted tree factorial.
Thus \(T,X\) model \(B,C\): expand \(B=A-\gamma I\), so that each
remaining \(A\) adds a unary ancestor and each \(C\) attaches a leaf
to the current root. A word with \(d\) strict factors and \(r\) clock
factors costs at most \(d+r+1\) rooted vertices. In particular
\[
 \lambda_j=\ell(T^j1)
       =\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!}
          =b^TB^je\quad(j+1\le p).
\]
Differentiating \(z\sum_{j\ge0}\lambda_j z^j
=\exp(z/(1+\gamma z))-1\) gives
\[
 (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j
                                       -j\gamma^2\lambda_{j-1}.
 \tag{1}
\]
Let \(\xi=1/\gamma\), and define a functional \(\mu\) on polynomials
of degree at most \(s-1\) in a new variable \(y\) by
\[
 m_k:=\mu(y^k)=\gamma^k\lambda_{s-1-k}/L,\qquad m_0=1.
\]
Equivalently \(\mu(P)=L^{-1}\ell(T^{s-1}P(\gamma/T)1)\), where the
formal expression has no negative powers for the stated degrees.
The reverse version of (1) is
\[
 (s-k)m_k=(\xi-2(s-1-k))m_{k+1}-(s-2-k)m_{k+2},
                                      \quad 0\le k\le s-3.
 \tag{2}
\]

A strict path of \(s-h-1\) edges omits exactly \(h\) physical indices.
At an internal occupied gap of this path, if \(g\) consecutive indices
are omitted between its two endpoints, their clock difference is
\(d=\alpha(g+1)\). Define
\[
     P_j(d)=\prod_{r=1}^j(d-r\alpha)\quad(j\ge1).
\]
At this gap \(P_j(d)=0\) for \(g<j\), and \(P_j(d)=\alpha^j j!\) for
\(g=j\). This polynomial times the actual strict entry on the gap
is modeled by \(Q_j(T)\): replace \(d^0 B\) on that link by \(T\),
and for each \(r\ge1\) replace \(d^rB\) by \(r!J^{r+1}\).
Indeed a matrix commutator \(\mathrm{ad}_C^r(B)\) multiplies that
entry by \(d^r\), and \([X,J]=J^2\),
\([X,J^k]=kJ^{k+1}\) give
\(\mathrm{ad}_X^r(T)=r!J^{r+1}\).
Set \(t=\alpha/\gamma\) and write
\[
            F_j(y)=\frac{Q_j(T)}{j! T^{j+1}}\bigg|_{\gamma/T=y}.
\]
This is a polynomial in \(y\) of degree at most \(j+1\). The first
three are, with \(w=1+y\),
\[
 \begin{aligned}
 F_1&=w^2-t y,\\
 F_2&=w^3-\tfrac32 t y w^2+t^2 y^2,\\
 F_3&=w^4-2t y w^3+\tfrac{11}{6}t^2 y^2 w^2-t^3 y^3 .
 \end{aligned}                                               \tag{3}
\]

For a single marked gap \(j=h\), all \(h\) holes have to be in that
gap for the test to survive. The actual weight is that of one
interior interval omission, normalized by \(L\). Because the
formal answer is \(\ell(T^{s-1}F_j(\gamma/T)1) j!\), independent
of the gap position, every interior interval of \(j\) omitted
indices has the same normalized weight \(f_j=\mu(F_j)/\alpha^j\).
This is valid for \(j\le s-2\), when an internal gap exists.
Thus the scaled strict matrix is lower Toeplitz, with link
parameter depending only on its length; no assertion is made
about the boundary gaps.

More generally mark \(q\) distinct internal gaps with positive counts
\(j_1,\ldots,j_q\), and set \(h=\sum j_i\). The only requirement on
the number of slots is \(h+q\le s-1\).
Each mark is \(P_{j_i}\); the total strict hops \(s-h-1\), mark
degree \(h\), and initial leaf pay exactly \(s\) vertices. Every
surviving path must have \(g_i=j_i\) at the chosen gaps and no
other holes. It is a single physical path. Its normalized weight
is \(\prod_i f_{j_i}\) because its contiguous omitted runs are
separated by retained stages; the bypasses of the full adjacent
product affect disjoint strict edges, even when a retained endpoint
is shared. This uses \(L\ne0\) and never divides by an individual
skip-edge weight. The formal polynomial product is
\(T^{s-1}\prod_i F_{j_i}(\gamma/T)\) after cancelling the \(j_i!\).
Therefore
\[
                   \mu\!\left(\prod_i F_{j_i}\right)
                       =\prod_i\mu(F_{j_i})
                   \quad\text{if }\sum_i(j_i+1)\le s-1 .
 \tag{4}
\]
The grade of \(F_j\) here is \(j+1\). It budgets distinct internal
gaps as well as marks; it is not only the polynomial degree.
By linearity, (4) applies to products of polynomials represented
by linear combinations of these monomials, when the sum of their
grade budgets is allowed. We will use only total grade at most six.

## 2. Generic slope: a contradiction to the reverse recurrence

Put \(k=t/2\), \(u=y+1-k\). Then \(w=u+k\) and
\(F_1=u^2+2k-k^2\) is even in \(u\). Subtract from \(F_2,F_3\)
their even parts, which lie in the span of \(1,F_1,F_1^2\)
with grade at most four. Their odd parts have the following
coefficients of \(u^3,u\), by expanding (3):
\[
 \begin{array}{c|cc}
    & u^3 & u\\ \hline
 F_2 & 1-3k & k^2(1-k)\\
 F_3 & \tfrac43 k(6-23k+16k^2) &
                    \tfrac43 k^3(k-1)(4k-5).
 \end{array}
\]
The determinant is
\(\tfrac43 k^3(k-1)(2k-1)^2\).
When \(t\ne1,2\), it is nonzero since \(\alpha\ne0\).
Thus \(u,u^3\) have representations of grade at most four.
Together with the even polynomials, every polynomial of degree at
most four has such a representation. In particular, (4) with
\(F_1\) implies
\[
              \mu((F_1-\mu(F_1))P)=0\qquad(\deg P\le4).
 \tag{5}
\]
If the reverse \(3\)-by-\(3\) Hankel is already assumed
nondegenerate, (5) with degree at most two immediately contradicts
the nonconstant monic quadratic \(F_1-\mu(F_1)\).

The arithmetic-clock theorem does not need that assumption.
Equation (5) forces \(m_0,\ldots,m_6\) to satisfy a monic,
constant-coefficient quadratic recurrence: use \(P=y^k\) for
\(k=0,\ldots,4\). The following elementary incompatibility with (2)
handles any rank.

**Fixed recurrence lemma.** For \(\xi\ne0\), \(m_0=1\), a sequence
through \(m_6\) obeying (2) for \(0\le k\le4\) cannot also satisfy
one monic constant quadratic recurrence there.

Proof. Extend by the constant recurrence and, only for the proof,
factor its characteristic polynomial in an algebraic closure.
For a geometric sequence \(r^k\), the residual of (2)
(left side minus right) is \(r^k A_k(r)\), where
\[
        A_k(r)=s-\big(\xi-2(s-1)\big)r+(s-2)r^2
                                              -k(1+r)^2.
\]
It has \(A_k(-1)=\xi\); hence there is no \(r\) for which
\(A_k(r)\) is the zero affine polynomial in \(k\).
If the roots are distinct and nonzero, the residual for a
combination of the two exponential modes is a combination of
each mode times an affine polynomial. It satisfies the homogeneous
fourth-order recurrence with characteristic polynomial
\((Z-r_1)^2(Z-r_2)^2\). Its first four values vanish by hypothesis,
so it vanishes identically. The two exponential-affine components
are independent: applying the squared shift-minus-other-root
kills one and is invertible on the other's affine component,
since the roots differ. Each nonzero sequence coefficient would
therefore require its \(A_k(r)\) to vanish identically, impossible.

If the root \(r\ne0\) is repeated, the sequence is
\((A+Dk)r^k\). Its residual divided by \(r^k\) is
\((A+Dk)A_k(r)+Dr A'_k(r)\), a polynomial in \(k\) of
degree at most two, hence identically zero from the paid rows.
For \(r\ne-1\) the quadratic term forces \(D=0\), then the
linear term forces \(A=0\). For \(r=-1\) we have
\(A_k(-1)=\xi,\ A'_k(-1)=2-\xi\), so the linear term forces
\(D=0\) and then the constant forces \(A=0\).
If one root is zero and the other nonzero, the sequence from
\(k=1\) on is a single geometric mode. The residual rows at
\(k=1,2\) force its coefficient to be zero, since otherwise
\(A_k(r)\) would vanish at both; then \(m_1=m_2=0\) contradict
(2) at \(k=0\). If both roots are zero, \(m_2=m_3=0\)
and (2) at \(k=1\) gives \(m_1=0\), the same contradiction.
This proves the lemma and excludes the generic slope.

## 3. The two exceptional slopes

The fixed-grade proof of (4) is also sufficient at the two
slopes where the odd-part determinant vanishes.

*If \(t=2\).* Equations (3) give
\(F_1=1+y^2,\ F_2=1+y^2-2y^3\).
Write \(a=m_2,\ b=m_3\). By (4),
\[
        m_4=a^2,\qquad m_5=ab,\qquad m_6=a^3=b^2 .
\]
If \(a=0\), then \(b=0\), so the two rows \(k=1,0\)
of (2) contradict \(m_0=1\).
If \(a\ne0\), set \(r=b/a\), so \(a=r^2,\ b=r^3\), and
\(m_2,m_3,m_4,m_5\) are the nonzero consecutive powers
\(r^2,r^3,r^4,r^5\). At \(k=2,3\), equation (2)
says \(A_2(r)=A_3(r)=0\), again impossible.

*If \(t=1\).* Put \(z=y+y^2,\ v=yz\).
Then \(F_1=1+z,\ F_2=1+\tfrac32 z-\tfrac12 v\), so these
new elements have grades at most two and three respectively.
Their identity \(v^2+zv=z^3\), and (4), give
\[
        b^2+ab=a^3,\qquad a=\mu(z),\quad b=\mu(v).
\]
If \(a=0\), \(b=0\) and \(m_2=-m_1,\ m_3=m_1\);
(2) at \(k=1\) then gives \(\xi m_1=0\).
Using \(k=0\) gives a contradiction. If \(a\ne0\), let
\(r=b/a\), so \(r(r+1)=a\) and \(r\ne0,-1\).
Using \(y^2=z-y\) and (4) on the needed products gives
\[
 \begin{aligned}
 \mu(z)&=a, &\mu(zy)&=b,\\
 \mu(zy^2)&=a^2-b=a r^2,\quad&
 \mu(zy^3)&=ab-a r^2=a r^3 .
 \end{aligned}
\]
For instance \(zy^3=zv-zy^2\).
It follows that \(m_{j+2}+m_{j+1}=a r^j\) for \(0\le j\le3\),
whence \(m_j=r^j+\eta(-1)^j\) for \(1\le j\le5\) with a
constant \(\eta\). Using (2) at \(k=1,2,3\) gives
\(r^k A_k(r)+\eta\xi(-1)^k=0\).
Divide by \(r^k\) and take a second difference across these
three positions. The affine term vanishes, and
\((-1/r)-1\ne0\), so \(\eta=0\).
Now \(A_1(r)=A_2(r)=0\) is impossible. This excludes \(t=1\).

Thus no cyclic arithmetic-clock method in the hypotheses exists.
Only the separately established arithmetic-overlap cutoff requires
\(s\ge8\) for application to an arbitrary nondegenerate clock branch.

The [seven-clock localization](../../lower-bounds/characteristic-zero/sdirk-local-seven-clock-floor.md) uses these same paid moment identities without a global arithmetic progression.
