# At s=p >= 7, the common-diagonal pole is full and the strict chain cannot break

Mathematical proof, not kernel-checked. Over a field of characteristic zero
let \(A=\gamma I+B\) on \(s\) physical stages, \(B\) strictly lower
triangular, with all rooted conditions through \(p=s\ge7\). Then
\[
         \lambda_{s-1}:=b^TB^{s-1}e
                 =b_s\prod_{i=2}^s B_{i,i-1}\ne0,\qquad e=1 .
\]
Thus every physical adjacent coefficient and the last output weight is
nonzero. When \(\gamma\ne0\), the reduced stability denominator has degree
exactly \(s\). This does not rule out order \(s\) on \(s\) stages; it rules
out the branch with missing longest support or one cancelled common pole,
and supplies actual necessary near-diagonal equations in its complement.
No Laguerre-root assumption is made in that complement.

## 1. Paid clock words and the one-hole identity

Throughout write \(c=Ae\), \(C=\operatorname{diag}(c)\), and, for paid
indices \(j+1\le p\), use the tall moments
\[
  \lambda_j=b^TB^je=\sum_{u=0}^j\binom ju\frac{(-\gamma)^{j-u}}{(u+1)!},
  \qquad
  (j+2)\lambda_{j+1}=(1-2(j+1)\gamma)\lambda_j
                               -j\gamma^2\lambda_{j-1}.
  \tag{1}
\]
The recurrence concerns the explicit scalar polynomials, so it can be
defined beyond the paid range without claiming equality to tableau
values there. It follows by differentiating the formal identity
\(z\sum_{j\ge0}\lambda_jz^j=\exp(z/(1+\gamma z))-1\).
In particular \(\lambda_0=1\).

In an exact clock model over the coefficient field, set
\(J f(y)=\int_0^y f(u)\,du\) (formal polynomial integration),
\(T=J-\gamma I\), and \(X f(y)=y f(y)\).
For any word of \(B,C\)'s applied to \(e\), its paid output equals formal
\(\int_0^1\) of the same word of \(T,X\)'s applied to 1. Indeed,
a rooted tree with factorial \(\rho(t)\) has exact stage model
\((|t|/\rho(t))y^{|t|-1}\): \(J\) puts a unary root above it, \(X\)
adds one leaf to its root, and the output integral gives \(1/\rho(t)\).
Expand each \(B=A-\gamma I\); a word with \(N\) copies of \(B\) and \(d\)
copies of \(C\) requires only tree orders through \(N+d+1\).

The commutator \([X,J]=J^2\), hence \([X,T]=J^2\), gives
\[
       T^{N-a} X T^a1=J T^N1+a J^2 T^{N-1}1
                     \qquad(0\le a\le N).
 \tag{2}
\]
Any term with a zero prefactor is omitted before interpreting powers.
We also use, in the same convention,
\[
 T^{N-a} X^2 T^a1=2J^2 T^N1+4a J^3 T^{N-1}1
                                   +a(a-1)J^4 T^{N-2}1.
 \tag{3}
\]
For example \(XT^a1=JT^a1+aJ^2T^{a-1}1\). Apply \(X\) again using
\([X,J^2]=2J^3\), and then \(T^{N-a}\), to get (3).

Let \(L=\lambda_{s-1}\), \(M=\lambda_{s-2}\), and
\[
              \kappa=L+2\gamma M+\gamma^2\lambda_{s-3},
       \qquad (s-2)\kappa=(1-2\gamma)M-2L
 \tag{4}
\]
(the second equality is (1)). Each strict path of length \(s-2\)
uses \(s-1\) physical stages in increasing order, hence is indexed
by the one omitted stage \(j\). Its weight \(\omega_j\) is the product
of the actually used strict entries, times the output weight at
the last retained stage; it is zero if any factor vanishes.
Then \(\sum_j\omega_j=M\), and with \(T_k'=\sum_{j\le k}\omega_j\)
the paid one-clock word at position \(k\) gives
\[
 \boxed{\quad M c_k+T_k'(c_{k+1}-c_k)
          = L+\gamma M+(k-1)\kappa,\qquad 1\le k\le s-1. \quad}
 \tag{5}
\]
Indeed position \(k\), counting from the earliest stage, is physical
\(k\) if \(j>k\), otherwise \(k+1\). Formula (2) with \(N=s-2,a=k-1\)
and output \(\int_0^1\) gives the right side of (5) after substituting
\(J=T+\gamma I\). The total cost is exactly \(s\) tree vertices.
No sign, support completeness, or clock distinctness was used.

## 2. A broken edge cannot be late when L=0

For \(\gamma=0\), (1) directly gives \(L=1/s!\ne0\). Suppose
\(\gamma\ne0\) and \(L=0\). The recurrence and \(\lambda_0=1\)
give \(M\ne0\) because consecutive zero tall coefficients would
propagate backwards. The last physical stage is active: otherwise
delete this unused suffix row and column, obtaining order \(s\)
with \(s-1\) stages, which the common-diagonal saturation theorem
(exclusion of \(p=s'+1\ge5\)) forbids. Thus \(L=0\) entails at least
one broken adjacent strict entry \(B_{i,i-1}=0\).

We use the support-only version of the previously proved saturation
calculation. Write \(w_h=b^TB^h\). If \(m\ge4\), order \(m+1\) is
paid, \(\lambda_m=0,\lambda_{m-1}\ne0\), and
\[
    \operatorname{supp} w_{m-2}\subseteq\{1,2\},\qquad
    \operatorname{supp} w_{m-3}\subseteq\{1,2,3\},
 \tag{6}
\]
then a contradiction, even when the actual tableau has more than
\(m\) stages. Here is exactly what the earlier first-row calculation
needs: put \(x=c-\gamma e=Be\), \(a=x_2\), \(d=x_3\).
The paid bush \(c^2\) at \(w_{m-2}\) gives
\(a=2\gamma+\gamma^2\lambda_{m-2}/\lambda_{m-1}
     =(1-2\gamma)/(m-1)\).
At \(w_{m-3}\), \(Bx\) is zero on rows 1 and 2; consequently
\(w_{m-3} Bx=\lambda_{m-1}\ne0\) and
\(w_{m-3}(x Bx)=d\lambda_{m-1}\). The paid mixed four-vertex fork
\(c(Ac)\) then forces \(d=2a\). The paid \(x^3\) moment on the
points \(0,a,2a\), using (1), forces
\[
       C_m(a/\gamma)=0,\qquad
       C_m(t)=(m+1)t^3-4m t^2+2(m-3)t+4.
 \tag{7}
\]
Since \(a/\gamma=(1/\gamma-2)/(m-1)\) and \(\lambda_m=0\),
the monic integer main factor
\((-1)^m m! L_m^{(1)}(1/\gamma)\) also vanishes.
Schur's alpha-one irreducibility over the rational prime subfield
excludes the cubic for \(m\ge4\). The prior saturation packet includes
a standalone rational-factor exclusion for this same pair of
polynomials if Schur is not invoked. Tree payment in (6) is exactly
\(m+1\), by unary lifts of the order-three bush and order-four
bush and mixed fork. No assertion of a physically smaller tableau
is made just from (6).

If a broken edge has receiver \(i\ge5\), then \(w_{s-3}\) has
support in the first two rows and \(w_{s-4}\) in the first three.
For the first claim the raw strict support permits at most row 3,
whose sole possible contributing path uses all indices \(3,\ldots,s\)
and hence the broken edge. For the second claim reason identically
with the highest possible row 4 and all indices \(4,\ldots,s\).
Thus (6) applies with the effective index \(m=s-1\), since
\(\lambda_{s-1}=0\) and \(\lambda_{s-2}=M\ne0\).
It follows that any remaining broken edge has receiver \(i\le4\).

## 3. An early break cannot survive either: penultimate-slot test

For any broken adjacent edge with receiver \(i\), a nonzero path of
length \(s-2\) must omit exactly one of \(i-1,i\), because including both
forces the broken edge. Hence for \(k\ge i\) the partial weight
\(T_k'=M\), and for \(k<i-1\) it is zero. In particular (5) yields
the actual late and early clock ladders
\[
 \begin{aligned}
     &c_{k+1}=\gamma+(k-1)\epsilon &&(i\le k\le s-1),\\
     &c_k=\gamma+(k-1)\epsilon &&(1\le k<i-1),\\
     &\epsilon=\kappa/M=(1-2\gamma)/(s-2).
 \end{aligned}
 \tag{8}
\]
No claim is made about the two exceptional rows at the broken edge.

Put \(n=s-2\), so \(M=\lambda_n\) and \(\lambda_{n+1}=0\).
Take strict length \(n-1=s-3\) paths, omitting exactly two indices.
At any position \(k=a+1\ge i\), a nonzero path has omitted at
least one of \(i-1,i\) before that position, and its physical stage
there is either \(k+1\) or \(k+2\); it cannot be \(k\).
By (8) the shifted clock \(c-\gamma\) at that position is either
\(a\epsilon\) or \((a+1)\epsilon\). Its actual weighted moments
\(m_0,m_1,m_2\) therefore satisfy
\[
           m_2-(2a+1)\epsilon m_1+a(a+1)\epsilon^2m_0=0.
 \tag{9}
\]
All are paid: they are the words
\(b^TB^{n-1-a}(C-\gamma I)^jB^ae\), \(0\le j\le2\),
of order at most \(s\).

Here is the exact normalized residual. Set
\[
 v=\gamma\lambda_{n-1}/M,\quad t=v+2=\epsilon/\gamma,\quad
 Q=\gamma^2\lambda_{n-2}/M,\quad R=\gamma^3\lambda_{n-3}/M.
\]
Equation (1) gives
\[
       (n-1)Q=nv^2+2v-n-1,\qquad
       (n-2)R=(nv+4)Q-nv .
 \tag{10}
\]
By (2), (3), and \(\lambda_{n+1}=0\),
\[
 \frac{\gamma m_0}{M}=v,\qquad
 \frac{m_1}{M}=1+aU,\qquad
 \frac{m_2}{\gamma M}=t+a(10+8v+2Q)+a(a-1)V,
\]
where \(U=1+2v+Q\) and \(V=4+6v+4Q+R\).
For example the ordinary \(C^2\) word is
\(2J^2T^{n-1}+4aJ^3T^{n-2}+a(a-1)J^4T^{n-3}\) applied to 1;
subtract twice \(\gamma\) times the \(C\) word and add \(\gamma^2\)
times the constant word to obtain the displayed \(m_2\).

Normalize the left side of (9) by \(\gamma M\). Substitution
reduces it to \(a(aK+D)\), where
\[
 K=V-2tU+t^2v=v^3-2vQ+R,\qquad
 D=v^3+2v^2-v-(v+4)Q-R .
\]
The two equations (10) give
\(D+(n-1)K=v[nv^2+2v-(n+1)-(n-1)Q]=0\).
Also, direct expansion of (10) gives
\[
 \begin{aligned}
  (n-1)(n-2)K
     &=(n+2)v^3+2(n+4)v^2+(4-2n)v-4(n+1)\\
     &=C_{n+1}(v+2).
 \end{aligned}
\]
Thus the normalized residual is exactly
\[
                 a(a-(n-1))\frac{C_{n+1}(t)}{(n-1)(n-2)}.
 \tag{11}
\]
In particular the terminal position \(a=n-1\) cannot give a
contradiction: its two-node equation is automatically satisfied.
Take instead the penultimate position \(a=n-2\),
\(k=n-1=s-3\ge4\ge i\). Its coefficient in (11) is nonzero
in characteristic zero. Equation (9) forces \(C_{n+1}(t)=0\).
But \(t=(1/\gamma-2)/n\) and \(\lambda_{n+1}=0\); the same scalar
Laguerre/cubic exclusion as above with \(m=n+1=s-1\) is impossible.

Thus \(L\ne0\). The cutoff \(s\ge7\) gives the asserted position
coverage without a special-order search. The prefix and ladder
identities themselves are valid whenever their scalar payments and
nonvanishing hypotheses hold; no conclusion at \(s=5,6\) is made here.

## 4. Consequences in the surviving branch L != 0

Write \(a_i=B_{i,i-1}\) for \(i\ge2\). Since \(L=b_s\prod a_i\ne0\)
all are nonzero, and all stages reach the last active stage along
the actual strict chain. Chronological relabeling must respect that
entire chain. For nonzero \(\gamma\),
\[
  1+z b^T(I-zA)^{-1}e
      =1+\sum_{j=0}^{s-1}\frac{\lambda_j z^{j+1}}
                                       {(1-\gamma z)^{j+1}} .
\]
Clearing the displayed common denominator leaves, at \(z=1/\gamma\),
only \(L/\gamma^s\ne0\), proving no cancellation and degree exactly
\(s\) in the reduced denominator. This is an algebraic statement,
not a stability requirement.

The one-hole weights in (5) are explicitly
\[
 \omega_1=L/a_2,\qquad
 \omega_s=L b_{s-1}/(b_s a_s),\qquad
 \omega_j=L B_{j+1,j-1}/(a_j a_{j+1})\quad(2\le j\le s-1).
 \tag{12}
\]
Therefore if \(c_k\ne c_{k+1}\), (5) determines \(T_k'\)
from \(\gamma\), \(s\), and actual clocks. When both consecutive gaps
for \(k=j-1,j\) are nonzero it determines the normalized genuine
second-subdiagonal entry via \((T_j'-T_{j-1}')/L\); the endpoint
ratios follow likewise when available. If a gap vanishes, its exact
replacement condition is \(M c_k=L+\gamma M+(k-1)\kappa\).
For instance when \(M=0,L\ne0\), a zero gap is possible only at
\(k=s/2\), if that is an integer, by (4). If \(M\ne0,\kappa\ne0\),
one clock value cannot occur on two zero adjacent gaps at different
positions. All this is necessary only, not an assumption of
distinct clocks or a claimed nonlinear existence theorem.
