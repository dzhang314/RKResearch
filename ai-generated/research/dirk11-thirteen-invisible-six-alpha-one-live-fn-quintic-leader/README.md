# The true weighted quintic error retains its cubic leader

**Result.** In the normalized no-late invisible-six DIRK11/13
chart with live reciprocal multiplier, \(\alpha=1,\beta=1\)
or \(2\), and direct noncontact \(F_n\), the actual reverse
quintic-error polynomial \(Q_5\) is cubic. No extra nonzero
regular-diagonal assumption enters this proof. In the beta-one
nonzero-fourth/nonzero-fifth profile, the
[live late-affine certificate](../dirk11-thirteen-invisible-six-alpha-one-live-fn-late-affine/README.md)
also makes the first middle root simple. These are scoped
restrictions; the unrestricted real stage interval remains
**13–14**.

Let \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(W(f)=b_{\rm wt}f(Y)\), \(R=(Y-v)(Y-u)(Y-w)\) for the
old three ordinary clocks, \(P_0=YR,\ P_5=(Y-V)P_0\).
Use the actual zero-diagonal first-middle ghost \(x\) and
its live affine fit from the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md).
Write
\[
 P=Ym,\qquad Q_4=(Y-z)P+K_*P_0,\qquad
 D=(Y-z)G-W(Q_4),\qquad
 ND=G L-W(IQ_4),
\]
with \(L=\lambda(Y-z)(Y-x)\), \(\lambda\ne0\).
The ordinary reciprocal scale on those live slots is
\(H_{\rm bary}/b_{\rm wt}=YJ_4\). Here \(I\) is the
zero-constant primitive.

## 1. Pure ordinary projection from a hypothetical degree loss

The actual weighted quintic error
\(W(IP_5)-NW(P_5)=GQ_5+\theta H_{\rm bary}\)
has distinct roots \(z,x\), by chronology of its
literal weighted-zero prefix. It is not the zero
polynomial by the exact
[old ordinary independence](../dirk11-thirteen-invisible-six-alpha-two-debit/README.md#1-a-nonzero-old-determinant).
Thus if \(\deg Q_5\le2\), it must be proportional to
\(L\), say \(Q_5=\sigma L\).

Both \(D\) and \(W(P_5)\) vanish through \(V\);
by triangularity their \(N\)-images do also.
Therefore the ordinary rows \(v,u,w,V\) give
\[
 IP_5=\sigma IQ_4+\theta Y J_4
\]
at those samples, by dividing only their live weights.
At the polynomial origin all three polynomials vanish.
The polynomial difference therefore equals
\((a+bY)P_5\) for some \(a,b\), since the five roots
are distinct and the degree is at most six. Its leading
coefficient gives \(b=1/6\). Its coefficient of \(Y\)
gives \(\theta=-a P_5'(0)\), since \(J_4(0)=1\)
and both primitive polynomials have double zeros at 0.
This yields the actual polynomial span
\[
 IP_5-\tfrac16 YP_5
  =a\big(P_5-P_5'(0)YJ_4\big)+\sigma IQ_4.
\]
The three columns are all divisible by \(Y^2\)
and have degree at most five. Also
\(IQ_4=I[(Y-z)P]+K_* IP_0\), so the four-column
determinant on
\[
 IP_5-\tfrac16 YP_5,\quad P_5-P_5'(0)YJ_4,\quad
 I[(Y-z)P],\quad IP_0
\]
in coefficients of \(Y^2,\ldots,Y^5\) vanishes.
This is pure in old ordinary parameters and \(V\),
with no \(K_*,x,t\) or late-ghost unknown.
No denominator involving a ghost–regular difference,
a coefficient of \(Q_4\), or a diagonal was needed.

For horizontal clock scale \(A=132J_4(V_{\rm unscaled})\)
the projector uses \(J_4^{\rm sc}(Y)=A^4J_4(Y/A)\).
The second column is then \(A^4P_5-P_5'(0)YJ_4^{\rm sc}\);
the third column is cleared by the live first-gap
ratio \(z=p/q\), replacing \(Y-z\) by \(qY-p\).
**coordinate-audit.py** checks these exact polynomial
coordinates and the independent old adjacent division
over four rational samples with nontrivial scales.

## 2. Every exact projected factor is excluded

**project.py** uses the monic rank-12 ordinary clock and
direct \(F_n\) tower from the
[earlier exact projection](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md).
Its exact raw norm has degree **912** and squarefree
degree **176**. Besides the four forbidden Jacobi
factors its support is:

| Projected irreducible factor | Live guard | Exact cap | Residue degree at 103 |
|---|---|---:|---:|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 12 |
| degree 12, constant 54123 | lower \(c_2\) | 9 | 4 |
| degree 60, constant −1461941766456 | determinant of old \(m\)-multiplication | 11 | 1 |
| degree 72, constant 70959087539532 | 1 | 12 | 19 |

The script checks the exact norm divisibility of the three
nontrivial guards. In the rank-four lower clock algebra
the second exact rank is at most 3, hence at most 9
after the free cubic extension. The other two rank drops
use the indicated exact norm zero in rank 12.
All guards are live at an actual candidate.

Use carrier variable \(E=qK_*\), with \(Z=qY-p\),
\(Q^\#=ZP+E P_0=qQ_4\). For common old adjugate
scale \(n\), put
\(L^\#=Z\widehat\ell-q\widehat\rho+E\widehat W_0\).
The exact zero \(ND=0\) at \(V\) gives the quadratic
gate obtained from
\[
 \left. (L^\#Q^\#-n Z I Q^\#)/P_0 \right|_{Y=V}=0 .
\]
The division is polynomial: it holds at the old roots
by the old three inverse fits and integration by parts,
and at zero by the primitive factors. The numerical
\(P_0(V)\) is live. This does not require \(V-z\ne0\).

The actual degree-drop span from §1 also implies that
the scaled first, second and \(IQ^\#\) columns have rank
at most two. The four \(3\times3\) minors in the indicated
four coefficient rows have degree at most one in \(E\).
Together with the exact adjacent gate of degree at most
two, they give the matrix for carrier cap three in
**rank.py**. Multiply every gate by the prescribed guard,
each clock basis element and each allowed power of \(E\).
The image is contained in the direct sum of four exact
guard images. The residue ranks 528, 144, 44 and 912
attain the full exact caps times \(4\) and the residue
degrees on the indicated components. Thus the rational
image itself contains the live guard in degree zero.
An exact candidate killing those gates would kill its
guard, an impossibility. No integrality of the unknown
carrier or clock is assumed, and the old coefficient
or carrier leaders need not be preserved one by one.

## 3. Consequence for the two required roots

The quotient \(L_5=Q_5/[(Y-z)(Y-x)]\) is therefore
exactly affine with a nonzero leader.
When the late-affine pivot is live as in the cited
beta-one proof, \(L_5(x)\ne0\): if it were zero,
the nonzero late affine polynomial
\(\lambda(Y-x)-\nu L_5(Y)\) would vanish at both
\(x\) and the distinct actual late clock \(y\).
Thus the third root is in the coefficient field and
differs from \(x\) and \(y\). The present argument
does not assert that it differs from \(z\).

Run **bash verify.sh** with SymPy and python-flint 0.9.
This packet gives written and exact executable arithmetic
proofs; it does not claim a Lean tableau exclusion.
