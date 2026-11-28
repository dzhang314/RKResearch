# Two exact refinements of the A(1)=0 subchart

Use reverse horizon one and the fixed-\(q\)
[scalar spectrum](README.md). This section concerns
the old forward \(A(0)=0\) branch, equivalently
\(A(1)=0\) in these coordinates.

## A resultant-free common-root exit

In the earlier
[symmetric first-two equation](../erk10-fifteen-split-host-late-chart/A-ORIGIN-ROOT.md),
\(E_0,E_1\) are the cardinal moments excluding the
first two interior clock factors. At a surviving
spectrum,
\[
                        E_1=R E_0\quad\Longleftrightarrow\quad c=2.
\]
If \(E_1=R E_0=0\), then \(\mu_a=E_1-bE_0=0\),
impossible at the live first ordinary row. Hence
under \(E_1=R E_0\) one may cancel \(E_0\ne0\).
The two quadratics in the alternating identity then
have common factor \(y-R\).
Cancel it at \(a,b\ne R\); distinct \(a,b\)
force \(c=2\).
Conversely if \(c=2\) the quadratics instead
share \(1-y\), a nonzero factor at \(a,b\).
Cancelling it forces \(E_1=RE_0\).
There is no need to divide by a two-by-two
sum/product reconstruction determinant.

In fact, with \(S=(1-y)(y-g)(y-h)(y-R)\),
\(M=y^2(y-c)^2\) and \(D\) the earlier Jacobi
derivative, the actual moments and the Möbius
gate give
\[
 E_1-RE_0=-de\, I\!\left(
        S(y)(y-f)y(y-c)\,[1+(D(c)-1)y/c]\right).
\]
To see this, subtract the known zero
\(I(S(y-f)M)\) from the expression for
\(E_1-RE_0\), and use
\(c-d-e=(D(c)-1)de/c\).
In particular the **entire rational branch**
\[
             c=2/3,\qquad \{g,R\}=\{1/2,3/4\}
\]
is excluded, allowing arbitrary rational \(d\)
with the existing physical guards. The earned
tail ratios fix \(h=11/30,\ f=-3/5\),
and the displayed polynomial moment is exactly
zero, independently of \(d\). Thus \(E_1=RE_0\)
would force \(c=2\), a contradiction.
The exact rational replay checks the fixed tail
moments, their nonzero pivots, and the zero
moment with \(1-(28/9)y\).

## A 7-adic necessity when c=2

The branch \(c=2\) itself is not closed.
The common-root equation supplies a new true
moment for the cubic \(s(y)=S(y)/(1-y)\) with
the three rational roots \(g,h,R\). Here
\(D(2)=1289\), so besides the two existing
blind moments its zero pairings (with weight
\(1-y\)) are against
\[
    JM,\quad (y-f)M,\quad (y-f)y(y-2)(1+644y).
\]
The exact signed minors of these three linear
forms give the cubic coefficient vector
\[
\begin{split}
 C_f(y)={}&86298f^2-477063f-5939\\
       &-6(111963f^2-582798f-5837)y\\
       &+6(242269f^2-1207208f-10357)y^2\\
       &-30(30891f^2-148922f-1137)y^3.
\end{split}
\]
The coefficients have no common root as
polynomials in \(f\), so this is the unique
cubic line whenever an actual monic survivor
exists. Let \(f=A/B\) with primitive integers.
The exact homogeneous coefficient congruence is
\[
 B^2 C_{A/B}(y)
   \equiv (A-B)(B y+A+5B)(y^2-2y+2)\pmod 7 .
\]
The quadratic \((y-1)^2+1\) is irreducible
modulo seven. If \(A\not\equiv B\pmod7\),
the primitive nonzero polynomial therefore
cannot split projectively, and neither can
the rational cubic. In particular \(f\)
must be 7-integral and \(f\equiv1\pmod7\).
Write \(f=1+7t\) and divide the full integer
coefficient polynomials by \(7\). The result
is congruent to \(t(y-1)(y^2-2y+2)\), so the
same argument forces \(t\equiv0\pmod7\).
Next write \(f=1+49v\), divide by \(49\),
and reduce:
\[
 \frac{C_{1+49v}(y)}{49}
  \equiv (y-1)\bigl[v(y^2-2y+2)-(y^2-2y+3)\bigr]
                                                        \pmod7 .
\]
The quadratic is irreducible if \(v\equiv0,3\).
Thus any survivor has
\[
             f\equiv1\pmod{49},\qquad
                  (f-1)/49\not\equiv0,3\pmod7 .
\]
These reductions use primitive projective
factorization, allowing a root at infinity
when a leading coefficient drops modulo seven.
They are necessary only; no rational
solution at the other residues is asserted.

## Exact finite sample

The included selector tests 5,040 ordered distinct
quadruples \((c,d,g,R)\) drawn from
\[
 -2,-1,-1/2,1/4,1/3,1/2,2/3,3/4,3/2,2 .
\]
It reconstructs the late clocks and uses the
nonsingular \(A(1)=0\) symmetric pivot to
test the first two rational clocks. The log
contains only failures of this finite screen.
This is not a proof for other rational inputs
or for a zero symmetric pivot.
