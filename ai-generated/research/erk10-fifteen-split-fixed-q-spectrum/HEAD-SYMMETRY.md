# A common exact head solve in the two affine-cofactor branches

Use the fixed-\(q\) literal chart and reverse
horizon one. Put \(s=a+b,\ p=ab,\ \tau=de\),
\(M=y^2(y-c)^2\), \(T_3=(y-f)(y-g)(y-h)\), and
\(S=(1-y)(y-g)(y-h)(y-R)\).
These equations are necessary in **both**
\(A(1)=0\) and \(A(1)\ne0\); no division by
\(c-2a\) or by an ordinary score is used.
The labels \(c,d,g,R\) reconstruct \(e,f,h\)
by the earlier paid moment formulae.

Let \(B=(y-c)(y-d)(y-e)T_3\), and
\(E_i=I(y^{i+1}(y-1)B)\) for \(i=0,1\).
At \(z=a,b\) the scalar cardinals are
\(\mu_z=E_1+(z-s)E_0\).
The paid head ratios yield the division identity
\[
 \frac{A(y)N(y)+y(y-c)(y-R)[E_1+(y-s)E_0]}
                         {y^2-sy+p}
 = E_0y^2+[E_1-(c+R)E_0]y+k_0 ,
       \qquad k_0=\frac{A(0)N(0)}p .
\]
The numerator vanishes at both head sites
by their actual ratios; the leading two
quotient coefficients follow by degree, and
the constant follows at zero.

At another singleton root \(z\) of \(B\), its
cardinal is \(E_1+(z-s)E_0+(z-a)(z-b)
I(y(y-1)B/(y-z))\).
The exact common-ratio constraint at \(d\)
therefore gives \(k_0=-\Theta_d\), with
\[
 \Theta_z=z\,I\!\left[
    y(y-1)(y-c)(y-R)\frac{B(y)}{y-z}\right].
\]
The \(e\)-ratio is the same equation:
\(\Theta_e-\Theta_d=-(e-d)I(S(y-f)M)=0\).
More specifically
\[
 \Theta_d=-\tau\,I(y(y-1)(y-c)^2(y-R)T_3),\qquad
 \Theta_f-\Theta_d=-(f-d)(f-e)I(SM).
\]
Both identities follow by cancelling the
literal cardinal products and using
\(I(S yM)=f I(SM)\).

At the true \(f\)-transition \(KZ_f=0\),
substitute \(P_Z=y(y-c)P_3\), \(Q_Z=(y-c)Q_2\)
and the paid four-anchor identity
\[
   N P_3+y(y-c)Q_2
          =\frac{N(0)P_3(0)}{p d e}
                      (y-a)(y-b)(y-d)(y-e).
\]
After cancelling only distinct nonzero clock
differences, this yields
\[
  \widehat A(0)=k_0,\qquad
  \widehat A(f)=-\tau\, I(SM)\frac{P_3(f)}{P_3(0)},
          \qquad \widehat A=\frac{N(0)}p A .
\]
In particular \(A(1)=0\) is equivalent to
\(\widehat A(1)=0\), a condition on \(c,g,R\)
**independent of \(\tau\)**: both displayed
values are proportional to the nonzero \(\tau\).
For example this remains valid if a score at
\(b\) happens to vanish in the origin-root case.

Write \(\widehat A(y)=k_0+\ell_0y\).
The ordered head's affine \(N\) has
\[
 \frac{N(y)}{N(0)}
       =1-\frac{c^2-cs+2p}{cp}\,y
\]
by its coefficient formula. Thus \(A(y)N(y)=
(k_0+\ell_0y)[p-(c-s+2p/c)y]\).
Compare with the quotient identity above.
The coefficients of \(y,y^2\), cleared by \(c\),
are linear equations in \(s,p\).
**These are not independent:** the first row
is \(-c\) times the second. In fact
\[
                         \ell_0=R E_0-E_1-2k_0/c .
\]
Here is a direct exact reason. Set
\(D=D(c)\), \(\omega=(D-1)/c\), and use the
earlier expression for \(E_1-R E_0\).
The claimed equality follows if the integral
against \(S\) of
\[
 (y-f)y(y-c)\{f(1+\omega y)-(1-2f/c)(y-c)\}
          + \frac{P_3(f)}{P_3(0)}M(y)
\]
vanishes. Divide by \(y(y-c)\); the resulting
polynomial agrees at \(0,c,f\) with
\(\frac{f(f-c)}{P_3(0)}P_3(y)\), using
\(P_3(c)/P_3(0)=-D\).
Its difference is a multiple of
\((y-f)y(y-c)\). Thus before division the
expression is a linear combination of
\(P_Z\) and \((y-f)M\), both killed by \(I(S\,\cdot)\).
For \(P_Z=JM-\lambda yL_4(y)\), use the paid
blind \(I(SJM)=0\) and Jacobi orthogonality
against \(S/(1-y)\), a cubic.
Consequently there is no further cubic
consistency obstruction from these linear rows.

For a usable two-row solve take
\[
 \begin{split}
  &[E_0Rc^2-2k_0c]s
   +[-E_0Rc-E_0c^2+E_1c+2k_0-\ell_0c]p
   -E_1 R c^2+k_0c^2=0,\\
  &I(\Phi y^2)-s I(\Phi y)+p I(\Phi)=0,\quad
 \Phi=(y-1)(y-c)(y-d)(y-e)[V_c-\beta T_3] .
 \end{split}
\]
The second is the earlier true tail-cardinal
moment. The determinant must be treated as a
guard, not silently divided away. As
\[
          (y-d)(y-e)=y^2-cy+\tau(1+\omega y),
\]
all matrix entries are affine in \(\tau\).
On the nonsingular chart the head \(s,p\)
are rational functions with numerator and
denominator degree at most two. Before the
true nonlinear test, the remaining two
root splittings are the \(d,e\) quadratic
and this \(a,b\) quadratic. Those alone are
not asserted impossible.
