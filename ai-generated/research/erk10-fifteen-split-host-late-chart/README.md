# Rational late-node chart and a unified tail cardinal equation

Use the rational width-eleven split-host branch with
the [terminal](../erk10-fifteen-split-host-terminal/README.md)
and [grade-five](../erk10-fifteen-split-host-grade-five/README.md)
identities already earned. Normalize now by the horizon
\(H\) to reverse ordinates \(y=1-x\) and use the names
\[
                    0,a,b,c,c,d,e,f,g,h,R .
\]
Thus \(a\) is the earlier normalized first interior
\(1/H\); the external origin is at \(y=1\).
The unscored host \(R\) remains a singleton and
\(\eta_R=1,\ u_R\ne0\).
All scalar integrals below are formal on \([0,1]\).
Put \(M=y^2(y-c)^2\), \(J M=\int_0^y M(t)\,dt\).

## All three late reconstruction denominators are paid over Q

The first tail after \(d\) is forced by the
[Jacobi derivative gate](../erk10-fifteen-split-host-grade-five/README.md#a-scalar-möbius-gate-on-the-two-first-tail-sites):
\[
                  e=\frac{c(c-d)}{c+(D(c)-1)d},
       \qquad D(c)=210c^4-336c^3+168c^2-28c+1 .
\]
The denominator is nonzero in the physical branch.

Set \(U(y)=(y-g)(y-R)\) and \(W(y)=(1-y)JM(y)\).
The pure blind moment from the terminal proof is
\(\int W U(y)(y-h)\,dy=0\). We claim the
denominator is **unconditionally** nonzero over
the rationals in this actual branch, so
\[
                  h=\frac{\int W(y)yU(y)\,dy}
                            {\int W(y)U(y)\,dy} .       \tag{1}
\]
If the denominator vanished, the numerator
would vanish as well. Then \(U\) would be the
unique monic quadratic orthogonal to \(1,y\)
for the positive formal weight \(W\) on \((0,1)\).
The four exact moment entries are
\[
 \begin{split}
 m_0&=(7c^2-7c+2)/420, &
 m_1&=(28c^2-30c+9)/2520,\\
 m_2&=(40c^2-45c+14)/5040,&
 m_3&=(150c^2-175c+56)/25200 .
 \end{split}
\]
For \(U=y^2+u y+v\), solve the two linear
equations from these moments. Its discriminant
is \(B(c)/(100 D_0(c)^2)\), where
\[
\begin{split}
 D_0(c)&=56c^4-105c^3+75c^2-24c+3,\\
 B(c)&=42000c^8-154000c^7+246980c^6-225900c^5\\
     &\qquad+128904c^4-47088c^3+10797c^2-1428c+84 .
\end{split}
\]
The pivot is nonzero by the positive degree-one
Gram form, since \(W\) is positive on the open
interval apart from the isolated endpoints
(where it may vanish).
There is **no rational square value** of \(B(c)\).
For \(c=A/B_0\) in primitive integers, clear
the square denominator \(B_0^8\).
If \(A,B_0\) are both \(7\)-units, reduce the
homogeneous degree-eight numerator modulo seven:
the affine nonzero residues \(1,\ldots,6\) give
\(6,5,6,3,6,3\) respectively, all nonsquares.
If \(A\) is divisible by seven, the constant
coefficient \(84\) has valuation exactly one
and the adjacent coefficient \(-1428\) is a
multiple of seven, so the whole homogeneous
value has valuation exactly one. If \(B_0\)
is divisible by seven, use the leading coefficient
\(42000\) of valuation one and the adjacent
\(-154000\) of positive valuation instead.
These are all primitive projective cases.
Thus the monic orthogonal quadratic could not
have both \(g,R\) rational, proving the claim.

Finally with \(S=(1-y)(y-g)(y-h)(y-R)\),
the actual blind moment \(I(S(y-f)M)=0\) gives
\[
                  f=\frac{\int y S(y)M(y)\,dy}
                            {\int S(y)M(y)\,dy} .        \tag{2}
\]
The denominator is nonzero: the literal identity
\(I(SM)=S(f)Z_f\) was proved by the terminal
cofactor argument (up to a nonzero common scaling
upon changing \(H\)), and \(Z_f\ne0\) by the
actual grade-five transition. Thus \(e,h,f\) are
rational functions of \(c,d,g,R\), without omitting
a denominator-zero rational branch. These are
necessary conditions, not a sufficiency theorem
for an actual tableau.

## One explicit ordinary-cardinal equation, including A(1)=0

Let \(F\) be the monic polynomial on the nine
ordinary sites \(a,b,c,d,e,f,g,h,R\). A nonzero
affine numerator \(A\) and a quadratic \(Q\) satisfy
\[
 u_z=\frac{A(z)}{(1-z)F'(z)}\quad
       \text{at ordinary singletons},\qquad
 \boldsymbol w\odot\boldsymbol\eta
       =Q(\boldsymbol y)\odot\boldsymbol u .
\]
In particular \(Q(R)=0\), \(A(R)\ne0\), and
\(A(1)Q(1)=0\) by the constant true dirt moment.
Therefore
\[
              L(y)=\frac{A(y)Q(y)}{(y-R)(1-y)}
\]
is a nonzero polynomial of degree at most one.
This includes the actual \(A(1)=0\) branch:
there \(Q\) need not have a root at \(1\).
No degree or nonzero guard for \(Q(1)\) alone
is assumed.

Let \(\mathscr P=y(y-1)F/(y-R)\) be the
ten-site scalar polynomial (the host has zero
score). For \(z=f,g,h\) let
\(\mu_z=I(\mathscr P(y)/(y-z))\).
The exact cardinal rule gives
\(w_z=\mu_z/\mathscr P'(z)\).
The augmented terminal interpolation says
\[
        \eta_z=\frac{(1-z)V_c(z)}{(1-R)V_c(R)} ,
\]
where \(V_c\) is the explicit terminal cubic.
Use the pointwise relation \(w_z\eta_z=Q(z)u_z\)
and cancel only distinct nonzero clock factors:
\[
                    \frac{\mu_z V_c(z)}{z}
                         =-(1-R)V_c(R)L(z).              \tag{3}
\]
This does not divide by \(w_z, u_z, Q(z)\),
or \(V_c(z)\), so also covers singleton zero
weights and cofactor roots.

Let \(T(y)=(y-f)(y-g)(y-h)\) and
\(\beta=V_c(0)/T(0)\). The ordinary
three-site cofactor annihilates the affine
right side of (3). The Lagrange interpolation
polynomial for \(V_c(z)/z\) on those three
sites is \((V_c(y)-\beta T(y))/y\): division
is polynomial, degree at most two, and its
values at the three sites are prescribed.
Substituting the exact cardinal integrals
therefore gives the single scalar moment
\[
 I\!\left((y-1)(y-a)(y-b)(y-c)(y-d)(y-e)
                         [V_c(y)-\beta T(y)]\right)=0 .  \tag{4}
\]
In particular this is linear in \(b\) once
\(a,c,d,g,R\) are fixed and (1)–(2) and the
formula for \(e\) have been applied. If the
linear coefficient in \(b\) vanishes as well
as its constant, (4) alone does not select
\(b\); that pivot is not asserted paid here.
This chart supplies an exact rational target
for the remaining head/terminal cardinal
equations, not a found tableau or a complete
exclusion. The [separate origin-root branch](A-ORIGIN-ROOT.md)
reduces the first two interior labels to a two-by-two
linear system in their sum and product when that pivot
is nonzero.

## Replay

    python3 -B audit.py | diff -u exact-audit.txt -

From the overlay or repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-split-host-late-chart/sources.sha256
