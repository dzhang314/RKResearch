# Separate branch \(A(1)=0\): symmetric first-two-node equations

Keep the [late rational chart](README.md) and reverse
horizon \(1\). This is the old forward \(A(0)=0\)
case: \(A(y)=\lambda(1-y)\), \(\lambda\ne0\).
The quadratic \(Q(y)\) need not vanish at \(1\).
The conclusion here is a two-by-two exact **necessary**
system for the sum and product of the first two
interior nodes, not an exclusion.

Let
\[
 B(y)=(y-c)(y-d)(y-e)(y-f)(y-g)(y-h),\qquad
 E_i=I(y^{i+1}(y-1)B(y))\quad(i=0,1).
\]
By the ten-site scalar cardinal identity,
\(\mu_a=E_1-bE_0,\ \mu_b=E_1-aE_0\).
The literal first two ratios in the normalized
head, transferred back to \(a,b\), are
\[
 \frac{w_a}{u_a}=-\frac2{a^2},\qquad
 \frac{w_b}{u_b}=-\frac{2(c-2a)}{ab(c-2b)} .
\]
They follow equivalently from the affine numerator
\[
 N(y)=\frac{2[(-2ab+ac+bc-c^2)y+abc]}{a(2b-c)}
\]
in \(w/u=N(y)/(y^2(y-c))\).
The nonzero denominator \(2b-c\) follows from the
head's \(\kappa=c/(2c-4b)\). We do **not** require
\(c-2a\ne0\) or \(w_b\ne0\).
For an ordinary singleton, the scalar cardinal
and affine-cofactor identity gives
\(w_z/u_z=-\mu_z(z-R)/(zA(z))\) when \(A(z)\ne0\),
as it is at both of these distinct nodes.
Hence the two head equations clear directly as
\[
 \begin{split}
 a(a-R)(E_1-bE_0)&=2\lambda(1-a),\\
 a(c-2b)(b-R)(E_1-aE_0)&=2(c-2a)\lambda(1-b).
 \end{split}
\]
Eliminating \(\lambda\) by cross multiplication
and cancelling only \(a\ne0\) gives
\(C_2(b)D_2(a)=C_2(a)D_2(b)\), where
\[
           C_2(y)=(y-R)(c-2y),\qquad
           D_2(y)=(1-y)(E_1-yE_0).
\]
If \(C_2(y)=c_2y^2+c_1y+c_0\) and
\(D_2(y)=d_2y^2+d_1y+d_0\), dividing the
alternating difference by \(a-b\ne0\)
yields the exact symmetric equation
\[
 (c_2d_1-c_1d_2)p
 +(c_2d_0-c_0d_2)s
 +(c_1d_0-c_0d_1)=0,\qquad s=a+b,\ p=ab.                 \tag{1}
\]
This calculation includes the \(c=2a,w_b=0\)
spectral subcase without division.

For the [tail cardinal equation](README.md#one-explicit-ordinary-cardinal-equation-including-a10),
put
\[
 \Phi=(y-1)(y-c)(y-d)(y-e)\,[V_c(y)-\beta T(y)]
\]
using the previous \(T,\beta,V_c\). That equation
becomes
\[
                 I(y^2\Phi)-sI(y\Phi)+pI(\Phi)=0 .       \tag{2}
\]
With exact reconstructed \(e,f,h\), equations
(1)–(2) have coefficients depending on
\(c,d,g,R\) only. When their determinant is
nonzero, the sum and product of the two
first interior nodes are fixed over \(\mathbb Q\).
In particular \(s^2-4p\) must be a nonzero
rational square before either order of the
two nodes can be tried. A zero determinant
does not justify division and is an explicit
separate case. Further head ratios at \(d,e,f\),
the true residual/chronology constraints and
other rooted orders still need to be met.
