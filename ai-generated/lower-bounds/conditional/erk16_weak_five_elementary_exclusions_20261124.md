# Weak-five scalar gate: exact partial exclusions and a constant-test limit

These elementary arguments use the full `WeakFive16.Moments` interface. They exclude profiles of degree at most two and reflection-odd profiles. They do not exclude a nonsymmetric cubic or quartic, and are not Lean certificates.

Write \(w=x(1-x)\), \(c=(0,u,a,h,z)\) in physical order, \(Z=(X-a)(X-h)\), \(N=(X-u)(X-z)Z\), and \(M=qN\). The four end tests are \(\int_0^u xq=\int_0^u x^2q=0\) and \(\int_z^1 (1-x)q=\int_z^1 (1-x)^2q=0\). The actual extra tests are \(F(a)=G(h)=0\) for
\[
F(t)=\int_0^t x(x-u)q(x)\,dx,\qquad
G(t)=\int_t^1(1-x)(z-x)q(x)\,dx.
\]
The global law is \(\int_0^1 wMR=0\) for every \(\deg R\le5\) over the original ordered field. All integrals mean the differences of formal primitives. The displayed-factor budget with weight \(w\) charges every fixed-sign factor of \(M\) at most \(\deg q-2\); in particular \(\deg q\ge2\).

## Exact exclusion of all quadratic or lower profiles

Scale a quadratic \(q\) to be monic, \(q=X^2+BX+C\). The two left end tests, divided by \(u^2\) and \(u^3\), give
\[
u^2/4+Bu/3+C/2=0,\qquad u^2/5+Bu/4+C/3=0.
\]
Thus \(B=-6u/5\) and \(C=3u^2/10\). The reflected monic \(q(1-X)\) satisfies the same formulas at \(v=1-z\). Its coefficients yield \(u+v=5/3\) and \(1-6u/5+3(u^2-v^2)/10=0\). Hence \(u=v=5/6\). In particular \(z=1/6\) and \(q=5/24-x(1-x)\).

By differentiation and evaluation at zero,
\[
F(X)=X^2(X-u)^2(X-3u/4)/5.
\]
The actual \(a\) is distinct from \(0\) and \(u\), so \(F(a)=0\) gives \(a=5/8\). Reflection gives \(G(t)=F(1-t)\), hence \(h=3/8\). Put \(s=x(1-x)\). The constant global moment would require
\[
0=\int_0^1 s(5/24-s)(5/36-s)(15/64-s)\,dx
 =233/11612160.
\]
The last evaluation uses \(\int s,\int s^2,\int s^3,\int s^4\) equal to \(1/6,1/30,1/140,1/630\). This excludes degree two, and the [displayed-factor test](../../lean/RKCert/ReviewedNative/DisplayedFactorDegreeBudget.lean) already excludes the lower degrees.

## Exact exclusion of every reflection-odd profile

Assume \(q(1-x)=-q(x)\). By the degree range and monic normalization put \(t=x-1/2\), \(T=t^2\), and \(q=t(T-\ell)\). For a general monic cubic \(X^3+BX^2+CX+D\), the two left end tests give
\[
C=-6(u^2+Bu)/5,\qquad D=2u^3/5+3Bu^2/10.
\]
Here \(B=-3/2\), \(C=3/4-\ell\), \(D=-1/8+\ell/2\). Substitution gives
\[
\ell=3/4-9u/5+6u^2/5,\qquad (u-1)^2(8u-5)=0.
\]
The endpoint exclusions allow only \(u=5/8\). The reflected right side with \(-q(1-X)=q\) gives \(v=1-z=5/8\) in the same way, so \(\ell=3/32\) and \(z=3/8\).

Write \(Z=T-\sigma t+p\), with \(\sigma=a+h-1\) and \(p=(a-1/2)(h-1/2)\). The other two nodal factors give \(T-1/64\). Define
\[
A_j=\int_0^1 (1/4-T) T^j (T-3/32)(T-1/64)\,dx.
\]
Reflection makes the \(\sigma\) term contribute zero to both odd tests \(R=t,t^3\). These tests would give \(A_2+pA_1=A_3+pA_2=0\). The exact formula is
\[
A_j=L_{j+2}-(7/64)L_{j+1}+(3/2048)L_j,\qquad
L_j=\frac1{2^{2j+1}(2j+1)(2j+3)}.
\]
Thus \(A_1=199/5160960\), \(A_2=1697/227082240\), \(A_3=3397/2361655296\), and
\[
A_1A_3-A_2^2=-10723/27931769516851200\ne0.
\]
This rules out the odd profile even without either extra local port. The constant test alone gives \(-\sigma A_1=0\) and would only force \(\sigma=0\).

## Exact diagnostic: the restored constant does not suffice by itself

Over \(\mathbb Q(\sqrt{19})\) in the reals, take the odd \(q,u,z\) just derived and set
\[
a=(13-\sqrt{19})/20,\qquad h=1-a.
\]
The end pairs hold by the cubic coefficient formulas above. Direct differentiation gives
\[
F(X)=X^2(X-5/8)^2(X^2-13X/10+3/8)/6.
\]
It follows that \(F(a)=0\) and, by \(G(t)=-F(1-t)\), \(G(h)=0\). The bracket \(4<\sqrt{19}<5\) puts \(a\) in \((2/5,9/20)\) and \(h\) in \((11/20,3/5)\). These clocks, \(u,z\), are nonzero, distinct, not \(1\), and \(q\) is nonzero at them and at the origin. In fact \(qN\) has seven distinct interior roots: the other three are \(1/2\) and \(1/2\pm\sqrt{3/32}\). Thus the deficit-one root restriction is met.

\(N\) is reflection-even and \(q\) reflection-odd, so the profile passes \(R=1,t^2,t^4\). It does not pass \(R=t\): the latter integral is \(A_2-(a-1/2)^2A_1>0\), since \(A_2/A_1=1697/8756>1/100>(a-1/2)^2\). This is a counterexample only to using the six locals, the root classification, and the three even global tests in place of the full gate.
