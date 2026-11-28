# The late-ghost affine pivot is live in the direct Fn beta-one chart

**Result.** In the normalized invisible-six DIRK11/13 no-late
profile with live reciprocal multiplier, \(\alpha=\beta=1\)
and direct noncontact \(F_n\), assume the fourth and fifth
regular reverse diagonals are nonzero. The first reverse
ghost \(y\) after the fifth regular row is uniquely determined
by a live affine equation over the field of the previous
clocks and carrier. In particular the late affine identity
branch, including the exceptional **kernel coefficient**
\(\lambda=-1\), is impossible. This is not the already
excluded **old slope** \(\ell_1=-1\), nor an exclusion of the
whole beta-one profile. The unrestricted real DIRK11 interval
remains **13–14**.

Use \(Y=1-c\), \(N=A^{\mathsf T}\) in literal reverse order,
\(W(f)=b_{\rm wt}f(Y)\), zero-constant primitive \(I\), and
the actual columns and constants of the
[gap-diagonal proof](../dirk11-thirteen-invisible-six-alpha-one-gap-diagonals/README.md).
In particular the reverse prefix is
\(T,v,u,w,z,V,x,B,y\), the ghost clocks \(z,x,y\) are distinct,
and the actual first-middle and first-late diagonals satisfy
\(d_x=d_y=0\). The five ordinary clocks are distinct and
nonendpoint, with live weights and reciprocal carrier
\(U_r\). Write \(R=(Y-v)(Y-u)(Y-w)\), \(P_0=YR\),
\(P_5=(Y-V)P_0\), \(P=Ym\).
In the clean reciprocal gauge \(G/b_{\rm wt}=YJ_4/U_r\)
on the five ordinary slots. No origin weight is divided by.

## 1. An affine identity would force a forbidden pure Jacobi line

Set
\[
 \begin{gathered}
 Q_4=(Y-z)P+K_*P_0,\qquad D=(Y-z)G-W(Q_4),\\
 L=(Y-z)\ell-\rho+K_*W_0=\lambda(Y-z)(Y-x),\\
 IQ_4=\lambda(Y-x)Q_4+\eta P_5,\qquad
 E=(Y-x)D-\omega W(P_5),\quad \nu=\eta-(1+\lambda)\omega .
 \end{gathered}
\]
The proved \(\lambda,\nu\) are live, and \(E\) is zero
through \(B\). Also
\(W(IP_5)-NW(P_5)=GQ_5+\theta H_{\rm bary}\), with \(Q_5\)
having the two actual roots \(z,x\), and
\[
 (1+\lambda)NE=(Y-x)ND+\nu NW(P_5).
\]
At the late ghost this yields the affine equation
\(\lambda(y-x)=\nu Q_5(y)/[(y-z)(y-x)]\).

Suppose that affine polynomial is identically zero and
\(1+\lambda\ne0\). Then
\(\nu Q_5=\lambda(Y-z)(Y-x)^2\).
At every actual ghost, \(ND\) equals
\(G\lambda(Y-z)(Y-x)\) and \(NW(P_5)=-GQ_5\),
since its ordinary weight and \(H_{\rm bary}\) are zero.
The kernel transfer forces \(NE\) zero at **all** ghosts.
By the true zero prefix of \(E\), \(NE\) is zero at the
terminal and all five ordinary slots as well. Thus \(NE\)
is supported only at the literal origin \(O\).

Define \(S=(Y-x)Q_4+\omega P_5\), so
\(E=(Y-x)(Y-z)G-W(S)\).
For \(j=1,\ldots,4\), pair \(NE\) with \(c^j\); the result
is zero because \(c_O=0\). This is the same as pairing
\(E\) with \(Ac^j\). The \(G\)-term is zero by the actual
\(G\in E_7^\perp\) and product bound \(2+j+1\le7\).
The scalar term \(W(S)\) sees only the exact primitive
\(c^{j+1}/(j+1)\), since \(F_{j+1}\) for \(j\le4\)
is ghost-supported (and \(F_2=0\)). The actual quadrature
pays degrees through 10. Hence the four exact conditions
are
\[
 \int_0^1 (1-Y)^k S(Y)\,dY=0,\qquad k=2,3,4,5.
\]
Here integration is the formal rational coefficient map,
not an ordering assumption on the field.

The polynomial \(S/Y\) has degree at most four and is not
zero: on the three old distinct clocks,
\(S(r)=(r-x)(r-z)P(r)\) with \(P(r)\) live, so two possible
clock contacts cannot kill all three. The four displayed
conditions make \(S/Y\) lie on the one-dimensional line
orthogonal to degrees zero through three for the density
\(Y(1-Y)^2\). **pure-orthogonality.py** verifies its exact
nonzero \(4\times4\) minor and that the line is spanned by
\[
 E_-(Y)=66Y^4-120Y^3+72Y^2-16Y+1,\qquad
 2(Y-1)E_-=J_5-J_4.
\]
Thus \(S/Y=a E_-\) with \(a\ne0\).
At each of the five ordinary reverse clocks, \(E=0\)
gives \(U_r S/Y=(Y-x)(Y-z)J_4\).
The true ordinary quintic is
\(T_5=(J_5+\mu J_4)/132\), so at those clocks
\(2(Y-1)E_-=-(\mu+1)J_4\) with \(J_4\ne0\).
This gives equality of the two cubics
\[
 -a(\mu+1)U_r=2(Y-1)(Y-x)(Y-z),
\]
since they agree at five distinct clocks. The coefficient
\(\mu+1\) is live (otherwise 1 would be an ordinary root
of \(T_5\)); the equality contradicts live \(U_r(1)\).
This part does not use a direct \(F_n\) formula.

## 2. The distinct exceptional kernel coefficient \(\lambda=-1\)

Use the old \(m=Y^2+rY+s\) gauge in this derivation.
The [old-contact proof](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-old-contact/README.md)
and [small direct-Fn contacts](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-small-contacts/README.md)
supply the live old factors
\[
 r,\ s,\ r^2-3s,\ r^2-6s,\ 2r^2-9s,\ 5r^2-24s,\quad
 \Delta=-c_2r^2+6c_2s+r^3-7rs .
\]
The [old slope exclusion](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-minus-one/README.md)
gives \(1+\ell_1\ne0\).
The exact direct \(F_n\) old parameters are
\[
 c_0=\frac{s^2(3c_2-4r)}{r^2-3s},\quad
 c_1=\frac{6s(c_2-r)}r,\quad z=\frac{rs}{r^2-6s}.
\]
Write \(W_2=[Y^2]W_0,\ \rho_2=[Y^2]\rho\) and
\(F=c_2(r^2-12s)+12rs\). **old-pin.py** verifies
\[
 W_2=\frac{(r^2-6s)F}{10(2r^2-9s)\Delta}.
\]
If \(W_2=0\), then \(r^2-12s\) is live and
\(c_2=-12rs/(r^2-12s)\). The same exact old fit gives
\(\ell_1=(r^2-6s)/(3(r^2-4s))\), with \(r^2-4s\) live
by \(\Delta=r(r^2-3s)(r^2-4s)/(r^2-12s)\).
But the exact identity
\((1+\ell_1)\rho=\ell^2+(1/4-\ell_1)W_0\) gives
\((1+\ell_1)\lambda=\ell_1\) at \(W_2=0\).
For \(\lambda=-1\) this forces \(2\ell_1=-1\),
hence \(5r^2=24s\), impossible. Thus \(F,W_2\) are live
on the exceptional branch being tested.

Now directly pin
\[
 K_*=\frac{\rho_2-\ell_1-1}{W_2},
 \qquad x=z-\rho'(z)+K_*W_0'(z).
\]
The first is the leader of \(L\) and the second its
derivative at \(z\), using \(\lambda=-1\).
The actual \(x\ne0\) small-contact proof gives
\(\eta\ne0\). The exact primitive identity gives
\(\eta=6(1+K_*)/5\) by leading coefficient and
\(\eta Vc_0=x(-zs+K_*c_0)\) by its coefficient at \(Y\).
No regular diagonal is divided by. **old-pin.py** checks
that these identities impose the pure ordinary gate
\[
 3V(5r^2-24s)F
   =2s(5r-3c_2)(-18c_2r^2+81c_2s+25r^3-111rs).
\]
Unlike a large generic carrier projection, this is
independent of \(t\) and the late-ghost unknown.

## 3. Exact projection and a single true first-middle test

**project.py** uses the scaled monic rank-12 ordinary
clock and direct \(F_n\) tower over \(\mathbb Q[V]\), as
in the [earlier exact projection](../dirk11-thirteen-invisible-six-alpha-one-live-fn-zero-fifth/README.md).
It forms the absolute norm of the just-displayed gate,
clearing the horizontal clock scale \(132J_4(V)\) and
the old direct-ratio denominators. It removes only
common content supported on ordinary forbidden factors
\(V(V-1)J_4 E_-E_+E_{\rm rep}\), known live on candidates.
The exact raw norm degree is **1164**, squarefree
degree **164**. The only forbidden factors occurring
in that squarefree norm are \(J_4\) and the \(E_+\)
endpoint factor. The complete surviving support is:

| Exact irreducible factor | Live guard | Exact rank cap | Prime / residue degree |
|---|---|---:|---|
| degree 12, constant 16227 | homogeneous \(c_1+6s\) | 11 | 103 / 12 |
| degree 12, constant 54123 | \(c_2\) in lower rank-four algebra | 9 | 103 / 4 |
| degree 24, constant 482450985 | homogeneous \(F\) | 11 | 103 / 4 |
| degree 108 | 1 | 12 | 101 / 1 |

For the three nontrivial guards, the exact factor divides
the corresponding multiplication norm. The lower \(c_2\)
guard has rank at most three in rank four, hence at most
nine after the free cubic extension. Every listed guard
is live at an actual candidate.

Recover the carrier from the genuine quartic \(V\) read.
Since \(V-z\ne0\) in the nonzero-\(d_V\) profile of the
[fourth-clean separation](../dirk11-thirteen-invisible-six-alpha-one-direct-fn-fourth-separation/README.md),
\[
 k=G_V/b_V=P(V)+K_*P_0(V)/(V-z),\quad
 U_r(V)=VJ_4(V)/k,\quad
 d_V=(IP_0(V)-kW_0(V))/P_0(V).
\]
Then \(U_r=M+tR\) is fixed. With the true \(d_x=0\), one
necessary scalar is the actual \(P_0\) commutator
\[
 (x-V-d_V)W_0(x)
   -\frac{d_V^2 V}{k}
       \left[R(x)-R(z)\frac{U_r(x)}{U_r(z)}\right]=0 .
\]
**rank.py** clears only the known live scales from the
old inverse fits and the pinned \(K_*,x,k,U_r,d_V\),
and cancels the shared polynomial root \(Y-z\) using
live \(x-z\). In particular it never divides by a value
of \(R\) at a ghost. **coordinate-audit.py** independently
verifies the resulting pinned numerator and primitive
identity on four exact QQ old-coordinate samples.

At the listed residue primes multiplication by the product
of the guard and the pinned commutator alone has ranks
\(132,36,44,12\) respectively, attaining the exact caps
times the residue degrees. Their images are therefore
the full guard images in characteristic zero. Evaluating
the vanishing commutator at an actual exact candidate
would kill its live guard, a contradiction. This argument
does not reduce unknown clocks or tableau coefficients.

## 4. A usable exact late-clock reduction

Thus \(\lambda\ne-1\). Section 1 excludes the remaining
affine identity. Write \(L_5=Q_5/[(Y-z)(Y-x)]\); if
\(L_5=a_0+a_1 Y\), the actual late ghost has
\[
 y=\frac{\lambda x+\nu a_0}{\lambda-\nu a_1},
 \qquad \lambda-\nu a_1\ne0.
\]
Indeed a nonzero affine polynomial with an actual root
cannot have zero leader. The actual late commutator
from the gap-diagonal proof is a quadratic in \(y\) after
the same two polynomial factors are cancelled. Substituting
this rational \(y\) and clearing the live leader squared
therefore gives a genuine polynomial gate on the previous
clocks and carrier, without adjoining a late clock.
We do not claim that the resulting generic projection
has been eliminated.

Run **bash verify.sh** with SymPy and python-flint 0.9.
The exact written/source argument is separate from the
local Lean scalar checks, and makes no end-to-end Lean
tableau claim.
