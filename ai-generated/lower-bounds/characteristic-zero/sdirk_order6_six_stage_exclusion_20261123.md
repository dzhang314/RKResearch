# A six-stage strict real SDIRK cannot have classical order six

**Theorem.** Every six-stage real lower triangular RK method with one common nonzero diagonal has classical order at most five. Hence the strict SDIRK stage interval for p=6 narrows from [6,8] to **[7,8]**. Signed and zero interior weights, repeated or exterior abscissae, either sign of the diagonal, and all real RK tableaux are covered. This does not settle seven stages, and it does not exclude order-six DIRK with variable or partially zero diagonals. No claim of literature priority.

The proof combines four small exact obstructions: saturation of the full/pure flags, one chronological three-stage prefix incidence, a causal coupling through two reflected quadratic output profiles, and a last-two-coordinate weighted defect. It does not assume an order-preserving weighted-transpose method or a nonsingular weight matrix.

**Normalization and equality flags.** Suppose p=6,s=6. Put z=1/γ, rescale A and c by 1/γ, and henceforth call the rescaled objects A,c, so A has diagonal 1, c=Ae, the scalar time is t=x/γ with endpoints 0,z, and the output pairing is (1/z)∫₀ᶻ. Put N=A−I, C=diag(c), R=CA−AC−A², B=diag(b). Origins and ends are preserved even if z<0; any use of definiteness follows from the original integral on [0,1]. The companion note sdirk_saturated_weighted_mirror_duality_20261123.md proves that the full forward and scalar reverse ranks through grades 0,…,5 are 1,2,4,5,6,6, and the pure ranks are 0,0,1,2,4,5. In particular D(1) holds, bA=b(zI−C), b₆,b₅ are nonzero, c₆=z−1, and b₆a₆₅=v b₅ for v=z−1−c₅. Indeed a zero terminal weight permits trimming; if b₅=0 then a₆₅=0 by D(1) and every scalar context vanishes on index 5, contradicting the full reverse rank. The first two chronological abscissae are distinct: otherwise the strictly preceding tap is zero, so these two stage evaluations coincide on every tree feature, contradicting full forward rank. We write c₁=1,c₂=1+u with u≠0.

Set g=Ac−c²/2 (componentwise squares), so Re=−2g. Its first component is 1/2 and its second is κ(u)/2, κ(u)=1+2u−u². Ng has initial entries 0,u/2. These are independent pure features of grade ≤3 and hence form the whole F₃. Consequently
    (C−I)g=κ(u)Ng,
by comparison of the first two coordinates. Also [A,R]e is pure of grade ≤3; the first two diagonals of [A,R]=[N,R+I] vanish, so [A,R]e vanishes in its first two entries and must be zero. For the third row write w=c₃−1 and r=a₃₂ (thus a₃₁=w−r). The third coordinate of the commutator equality gives ru(2u−w)=0. The third coordinates of 2g and 2Ng are, respectively,
    G=1+2w−w²+2ru,    V=w+r(κ(u)−1).
The first equality above requires wG=κ(u)V.

There are two cases. If r=0, then w cannot be 0 or u: the third stage would duplicate the first or second on all tree features by its single-parent row. Thus w=2−u and u is neither 1 nor 2. If r≠0, then w=2u and
    d=−2+u+4u²−u³,    r=2u(3u−2)/d.
In fact dr=2u(3u−2); d=0 would force u=2/3 where d=4/27.

**The collapsed cubic at the first three stages.** Define the shifted cubic Legendre polynomial P(t)=20t³−30zt²+12z²t−z³. Since E₃/F₃ has dimension three with independent classes 1,c,c², and P is orthogonal to all scalar quadratics on [0,z], P(c) belongs to F₃: pair its polynomial representative modulo F₃ against any quadratic and use the ordinary order-six conditions. Comparing the first two coordinates yields the vector identity
    P(c)=2P(1)g + (2/u)(P(1+u)−κ(u)P(1))Ng.
Its third coordinate requires P(1+w)−P(1)G−(P(1+u)−κ(u)P(1))V/u=0. In the zero-tap case this equals −2(u−2)(u−1)(z³−12z²+60z−120). In the nonzero-tap case it equals 2u² T/(u³−4u²−u+2), with T exactly as given in the replay below.

**Causal quadratic bridge.** Write L_j(t) for the ordinary Laguerre polynomials, L₀=1, L₁=1−t, L₂=1−2t+t²/2. Two quadratic profiles with lifts zero on the first two indices are (t−1)(t−1−u), using its literal scalar column, and L₂(t), using N²e. The corresponding entries at the third stage are w(w−u) and ru. In the zero-tap case H=L₂ therefore clears the first three. In the nonzero-tap case a nonzero cleared profile is H=h₀L₀+h₁L₁+h₂L₂ with
    (h₀,h₁,h₂)=(3u−2,(3u−2)(u−2),(u−1)²(u−2)).
For verification, use (t−1)(t−1−u)=L₀+(u−2)L₁+2L₂. The clearing combination d L₂−(3u−2)(t−1)(t−1−u) is minus the displayed H since d−2(3u−2)=−(u−1)²(u−2). Its third entry is d r u−2u²(3u−2)=0.

Independently, with y=z−t, reverse rows with profiles L₂(y) and L₀(y)+(v−2)L₁(y) both clear the last two indices. The former is bN². For the latter subtract twice bN² from the literal row b(y−1)(y−1−v), which vanishes at c₅,c₆ before subtraction. These statements use no division by interior weights. Let x_H be the forward lift of H clearing the first three. Then Nx_H clears the first four, so both of these reverse rows annihilate it on six stages. Their respective profiles therefore give ordinary order-six scalar identities (budgets 2+1+2=5). On Laguerre polynomials (J−I)L_j=−L_(j+1) for J integration from 0. The convolution (1/z)∫₀ᶻ L_i(t)L_j(z−t)dt is m_(i+j)=(L_(i+j)(z)−L_(i+j+1)(z))/z; e.g. multiply their formal Laplace transforms (s−1)^i/s^(i+1) and (s−1)^j/s^(j+1), or expand both sides. With U_j=Σ_i h_i m_(i+j), the two necessary equations are
    U₃=0,    U₁+(v−2)U₂=0.
For H=L₂ the first is m₅=0, coprime to the cubic in the zero-tap chart, immediately excluding that branch.

**Two terminal coordinates, not division by B.** The row gᵀB is pure and annihilates E₃. Ann(E₃) is one-dimensional, generated by bR (nonzero terminal component −b₆). Its penultimate component is −b₅+(v−2)b₆a₆₅=−κ(v)b₅. Both end weights are nonzero, whence
    g₅=κ(v)g₆
even when g₆=0. Put D(t)=uκ(u)P(1)+(P(1+u)−κ(u)P(1))(t−1). The preceding two degree-three identities imply 2D(c_i)g_i=uκ(u)P(c_i). Thus if κ(u)≠0,
    O=P(z−1−v) D(z−1) − κ(v)P(z−1) D(z−1−v)=0.
No division by any value of D, any numerator polynomial, or g₆ has been made. The remaining κ(u)=0 alternative is separately tested.

**Exact elimination over Q.** For r≠0, the first causal equation and the prefix cubic condition have u-resultant equal, up to a nonzero constant, to z⁴ times (z³−18z²+72z−48)² times the irreducible degree-12 polynomial z¹²−68z¹¹+2016z¹⁰−34400z⁹+374400z⁸−2723040z⁷+13510080z⁶−45964800z⁵+106488000z⁴−164160000z³+158976000z²−82944000z+13824000. Exclude z=0 by γ≠0. On each other factor the ideal from the two causal equations and T with either κ(u)=0 or O=0 is the unit ideal over Q. The full deterministic replay below took a few seconds in SymPy 1.14.0 and printed its success message. The gcd, resultant, subtractions and individual Gröbner reductions use characteristic zero. This proves the unconditional lower endpoint 7.

~~~python
import sympy as S
z,u,v=S.symbols("z u v"); E,F=S.expand,S.factor
P=lambda t:20*t**3-30*z*t**2+12*z**2*t-z**3
k=lambda x:1+2*x-x*x
D=lambda t:u*k(u)*P(1)+(P(1+u)-k(u)*P(1))*(t-1)
m=[S.cancel((S.laguerre(i,z)-S.laguerre(i+1,z))/z) for i in range(6)]
# r=0: two univariate polys in z must have a common root
assert S.gcd(m[5],z**3-12*z**2+60*z-120)==1
# r nonzero: H clears the first three
h=[3*u-2,(3*u-2)*(u-2),(u-1)**2*(u-2)]
U=lambda j:sum(h[i]*m[i+j] for i in range(3))
T=2*u**3*z**3-24*u**3*z**2+120*u**3*z-240*u**3-10*u**2*z**3+84*u**2*z**2-240*u**2*z+120*u**2+15*u*z**3-84*u*z**2+120*u*z-6*z**3+24*z**2
O=P(z-1-v)*D(z-1)-k(v)*P(z-1)*D(z-1-v)
f=E(U(3)); t=E(U(1)+(v-2)*U(2))
res=S.factor_list(S.resultant(f,T,u))[1]
assert sorted((S.degree(Z,z),mult) for Z,mult in res)==[(1,4),(3,2),(12,1)]
for Z,mult in res:
 if S.degree(Z,z)==1:
  assert S.rem(Z,z,z)==0
  continue
 Q=[f,T,t,Z]
 assert S.groebner(Q+[k(u)],v,u,z).polys[-1].as_expr()==1
 G=S.groebner(Q,v,u,z)
 Ored=G.reduce(E(O))[1]
 assert S.groebner(Q+[Ored],v,u,z).polys[-1].as_expr()==1
print("both charts excluded over Q, without a weight inverse")
~~~
