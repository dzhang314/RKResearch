# Two exact positive-characteristic scalar exceptions

These fixtures show that the characteristic-zero early pencil **scalar** gates do not extend unchanged to all fields of characteristic greater than the requested order. They do not construct a Runge–Kutta tableau or change any known stage bound. Use F=132X⁵−330X⁴+300X³−120X²+20X−1, j=1716X⁶−5544X⁵+6930X⁴−4200X³+1260X²−168X+7, J=Xj, and G=X(aj+bF). Write Iₖ(x)=(primitive(XᵏP))(x), or the same expression with R in the quartic case. Both examples have t,u, a,b,a+b and J(t),J(u) nonzero.

**F₂₃, cubic.** Set a=b=1, t=14, u=15, u/t=6, κ=5, and

    P=15+8X+19X²+22X³,   N=22X+11X²+10X³+18X⁴+14X⁵,   T=9+22X.

The signed moments (I₁,I₂,I₃) are (0,0,4) at t and (19,13,2) at u. J(t)=J(u)=10. These give I₁(t)=I₂(t)=0, I₂(u)−tI₁(u)=0, I₃(t)=κJ(t), and I₃(u)−tI₂(u)=κJ(u). The exact polynomial identity G T=N P holds and gcd(j+F,P)=X²+13X+17=(X−15)(X−18). This example directly falsifies the unrestricted cubic scalar/moment/mesh implication in this characteristic. **P(u)=0**: it does not certify an underlying stage pair with nonzero second mismatch. The additional common root 18 is not either prescribed pivot.

**F₅₃, nonzero-origin quartic.** Set a=1, b=3, t=17, u=37, u/t=24, κ=52=−1, and

    R=7+22X+51X²+13X³+20X⁴,   G=R X(X−17)(X−37).

Here (I₁,I₂)=(0,32) at t and (18,15) at u; J(t)=21, J(u)=26. Thus I₁(t)=0, I₂(t)=κJ(t), I₂(u)−tI₁(u)=κJ(u). The constant term of R is 7, and R(t)=R(u)=38≠0. The three polynomial obstruction forms A,M,B also evaluate to 0 at (z,t)=(24,17). This satisfies the literal scalar nonzero-origin quartic branch, including nonzero pivot amplitudes. It remains only a scalar example.

`certify_prime_exceptions.py` recomputes both identities coefficient-by-coefficient, verifies the formal derivative of each primitive, and checks every displayed value independently of the discovery search. `find_prime_exceptions.py 2000` checks all eligible prime-field rational knot pairs for primes from 17 through 1999, using a=1, all possible b consistent with the two knots, a+b, F(t), j(t) nonzero and nonvanishing leading degree. This is not a test of extension-field knots. `NativePencilPositiveFixtures.lean` is a standalone static source for the two fixtures using the original primitive and primal polynomials. No kernel pass is asserted by this archive.

**Cofinite field statement.** For a primitive ratio R and ordered projection data A,B, let the explicit integer D be the z-resultant of R and the t-resultant of A,B (using the advertised fixed t-sizes). The one good common-prime calculation makes D nonzero, even if the outer resultant loses degree modulo 1009. In every field of characteristic p with p not dividing D, a common t-root of A,B over an R-root is impossible. In the cubic case B is itself the fixed x-resultant of the pencil contrast and the cubic mask, giving full polynomial coprimality in every such field. This is a sufficient finite exceptional set, not a classification of all bad primes. The checked integer first-port identity also requires its known nonzero content (7 or 980) and, in the cubic case, a nonzero z. Small denominators in the physical parameter normalization require their own invertibility. Generic static Lean source is `NativePencilExceptionalCharacteristic.lean`.
