# Complete projective boundary: W=a j+b F, [a:b] arbitrary

Keep distinct nonzero ordered t,u and the original literal primitive rows. Normalize a=1 if possible, and b=1 when a=0. Most of the earlier calculations use a≠0. This addendum treats the whole projective pencil over characteristic zero or p>13. It classifies scalar profiles, not Runge–Kutta tableaux, and changes no stage bound.

The original notations are W=a j+b F, J=Xj, F=132X⁵−330X⁴+300X³−120X²+20X−1, and j=1716X⁶−5544X⁵+6930X⁴−4200X³+1260X²−168X+7. For a profile P (or R), Iₖ(x) is its zero-constant primitive after multiplication by Xᵏ, evaluated at x.

* [Cubic bare coprimality and full mesh](CUBIC-BARE-GLOBAL.md): four integer components give all bare noncoprimality exceptions when a,b are nonzero. Only p=23 survives the full degree-five mesh, and its second amplitude is zero. Neither pure pencil adds an exception.
* [Original quartic classification](QUARTIC-GLOBAL.md) and [ground-field square test](QUARTIC-SHAPES.md): the normalized guarded quartic solutions need at most a separable quadratic extension.
* [Dropping quartic guards and setting cubic leakage to zero](UNGUARDED-PORTS.md): dropping the terminal guard adds just p=155773 and p=16380373, with a=1,b=−1,u=1. The other three value guards are automatic. The further pure-pencil factor case adds p=2662133 if degree three is allowed, even with a+b≠0.

**Cubic, five primitive rows.** The full previous classifications are unchanged for arbitrary projective [a:b]. When b=0 both j(t) and j(u) vanish, so the homogeneous cubic theorem in [UNGUARDED-PORTS.md](UNGUARDED-PORTS.md) forces P=0 for any κ. When a=0 there are no bare noncoprimality exceptions and no full degree-five mesh exceptions.

To see the latter claim, set W=F. Its two roots have j(t),j(u) nonzero, by the integer pencil identity UF+Vj=5. The original contrast is H(Y)=−j(t)F(tY), still a nonzero multiple of the actual pencil at tY, even though its degree is five rather than six. The original A gate vanishes because F(t)=F(u)=0; the C gate follows by cross-multiplying the two high primitive rows against j(t),j(u). If F and P had a common factor, q=Res_Y(H,P_z;6,3) would vanish even at this degree drop. Thus R,A,C,T,U and the same two original integer indices give exactly the necessity from [CUBIC-BARE-GLOBAL.md](CUBIC-BARE-GLOBAL.md). Every candidate t in its entire integer support, however, has F(t) a unit. Consequently F and P are coprime over every field in the theorem in this boundary chart.

If (XF)T=NP, 0≠N and deg N≤5, bare coprimality forces F|N, so N is a nonzero constant multiple of the exact degree-five F. Cancel F to get P(0)=0. The cubic mask forces z=4/5. The remaining necessary equations are f=F(t)=0, g=5⁵F(4t/5)=0, and h=78125(D·j(4t/5)+z³N₀·j(t))=0, where D,N₀ are the original cubic mask scalars at z=4/5. The two ordered integer Sylvester resultants are

    Res(f,g)=4171045098189220973568,
    Res(f,h)=−1090571191482582559273376244326989824,
    gcd=2^10·3^4·7^5·11^2·181.

At the sole possible characteristic p=181, the polynomial gcds are t+100 and t+80, respectively. The first demands t=81, the second t=101, so no common t exists, even over an algebraic closure. This resolves that boundary without an unverified reduction in large characteristic.

**True factorization with three primitive rows, even if the quotient falls below degree four.** For a≠0 the full all-b classification is [UNGUARDED-PORTS.md](UNGUARDED-PORTS.md). For a=0 a **single further characteristic** gives an admissible normalized three-row factorization F=(X−t)(X−u)R, now with degree R=3. Over every field of characteristic 2662133 there is exactly one, already in the prime field:

    z=686626,   t=1200902,   u=1461232,   κ=1288066,
    R=2425131+474070X+2661935X²+132X³.

It has t+u=1, R(t)=2413436=−R(u), and all three amplitudes R(0),R(t),R(u) nonzero. There is no a=0 solution in any other allowed characteristic. If degree exactly four is required, this last fixture is absent by definition. For a chart with a+b≠0, nonzero amplitude, or exact degree conditions, use only the rows of the classification those conditions admit.

For the proof, the same original M,A,B integer projection is necessary: H=−j(t)F(tY) has the two prescribed roots, so M=0 and its normalized quartic quotient, up to the nonzero scalar −j(t), is just the actual R(tY), now of degree ≤3. The first low primitive gives A=0. Both F(t) and F(u) vanish, so the cross-multiplied B is automatically zero; it is only a necessary equation in this chart. The original complete two-index sieve therefore restricts to the same eight integer components as before. One has t=u; all but two of the others force F(t) a unit. On m=43 and m=104295260060968696963648183, F(t)=F(u)=0 and j(t) is a unit; exact monic division determines R and the first high integral fixes κ. The residual gap I₂(u)−tI₁(u)−κu j(u) is 8 mod 43, and 75175013869218993358871349 mod the second m. Its gcd with the latter m is the trial-division prime 2662133. This proves both exclusion and sufficiency: the remaining unique candidate has its literal factorization and all three primitive equalities after reduction. No extension-field solutions are missed because both successive monic gcds in the sieve are linear on these two components.

## Joint integer support and replay

The two original unstrengthened cubic and quartic signed integer indices have exact gcd

    2^2854 · 3^1522 · 5^960 · 7^333 · 11^730 · 13^144.

Thus they cannot both vanish in any characteristic p>13, irrespective of guards. This does not exclude a branch requiring just one of the two obstructions.

From this directory:

    sha256sum -c --quiet PROJECTIVE-CERTIFICATE.sha256
    python3 -E -B verify_indices.py inputs .
    python3 -E -B verify_cubic_bare_global.py inputs .
    python3 -E -B verify_quartic_global.py inputs .
    python3 -E -B quartic_symmetry.py .
    python3 -E -B verify_joint_support.py .
    python3 -E -B verify_unguarded_ports.py inputs .
    python3 -E -B verify_projective_ports.py inputs .

These checks require only Python's standard library. The first three reuse the original exact determinant/CRT computations and regenerate the previously published witnesses byte-for-byte. The rest check the ground-field symmetry, integer separation, unguarded profiles, and pure boundary charts by literal field/ring arithmetic and exact gcds. The manifest pins both the new addendum and unchanged data/source it reuses.
