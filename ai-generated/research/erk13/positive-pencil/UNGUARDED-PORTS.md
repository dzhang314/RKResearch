# What survives after dropping the extra quartic guards? Pure leakage never does.

Normalize a=1, write W=j+bF and J=Xj, and keep distinct nonzero ordered knots t,u. The integral/pencil inputs are as in [QUARTIC-GLOBAL.md](QUARTIC-GLOBAL.md). Instead of assuming b(b+1)R(0)R(t)R(u)≠0, allow **arbitrary b** and no value guards. Require only W=(X−t)(X−u)R and the three literal primitive equations with a single κ. In characteristic zero there is still no solution. In characteristic p>13 the previous complete quartic classification acquires just this one extra component:

    m=2551619843329 = 155773 · 16380373,
    t=568542283607,    u=1,    z=867363036929,    b=−1,
    R=1835664608774+2097292441940X+474800605300X²+899778513974X³+1716X⁴,
    κ=1822585602379.

Each of the two displayed primes is trial-division prime and has exactly one normalized ordered solution already over its prime field, with coefficients reduced from the display. There are no others. In particular, **b,κ,R(0),R(t),R(u) are automatically nonzero for every solution**, without assumptions on them. Among all the solutions R(t)=R(u) iff t+u=1 iff b=3; each holds exactly in the self-reflected ground characteristics p|3478762188949. For an unguarded genuine quartic profile, excluding u=1 suffices to recover the earlier terminal-guarded list.

**Necessity without b≠0.** From the factorization W(t)=W(u)=0, we have j(t)=−bF(t), j(u)=−bF(u). The original integral Bezout identity UF+Vj=5 shows F(t)≠0, even when b=0. The contrast H(Y)=F(t)j(tY)−j(t)F(tY) is now visibly F(t)W(tY). Its quotient by t²(Y−1)(Y−z) is F(t)R(tY), z=u/t. The two high moments can be cross-multiplied after substituting j(x)=−bF(x) at both knots: a term proportional to b occurs on both sides, and **b is not divided out**. Thus the old A=M=B=0 projection and both characteristic indices remain necessary without any of the five removed guards. The three excluded composite components in QUARTIC-GLOBAL have z=1 or F(t)=0 with j(t) a unit; each remains impossible for arbitrary b. The fourth previously rejected component really does have b=−1, u=1, with all three knot values nonzero; direct substitution proves the displayed fixture. On all five accepted components literal primitives and inverse-certified unit tests give the remaining conclusions. An equality vs a unit difference on each component proves the three-way equivalence in every residue field.

**Elementary cubic pure-leakage theorem.** Over characteristic zero or **any characteristic p>7**, the five homogeneous cubic moment rows

    I₁(t)=I₂(t)=I₃(t)=0,   I₂(u)−tI₁(u)=I₃(u)−tI₂(u)=0

force P=0 for degree ≤3. This stronger conclusion assumes neither pencil roots nor a mesh nor nonzero pivot amplitudes. The three low rows give the branch-free normal form P(tY)=γP_z(Y) from [CUBIC-ALL-FIELDS.md](CUBIC-ALL-FIELDS.md); only 2,3,5,7 are inverted. If P≠0, the two high rows force D=(5z−2)(7z−6)=0 and N=100z⁴−460z³+819z²−672z+210=0. But N(2/5)=1134/25 and N(6/7)=30/2401, both units in the stated field. Equivalently there is a one-line ring identity,

    (−2835400z³+10612140z²−14124306z+6945015)D+(992390z−396831)N=5670.

This identity works over every commutative ring in which 5670 is nonzero. In particular κ=0 is impossible for both true scalar profile types in characteristic zero or p>13, even without a mesh. Also, in the main cubic classification the assumption b≠0 can be dropped when a≠0: b=0 forces j(t)=j(u)=0 and hence both high rows are homogeneous whatever κ is. These results remain about the scalar ports, not complete tableaux.

Replay verify_indices.py, verify_quartic_global.py, then `python3 verify_unguarded_ports.py inputs .`. The addendum recomputes all eight monic-ring polynomial gcds with Bézout/quotient witnesses, rechecks the literal moments, factors the small extra component, and checks the cubic resultant and the two rational evaluations. No floating-point, factorization of a large component, or undisclosed extension search is used.
