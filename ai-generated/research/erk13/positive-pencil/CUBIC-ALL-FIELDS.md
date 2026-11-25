# The genuine cubic pencil/mesh gate holds in every characteristic above 13

**Theorem (scalar, not a stage bound).** Let K be a field of characteristic zero or of prime characteristic greater than 13. Use the original normalized j,F and J=Xj. Put G=X(aj+bF) with a,b nonzero; an assumption a+b≠0 is not needed. Let t,u be distinct nonzero roots of G. Let P be a polynomial over K of degree at most three, let N≠0 have degree at most five, and suppose G T=N P for some polynomial T. For Iₖ(x) the zero-constant primitive of XᵏP evaluated at x, suppose

    I₁(t)=I₂(t)=0,   I₂(u)−t I₁(u)=0,
    I₃(t)=κ J(t),     I₃(u)−t I₂(u)=κ J(u)

for a single κ in K. There is no such nonzero P with **both** P(t) and P(u) nonzero. These are the actual nonzero amplitudes of the two causal mismatches for the low-profile port. The amplitude guard is significant: F₂₃ furnishes a counterexample with P(u)=0 to the stronger characteristic-zero-only assertion that omitted it. The argument below does not forbid valid positive-characteristic tableaux as a whole.

## 1. The original first projection

Write z=u/t. The five literal primitive conditions and the two original roots imply, for P≠0,

    P(tY)=γ P_z(Y),    γ≠0,
    P_z=(12z−15z²)+(60z²−24z−18)Y−10(5z²+4z−6)Y²+15(4z−3)Y³.

This branch-free reduction uses only divisions by products of the primes 2,3,5,7; the scalar 4z−3 is not inverted. Indeed, after eliminating the two lowest moments the coefficient-kernel equation is Lc+Md=0 with L=3(4z−3), M=2(5z²+4z−6), and ((20z+31)/9)L−(8/3)M=1. The two high primitives remove the shared κ, yielding the original F and j gates. Set D=(5z−2)(7z−6), N₀=100z⁴−460z³+819z²−672z+210 and

    A=(D F(tz)+z³N₀F(t))/(z−1),
    C=(((D j(tz)+z³N₀j(t))/(z−1))+7A)/t.

These are integer polynomials with t-degrees ≤5; the displayed scalar divisions are legal at the actual point. The ordered fixed t-resultant of A,C equals the degree-50 primitive R multiplied by 168678816768 z¹⁵. Its content is 2¹⁰ 3⁴ 7⁵ 11², so R(z)=0 in all the asserted characteristics. Specifying R by this exact identity, the literal primitive coefficients are in `exact_cubic_outer.json`. The original integer identity U F+V j=5 forbids F(t)=j(t)=0; because a,b≠0 and t is a root, both F(t),j(t) are nonzero. Set H(Y)=F(t)j(tY)−j(t)F(tY). It is a nonzero multiple of the normalized pencil at tY, of degree exactly six.

Use the original projected index

    q_old=Res_Y(H,P_z;6,3),   U_old=Res_t(A,q_old;5,33),
    Δ_old=Res_z(R,U_old).

Here `Res` is the ordered Sylvester determinant with the indicated fixed sizes; any common finite root kills it even under a degree drop. The true mesh implies G divides NP. If the normalized pencil were coprime to P, its degree six would force N to have degree at least six. Thus H,P_z share a factor and Δ_old vanishes in K.

If P(0)=0, then z=4/5. Consequently the integer 5⁵⁰R(4/5) vanishes as well. Exact Bézout over the integers gives

    gcd(Δ_old, 5⁵⁰R(4/5)) = 2¹⁵ · 3 · 5²⁵ · 7.

This immediately excludes P(0)=0 over the fields in the theorem.

## 2. Paid nonzero amplitudes remove the two prescribed knots

Suppose P(0)≠0. Since G divides NP and deg N≤5 while deg G=7, its common divisor with P has degree at least two. Its known factor X is coprime to P. In the scaled variable, H has the two known distinct roots 1,z, neither a root of P_z because P(t)P(u)≠0. Hence the actual complementary quartic W obtained by dividing H by t²(Y−1)(Y−z) still shares a divisor of degree at least two with P_z.

One can compute W without any polynomial denominators, even away from the physical fiber. Write F_i,j_i for ordinary monomial coefficients and h_i=j_i F(t)−F_i j(t). For i=0,…,4 set

    w_i = Σ_{k=i+2}^6 t^(k−2) h_k · (1+z+⋯+z^(k−i−2)),    W=Σ_i w_i Y^i.

This is the quotient on the specified fiber, since monic division uses only the coefficients of H from Y² upward. It has bidegrees at most (10,4) in t,z. Introduce λ and define

    q₀=Res_Y(W,P_z;4,3),
    q₁=[λ] Res_Y(W,P_z+λ;4,3),
    U_i=Res_t(A,q_i;5,30),   Δ_i=Res_z(R,U_i),   i=0,1.

At the admitted point W has degree exactly four. Over an algebraic closure, the product formula gives the determinant with λ equal to lc(W)³ times the product of P_z(ρ)+λ over all four roots ρ of W counted with multiplicity. A common divisor of degree at least two gives two zero terms at λ=0, with multiplicities. Thus q₀=q₁=0, even at a repeated root and even if P_z loses its top coefficient. Since A(t,z)=R(z)=0, both Δ₀ and Δ₁ vanish.

The exact signed integer indices satisfy

    gcd(Δ_old,Δ₀,Δ₁)=2^5989 · 3^3982 · 5^2495 · 7^249 · 11^836 · 13^165.

In characteristic zero, any one of these nonzero integers gives the contradiction. In prime characteristic greater than 13 their simultaneous vanishing is impossible. This proves the result.

## Exact arithmetic replay

The portable verification scripts depend only on Python's standard library and the original published polynomial data/checker. The required original inputs are bundled in the inputs/ subdirectory. From this directory use RAW="$PWD/inputs" and HERE="$PWD":

    python3 verify_indices.py "$RAW" "$HERE"
    python3 verify_cubic_all_fields.py "$RAW" "$HERE"

The exact R reconstruction uses all 66 bounded integral interpolation knots. For q_old all 34×13 inner samples are ordinary fixed 9×9 Sylvester determinants, followed by all 259 exact outer samples. For W the independent audit uses the nonrecursive sum for w_i above, not the generation recurrence. It computes q₁ by summing the four ordinary diagonal cofactors in the 7×7 matrix, not by λ interpolation. Each marked q requires just 31×21 exact inner integral samples (t,z degree bounds 30,20), and each U is checked on all 281 outer integer knots (degree bound 30·6+5·20=280). The actual U degrees are 260 and 240.

Each large integer Δ is separately verified modulo thousands of distinct sieve-proved primes, using an independent finite-field Euclidean resultant. The modulus product exceeds twice the square root of the explicit squared Hadamard bound (sum-of-coefficient-squares for R raised to deg U times that for U raised to deg R). The claimed signed integers fall within that interval; CRT proves them exactly, including sign. The two final gcds are ordinary exact Euclid followed by division by the six displayed primes. `exact_index.py` and `strengthen_cubic.py` regenerate the data with an independent integer subresultant algorithm (SymPy); the verifier needs no SymPy. No native formalization or universal tableau conclusion is asserted here.
