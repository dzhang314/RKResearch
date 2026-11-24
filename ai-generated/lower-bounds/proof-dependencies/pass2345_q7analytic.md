# Certificate-free order 14; lighter order 15

## Result

The audited real explicit order-14 bound s≥21 can be made entirely computation-free. In the earlier p15 proof the entire order-15 alias certificate (60 arithmetic residues) can be removed; the order-15 no-alias parameterized pencil certificate is not removed here. This is an algebraic replacement of fixed-factor tests, not a new numerical bound. The rest of the proof is the same as in pass2313_q7_complete.md, based on the computation-free §§1–3 of the orders 16–19 proof and the elementary baseline. No order-15 all-cases claim.

## Centered polynomial and internal endpoints

Let y=2x−1 and H(y)=429 y^6−495 y^4+135 y²−5. The ordinary Legendre polynomial of degree seven is (429y^7−693y^5+315y^3−35y)/16, so H is its derivative multiplied by 16/7. Its roots all lie strictly between −1 and 1 and are distinct and nonzero, by the usual Rolle interlacing of Legendre roots. Thus the corresponding six shifted roots lie in (0,1). H is Eisenstein at 5, hence the Galois group of the splitting field acts transitively on its six roots.

Whenever the causal endpoint u is one of these six shifted roots omitted from a monic selected factor P, the moment I=∫₀ᵘ xP(x) dx cannot vanish. It is a rational polynomial expression in the root u and coefficients of P. If zero, apply an automorphism sending u to the least shifted root. The conjugated P remains a product of distinct other roots; its nonzero sign is constant on the interval from zero to that least root, as is the sign of x. The conjugated integral cannot be zero. This removes every internal m=6 root case at p14, and also all the p15 alias cases (which have an omitted-root u and a cubic P). No order-15 no-alias parameterized pencil root is covered by this fixed irreducibility argument.

## Order-14 endpoint u=1

Let F be the splitting field of H. Write the three positive squared centered roots as z_1,z_2,z_3. Their cubic C(Z)=429Z³−495Z²+135Z−5 is Eisenstein at 5; its discriminant is 2^12·3^5·5²·11 by the cubic discriminant formula. Its splitting field K therefore has group S3 and unique quadratic subfield Q(√33). Also z_1 z_2 z_3=5/429. The element T=√z_1√z_2√z_3 of F does not belong to K, since the square class of 5/429 differs from 33 (the 5-adic valuation is odd, for example).

The subgroup Gal(F/K) acts by sign flips on the three pairs. Because T is not fixed, there is an odd sign vector. This subgroup is stable under the permutations of the three pairs induced by Gal(F/Q)→Gal(K/Q)=S3 (restriction is onto for splitting fields). An odd vector is either (1,1,1) or flips a single pair, in which case conjugation yields all three coordinate flips and their product is the simultaneous sign flip. Thus simultaneous reflection y↦−y of all centered roots occurs as a Galois automorphism.

Let the monic centered quartic selected factor be P_c(y)=y⁴+s y³+v y²+w y+d, where the omitted pair has monic product y²−s y+t. Comparing coefficients in the product with H/429 gives, writing d4=−495/429 and d2=135/429,
    v=d4+s²−t,   w=s(v−t),   d=d2+s²(v−t)−t v.
The claimed zero integral at u=1 is equivalent to ∫_{−1}¹ (1+y)P_c(y) dy=0, by shifting and an overall nonzero constant. Its Galois conjugate under simultaneous reflection is ∫_{−1}¹ (1+y)P_c(−y)dy=0, which by substitution is ∫_{−1}¹ (1−y)P_c(y)dy=0. Thus its even and odd parts require
    1/5+v/3+d=0,       s/5+w/3=0.

If s=0, the omitted roots are an opposite pair, so t=−z_i has degree three over Q. Substituting v=d4−t and d=d2−t(d4−t) into the first equation gives a rational polynomial in t of degree exactly two (leading coefficient +1), impossible.

If s≠0, the second equation gives v=t−3/5, so s²=2t−3/5−d4. Substituting these into the first equation, using d=d2−(3/5)s²−t(t−3/5), gives a rational polynomial in t of degree exactly two (leading coefficient −1). But the omitted roots come from distinct opposite pairs, and t²=z_i z_j=(5/429)/z_k has degree three, so t has degree at least three. Again impossible.

This disposes of the only remaining order-14 integral certificate, so together with the proof already audited except for that substituted check, all p=14 branches are excluded without computer checks. The same argument establishes absence of the previously listed p15 alias obstruction without using its split-prime computation. The remaining p15 no-alias pencil has a variable coefficient and is outside this proof.

A still shorter mixed-pair check: v−t=d4+s²−2t=d4+a²+b²=−z_k, where a,b are the two omitted centered roots and z_k is the unrepresented squared root. Thus the odd moment alone forces z_k=3/5 if s≠0, contradicting irreducibility of the cubic. For s=0, the two remaining squared roots sum Σ−z_i and product Π/z_i, where Σ=495/429 and Π=5/429. Multiplying the even moment by z_i gives z_i²/3+(1/5−Σ/3)z_i+Π=0, again contradicting the same cubic.

## Independent q6 observation: localized backward L2, first-ordering subcase only

In the backward `ℓ1=0` case let N be the reversed transpose of A, let Y be the reversed diagonal X=I−C and v the reversed output weights. Thus Nv=Yv; the anchor at the first stage has Y=0 and v nonzero. At equality dim L2,L3,L4,L5=1,2,3,4 (all are now viewed as columns). Suppose L2 is Y-invariant, so d=NYv−Y²v/2 is supported on one node a, necessarily nonzero: the first nonzero Y_i v_i has no preceding nonzero Yv, so gives a nonzero d there. Rescale N,Y by a and d by a², so a=1. The following excludes the ordering in which a second independent feature (v_i,d_i) at node 1 occurs before the first off-stage nonzero Y_i v_i with Y_i∉{0,1}. It does not establish the assertion for the other ordering.

Let that first independent local feature at 1 occur at row r. Before r, all nonzero v lie at 0 or 1, and every earlier local d_i=−v_i/2 at 1. Consequently g:=Nd has g_r=−(d_r+v_r/2)/2≠0. Since g also vanishes at the first row with nonzero d, g is independent of d. Comparing d,g to ℓ3:=NY²v−Y³v/3 at these two rows gives `ℓ3=(2/3)(d−g)`. Until the first off-node y with yv_y≠0, this identity and NY²v=NYv show g=−d/2−v/4 at node 1 and g=0 off it, including ghost stages with v=0 at arbitrary nodes. The order implies that an off-node y must occur.

Strong Hermite amplification rules out Y-invariance of L3 and L4 (it would increase dimension by at least two on the following grade). Thus L4 is span(d,g,Yg) and L5 is span(d,g,Yg,Y²g). Ng is zero through row r, since g vanishes before r. The resulting expression of Ng in L4 has zero d component from the first nonzero d row, and its affine coefficient on g vanishes at the node of r. Thus Ng=k(Y−I)g. At y, NYv=y²v/2 and NY²v=NYv imply g_y=y²(2y−3)v_y/4, while Ng_y=−g_y/2−y²v_y/8=−y²(y−1)v_y/4. Thus y≠3/2 and k=1/(3−2y). Likewise comparing ℓ4:=NY³v−Y⁴v/4 on the first nonzero d row, on row r, and at y gives
    ℓ4=d/2+[−1+k(y−1)(Y−I)]g.
At row r the comparison is valid because NY³v=NYv, and ℓ4=(d+v/4) at node 1, agreeing with d/2−g.

Induct after the first y, maintaining g=−d/2−v/4 on node 1, g=γv on node y with γ=y²(2y−3)/4, and g=d=0 and Yv=0 elsewhere. At a new row x write S1,Sy for incoming weighted v sums at nodes 1,y. The known identities are
    S1+y Sy=x²v/2+d,
    S1+y² Sy=x³v/3+(2/3)(d−g),
    S1+y³ Sy=x⁴v/4+d/2+[−1+k(y−1)(x−1)]g,
    −g/2−S1/4+γ Sy=k(x−1)g.
At x≠1, d=0. Eliminating S1 and taking the augmented determinant of the last three equations for g,Sy gives a nonzero constant times
    (x−1)[−2d y²+4d y+3v x²(x−y)²].
Thus no new nonzero v at nodes x∉{0,1,y}. The 2×2 minors of the coefficient matrix from the first pair and first/third pair are, up to a common nonzero factor,
    3xy−3x−4y²+5y,       3x−2y²+y .
They only vanish simultaneously at x=y=2 (solve the second, then substitute into the first and use y∉{0,1,3/2}). At all other rows the known induction values satisfy the equations with Sy=0, including arbitrary ghost nodes, and are unique.

For x=y=2, use NYg−Ng∈L5. This vector has zero d component by the first nonzero d row, and its quadratic coefficient on g vanishes at node 1 (evaluate at row r, where all earlier g vanish) and at the first y (all earlier nonzero g supported at node 1). Therefore NYg−Ng vanishes at a repeat of y; its left-hand side by the induction hypothesis equals (y−1)γ Sy=Sy, so Sy=0. The second equation now gives g=γv and closes induction. The method would have at most three active Y nodes, impossible for scalar quadrature exact to degree at least 11 (use square of their cubic vanishing polynomial). If instead the first off-node y precedes r, κ in ℓ3=(2/3)d+κg is −2+4y/3, not generally −2/3; the proof above cannot be applied then. No unconditional q6 numerical result claimed.
