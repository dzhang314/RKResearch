# A two-ended obstruction at the eight-stage strict SDIRK7 floor

There is no eight-stage strict SDIRK tableau of order at least seven over the **prime field F19**. Alongside the [separate Lean-checked nine-stage tableau](../strict-sdirk7-nine-f19/README.md), this gives the exact minimum nine there. The proof covers every weight mask and repeated clocks. Therefore the stage minimum at order seven is **at least nine over Z[1/5040]**, or any nontrivial commutative ring admitting a unital map to F19. The underlying paid nonsingular stage floor is eight and a unit common diagonal survives the map. The separate ten-stage paid-ring construction gives **[9,10] over Z[1/5040]**. No claim is made for all rings with 5040 a unit, for extensions of F19, or for rational tableaux with bad reduction at 19. The unrestricted rational and ordered-field floor remains eight. The result combines a mathematical tableau-to-profile proof and a kernel-checked finite arithmetic gate; scope below.

## 1. Genuine chronological border profiles

Use one-based indices in the prose. Normalize an eight-stage strict tableau by the reciprocal z of its common diagonal. Denote the normalized matrix by B, its physical clock by x=B1, the output row by b, the diagonal clock multiplication by C, and the strict lower matrix by N=B−I. The scalar interval [0,z] denotes the algebraic functional I_z(X^j)=z^j/(j+1), not analytic integration over a finite field.

The midpoint ranks are E=(1,2,4,6,7,8,8) and F=(0,0,1,2,4,6,7), with F_(j+2)=R E_j for R=CB−BC−B². Exact D(1) is bB=b(zI−C); the last two weights are nonzero, their clocks distinct, and x_8=z−1. These statements hold even with zero weights. The seed g=−R1=2Bx−x² lies in F_2; the five genuine first-seed moments b C^j g=0, j=0,...,4, are paid.

At the front u=B_21=x_2−1≠0: a zero tap would clone the first two rows on all trees despite E_5 being full. The first two coordinates of g and Ng are (1,κ(u)) and (0,u), where κ(u)=1+2u−u², so they span F_3 and its first two coordinates are injective. Consequently (C−I)g=κ(u)Ng. Also [B,R]1 is cubic-pure with first two components zero, since the commutator is between two strict lower matrices after removing constant diagonals. Thus [B,R]1=0. Writing w=x_3−1 and r=B_32 yields the literal third-row equations

    r u (2u−w)=0,
    w (κ(w)+2 r u)=κ(u)(w+r(κ(u)−1)),
    g_3=κ(w)+2 r u.

If r=0, w cannot be 0 or u: in either case its single-parent row clones a prior stage. Cancelling w(w−u) in the remaining clock equation gives w=2−u, u≠1,2, and g_3=κ(u). If r≠0, w=2u and d(u)r=2u(3u−2), where d(u)=−2+u+4u²−u³. The zero d case would force u=2/3 at which d=4/27, nonzero. These are the two branches, including over F19.

## 2. Physical reflection with possible zeros

In F19, 2 is nonsquare and y³−9y²+18y−6 has no root. The earlier ghost-rank theorem makes all F_3 hidden on zero weights when any ghost occurs and sqrt(2) is absent. Thus b_1=b_2=0. If b_3≠0, stage 3 has no cubic defect and the literal row identity would give the displayed impossible cubic at y=x_3. The only masks are all-active or b_1=b_2=b_3=0.

The last three weights are nonzero in either mask: otherwise there would be at most four nonzero weights. F19 uniform quadrature through degree six needs at least five active clocks. To prove this, pad to four clock sites and observe that their monic nodal quartic is orthogonal to 1,X,X² and so lies in the span of the shifted Legendre cubic and quartic. No direction of this pencil splits over F19, by the independent projective residue certificate in the prior signs package. The checker here also exhausts all subsets of one through four sites by direct moments of the nodal product and its paid monomial multiples.

Form the weighted transpose only on the final three physical coordinates and reverse their chronology. This is legitimate because these weights are nonzero. Its row sums are y_i=z−x_(9−i) by D(1), and its diagonal is one. Z_3=Ann(E_3) has rank two and contains bR and bCR; they are independent on the last two coordinates by the distinct clocks, two nonzero weights, and triangular invertibility of R there. Also (bR)B, (bR)C, and (bB)R belong to Z_3 by the one-grade advances and D(1). Then b[B,R]=0 because it vanishes on the last two coordinates. The reflected local R is the weighted transpose of R, since the clock is reflected as well; b[B,R]=0 is precisely the local reversed [B,R] equality on 1. The reflected seed on the three coordinates is −(bR)_i/b_i, by D(1). The two rows (bR)(zI−C−I) and (bR)(B−I) are in Z_3 and vanish on the last coordinate. Their proportionality, with ratio determined by the penultimate component, is the reversed seed/tap identity. Hence the same two chronological branches apply at the rear, with spacing v. If a zero rear middle tap gave a repeated clock at its third coordinate, it would clone a prior coordinate on every reflected scalar clock/integration word. This contradicts the full reverse dual census, since the eight rows b C^{0,1}, b C^{0,1,2,3}R, b C^{0,1}R² are independent by paid Hilbert separation and invertible R. All word comparisons here use only that local three-coordinate restriction; no full weighted transpose is claimed when an earlier weight is zero.

The weighted vector b∘g annihilates E_4 by paid products. This annihilator is spanned by bR, nonzero at the last stage, so comparing last components gives g on the last three stages as the reflected local seed multiplied by σ=g_8; this includes σ=0. The clock and seed vectors necessarily have form

    x = [1,1+u,1+w_u, a,b0, z−1−w_v,z−1−v,z−1],
    g = [1,κ(u),G_u,g_4,g_5, σ G_v,σ κ(v),σ].

Here a,b0 are the middle clocks and w_u,G_u,w_v,G_v are the border prescriptions, not assumed generic.

## 3. Four causal cancellations

Each end admits a degree-two lift clearing its own first three coordinates. In the zero-tap branch take N²1 at the front and bN² at the rear. Their scalar profiles in their respective time variables are H=L_2=1−2X+X²/2. In the nonzero-tap branch the front uses

    −d(u)N²1 + (3u−2)(C−I)(C−(1+u)I)1.

It clears the first two coordinates termwise and the third by d(u)r=2u(3u−2). The reverse row is the same expression on b with reflected clock and v, and clears the last three by the just-proved local normalization. Both profiles have form

    H_u(X)=u²(u−1)−u(u−2)(2u−1)X+((u−2)(u−1)²/2)X².

Let H,K be the two cleared profiles, and F=(J−I)H, G=(J−I)K, with primitive J from the respective origin. Advancing the front lift by N or by C−aI clears the first four. Advancing the rear row on the right by N or by C−b0 I clears the last four. All four pairings vanish on the eight physical coordinates by disjoint supports. Their operator words cost exactly at most six, so the reviewed operator-word expectation theorem evaluates them from order seven. The scalar profile of a right integration is the primitive in reflected time, by polynomial Fubini, equivalently the beta factorial identity on monomials. Write

    <P,Q>_j = I_z(X^j P(X)Q(z−X)),
    T=<H,G>_0=<F,K>_0,
    L=<H,G>_1, M=<F,K>_1, S_j=<H,K>_j.

Then the four vanishing conditions are

    <F,G>_0=0,  L=a T,  M=b0 T,
    S_2−(a+b0)S_1+a b0 S_0=0.

The equality of the two expressions for T is the same polynomial Fubini relation. This proof does not divide by T or assume regular center clocks. The word evaluations and adaptations of the physical border chart to the finite gate are mathematical parts of this proof, not asserted as a new kernel-level wrapper.

## 4. Exact finite exhaustion

The generator takes all nonzero z,u,v and both branches at both ends, including singular possibilities. There are 33 raw local third-row charts at each end. If <F,G>_0=0 and T=0, at least one of L,M is nonzero in every admitted F19 instance. Thus the only middle clocks possibly allowed are a=L/T, b0=M/T. The fourth causal equation leaves 150 clock profiles, repeated nodes permitted.

- 72 profiles cannot even carry quadrature: an explicit degree-at-most-six polynomial vanishes at all proposed clocks but has nonzero required uniform mean.
- For each of the remaining 78, a specified free weight and seven explicit polynomial selectors determine the other seven weights. All 19 free values are audited. None has its first three weights zero, and there are 1014 all-active choices.
- For each all-active choice the five first-seed moments give a linear system in g_4,g_5,σ. An explicit dual row annihilates the unknown columns and takes value one on the known head column, making that system inconsistent. No nonlinear conditions beyond the formation of the border charts are needed.

The generator uses modular row reduction, but all its receipts are checked independently. The separate checker enumerates raw third rows, integrates scalar words directly, reconstructs weights by Lagrange interpolation, and tests nonzero 4×4 minors instead of using the generator's row reduction. Both computations are exact.

## 5. Separate characteristic-zero consequences

Both near-edge middle taps cannot be zero over any characteristic-zero field, including zero weights. Indeed N²1,bN² then clear the respective three ends without any weight inverse, and the four causal equations with H=K=L_2 apply even if a rear weight vanished. The first gives

    Q(z)=z^6−42z^5+630z^4−4200z^3+12600z²−15120z+5040=0.

Multiply the last equation by T² and substitute L=aT, M=b0T. After clearing fixed denominators and canceling the known nonzero z², the resulting numerator reduces modulo Q to a nonzero scalar times

    R(z)=1639z^5−39460z^4+322200z³−1068000z²+1344600z−456480.

Their resultant is 2^25 3^8 5^10 · 2843, nonzero in characteristic zero.

Over the rationals, either single zero near-edge tap is impossible as well. The same eliminated two equations for H=L_2,K=H_v have a z-resultant with factors z^24, three quartics of respective multiplicities 1,2,3, and one degree-thirty factor. Each non-z factor has no projective root modulo 43 (leading coefficients audited as well as all affine residues), hence no rational root. The reverse orientation is symmetric. The exact SymPy replay verifies these facts. They are subchart exclusions, not a new global rational floor.

The all-active rational midpoint must also have at least six distinct raw clocks. With five clocks, the old rational quadrature floor implies all five aggregate clock masses nonzero. Vandermonde forces the separate grouped first-seed masses to vanish. Dirty groups need at least two stages, so at most three dirty groups fit in eight stages with five clocks. Their square-seed masses therefore also vanish individually by the three paid square-seed moments. With two stages, eliminating the two seed values from the first- and second-mass equations forces them zero when the total weight is nonzero. Hence each dirty group requires at least three stages. The first two chronological clocks are distinct and both dirty (2 is not a rational square), so there must be six stages at those clocks and at least three for the others, a contradiction.

In an all-active ordered-field chart with κ(u)≠0, the exactly two negative weights have distinct clocks and nonzero seeds. Restriction of F_3=span(g,Cg) to those two coordinates is injective, since a pure vector vanishing there has a paid square with nonnegative terms. This does not locate the two negative weights in fixed chronology.

## Replay and kernel scope

Lean modules SDIRKSevenEightStageF19Arithmetic, SDIRKSevenEightStageF19Receipts, and SDIRKSevenEightStageF19Verification prove the stated linear certificate interface and kernel-check all 150 explicit profile receipts. SDIRKSevenEightStageF19Prelude obtains the two weight masks, actual quadrature, and the five actual first-seed moments directly from reviewed HasOrder. SDIRKSevenEightStageF19Gate packages these into the native theorem RKResearch.Certified.SDIRKSeven.F19.no_reviewed_order_with_receipted_chart, which takes the literal border clock/seed formulas, the two middle-clock identities, nonzero T, and membership in the certified receipt list as explicit hypotheses.

The complete coverage of the finite chart space and the absence of the T=0 case are independently replayed by the exact Python check. They are not claimed to be normalized by the Lean kernel. The mathematical border/reflection/crossover derivations and ring-reduction proof are Sections 1–3 above, not an already kernel-checked unconditional F19 or paid-ring wrapper.

Run python3 check-f19.py for the independent standard-library checker. Run python3 generate-f19-receipts.py to regenerate the Lean tables. The optional exact rational-resultant replay python3 check-chronological-resultants.py uses SymPy. For manual Lean compilation, build Arithmetic, Receipts, and Verification in order, then Prelude (which reuses the frozen signs package) and Gate. No code edits outside ai-generated are required.
