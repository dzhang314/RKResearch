# Excluding sole genuinely nonliteral fourth transport

This closes the [finite genuinely nonliteral fourth chart](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fourth-finite/README.md) for both star and arithmetic rears. The setting is ten-stage strict SDIRK8 over a characteristic-zero field, sole first quadratic defect at a weight-zero stage, detected cubic defect, seven distinct ordinarily active clocks, nonzero reverse factor \(k\), and a nonconstant coprime affine profile. Exactly one literal front \(a\) is active; physical fourth is the only actual nonliteral separate reverse contributor at \(z=\gamma s\), so its individual actual \(h\) and pure reads really transport. Physical fifth and eighth are ordinarily active. No other physical silent placements and no global improvement to the **10–11** stage interval are claimed.

## Tighten before projecting

Start from the two-anchor \(Q,P\) and the actual fifth equations in the prior finite reduction. The literal \(H_4(s)\) is genuinely nonzero. In an arithmetic literal front, the source fifth \(\tau_4,Ah\) equations each have precisely one further exact factor \(H_4(s)\), and the fifth \(J(\gamma,s)\) has three such factors. Remove them exactly over \(\mathbb Q(t)\). The tightened \(J\) has \(s\)-degree 16 in star literal front and 17 in arithmetic literal front, and \(\gamma\)-degree 12. The actual pure-fifth roots are preserved. This is not a deletion of an entire diagonal where some fourth value happens to meet \(H_4=0\).

Write \(x=1-\gamma\), \(c=x-\gamma u\), \(d\) the actual eighth clock, \(L=L_4\), \(X_z=x-z\), \(U=q(x)X_z\), \(l=\gamma L(x)\). Both factors of \(U\) are true nonzero chronological guards. The ninth cross after its exact zero-gap factor is
\[
R(u)=U\,\frac{L(c)-kL(x)}u
 +l k\bigl(q(x)+q_1 X_z-\gamma q_1 u\bigr).
\]
Here \(q_1\) denotes the slope of the physical affine profile; the displayed fraction is an exact polynomial. For star rear, center at \(v=u-1\), set \(V=v^2\) and write the indicated cubic quotient as \(p_0+p_2V+v(p_1+p_3V)\). Put \(b_0=q(x)+q_1X_z-\gamma q_1,\ b_1=-\gamma q_1\). The two actual reflected equalities give
\[
U(p_0+p_2V)+l(2-V)b_0=0,\qquad
U(p_1+p_3V)+l(2-V)b_1=0.
\]
Their affine determinant has the exact factor \(U\). After removing it, the necessary cross is
\[
U(p_0p_3-p_2p_1) + l\{b_0(2p_3+p_1)-b_1(p_0+2p_2)\}=0 .
\]
This is the [native guarded cross](../../lean/RKCert/ReviewedNative/SDIRK8FourthRearSaturation.lean). It never divides by an unknown centered slope; exact remaining guards give a tightened \(K(\gamma,s)\) of \((s,\gamma)\)-degree \((4,13)\).

For arithmetic rear, the actual eighth condition \(S\), after its exact zero-gap factor, has nominal \(u\)-degree six. Its top coefficient is \(-16\) times the top of the nominal cubic \(R\). Replace \(S\) by \(S+16u^3R\), which is nominally quintic; if \(R_j\) is the coefficient of \(u^j\) in the raw normalized ninth cross, the new raw quintic lead is \(8R_2+64R_3\). The actual root is preserved in every lower-degree branch. After taking the padded \(u\)-resultant, two factors each of the source-normalized \(q(x)\) and \(x-z\) are verified and removed exactly, along with true diagonal factors. The resulting tightened \(K\) has \((s,\gamma)\)-degree \((24,65)\). All source divisions are multiplied back in the quadratic coefficient field. No residue failure is used to assert an exact contact.

## Exact diagonal and locally monic residues

The padded scalar \(\operatorname{Res}_s(J,K)\) has nominal degree at most \(m\deg_\gamma K+n\deg_\gamma J\), where \(m=\deg_s J,n=\deg_s K\). The checker reconstructs it exactly. Clear each input separately into \(\mathbb Z[\sqrt2]\); the sum of absolute rational coordinates plus twice the absolute irrational coordinates is submultiplicative. The bound \((m+n)!\,\lVert J'\rVert^n\lVert K'\rVert^m\) then certifies both reconstructed coordinates once the split-prime CRT product exceeds twice the bound. Independently compare the entire degree-preserving reduction at \((1103,161)\). The exact degrees are **256/269** (star rear) and **1328/1393** (arithmetic rear), respectively for star/arithmetic literal fronts.

Every root of the whole tightened diagonal is retained in the residue replay. Its monic normalization is integral at the chosen split prime. At each reduced diagonal factor at least one actual \(s\)-equation has nonzero nominal leading coefficient; use it as the local monic carrier, and impose both \(J=K=0\). At each resulting \(s\) root, the star branch has at least one surviving actual affine slope, so \(V\) and then \(v\) are integral (the latter by \(v^2-V\)). In the arithmetic branch at least one of the cubic or tightened quintic has surviving nominal lead, and impose both actual gap equations. These checks license \(s,u\) reduction without assuming that an arbitrary exact nonzero guard stays nonzero. No residue clock coincidence is discarded.

At each remaining component, the needed fifths share the two actual pure-four equations and the pole-free nodal moment gate. Its five ordinary pegs are \(\gamma a,x,c,d,\gamma y\), **not** the transported fourth. Therefore all three pairwise padded resultants must vanish, whether or not \(y\) is itself integral. Their coefficient values depend only on integral \(\gamma,s,u\). A checked unit in the finite residual ideal contradicts a true fifth in every retained component. This eliminates all eight literal/rear orientations. Their arithmetic is exact source-level; the guarded cross identity is Lean/Mathlib 4.36.0 kernel-checked.

Run `python3 check_nonliteral_fourth_closed.py` from the sibling proof tree, using `sympy==1.14.0` and `python-flint==0.9.0`. It needs the finite fourth packet, the earlier no-front degree/nodal and closed-fiber helpers, and no precomputed coefficients. Other one-active-literal genuinely nonliteral placements (five through eight) remain outside the proof.
