# Shared exclusion of sole nonliteral transport at sixth or seventh

This closes both indicated strictly scoped charts at the ten-stage strict SDIRK8 floor over a characteristic-zero field. The first physically weight-zero stage is the only nonzero quadratic-defect stage; the cubic defect is detected; there are seven distinct ordinarily active clocks; \(k\ne0\); and the nonconstant affine active profile is coprime to \(L_4\). One literal front is ordinary and the other literal is silent. The sole actual separate nonliteral reverse contributor is physical sixth **or** physical seventh. Actual fourth, fifth, eighth, ninth, and terminal stages are ordinary active. Both star and arithmetic **active** eighth endings are covered. This does not cover a silent eighth or move the unrestricted **10–11** bound.

In particular physical fifth \(y\) is **ordinary active**, not a virtual reverse observation. Its actual clock is distinct from the actual ordinary fourth \(s\). Use the same honest ordinary \(a,s\) anchors and padded pure-fifth polynomials \(E_T,E_A,D\) of the [sole-fifth proof](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fifth-star/README.md). In this chart all three are necessary at the actual ordinary fifth \(y\). The other literal silent clock \(b\) may equal \(s\) or \(y\); no \(s-b\) or \(y-b\) nonzero condition is imposed, and their literal interpolation identities do not require those differences.

## Eliminate the unknown nonliteral reverse clock

Denote the separate reverse site by \(z\); its physical sixth/seventh assignment is not needed in this common elimination. Write \(x=1-\gamma,c=x-\gamma u\) and \(q(X)=\gamma Q(X/\gamma)\). The same \(L_4,W_{L_4}\) paid Bézout argument gives the nodal equation at the five known ordinary pegs \(\gamma a,\gamma s,x,c,d\), not at \(z\).

For the active arithmetic eighth \(d=x-2\gamma u\), reuse the [exact root-eliminated ninth/eighth cross and five-peg carrier](../sdirk-eight-silent-one-seven-distinct-coprime-nonliteral-fifth-arithmetic/README.md). That carrier's two rear equations used only ordinary \(a,s,x,c,d\) and eliminated the location of the separate reverse site; they never used \(z=\gamma y\). Its construction and exact characteristic-zero guard factors therefore transfer to either of the actual sixth/seventh placements. Do **not** use that proof's subsequent homogeneous substitution for \(y=z/\gamma\) here.

For the active star eighth \(d=x-\gamma(2-u)\), put \(v=u-1,\ V=v^2,\ k=2-V,\ l=\gamma L_4(x)\). As in the preceding star proof, write the centered cubic quotient \((L_4(c)-kL_4(x))/u\) as \(p_0+p_2V+v(p_1+p_3V)\). With \(w=x-z,\ e=p_0+p_2V,\ o=p_1+p_3V\), the actual even and odd tail reads are
\[
 [q_x e+lk q_1]w+lk(q_x-\gamma q_1)=0,\qquad
 q_x o\,w-lk\gamma q_1=0 .
\]
Here \(q_x=q(x)\) and \(q_1\) is the nonzero physical affine slope. Cross them and cancel the genuine \(lk\ne0\), obtaining the equation affine in \(V\):
\[
 [q_x e+lkq_1]\gamma q_1+(q_x-\gamma q_1)q_x o=0 .
\]
The source verifies the corresponding five-peg nodal polynomial is even in \(v\), so it is cubic in \(V\). After exact true guards, their padded \(V\)-resultant \(B_\star(\gamma,s)\) has \((s,\gamma)\)-degree \((11,33)\). The divisions use only strict nonzero \(\gamma\), distinct ordinary \(a,s,x\), their nonzero ordinary \(L_4\) and \(q\) values, the true nonconstant coprime affine profile, and \(V\ne0,1,2\) from distinct star tail clocks and nonzero \(k\). In particular auxiliary homogeneous Gauss factors are nonzero in the actual coefficient field, not just a selected finite prime.

Combining either rear \(B\) with the literal front \(J(\gamma,s)\) gives the outer exact padded \(s\)-resultant. Its bound \((\deg_s J)\deg_\gamma B+(\deg_s B)\deg_\gamma J\) is attained by the entire reduction at \((1103,161)\). The exact degrees are **660/693** for star rear and **2300/2416** for arithmetic rear, in star/arithmetic literal fronts. No factor of those reduced diagonals is excluded by a modular guard. One actual \(s\)-leading coefficient is a unit in every diagonal field; at each common \(s\) factor one nominal true gap leading coefficient is a unit. This yields integral \(\gamma,s\), and gap; for star use the whole monic \(v^2-V\), retaining both reflected signs.

## Actual ordinary fifth

At each such gap, form the pole-free nodal polynomial \(D_5(Y)\) using the **four fixed** ordinary pegs \(\gamma a,x,c,d\) and the additional variable ordinary peg \(\gamma Y\). Exact nodal interpolation supplies \(D_5(s)=0\) and \(D_5(y)=0\), since both actual stages are ordinary and distinct from the other four. The five-peg carrier already enforces the first equality. Divide the polynomial by \(Y-s\) with remainder \(D_5(s)\); the quotient of degree at most two must vanish at the actual \(y\ne s\). This removes exactly the known actual fourth as a possible fifth, without treating the two distinct true clocks as distinct after reduction.

The padded pairwise resultants of the two true pure-four reads and the quotient, including the quotient against \(D\), all vanish at a genuine retained \((\gamma,s,u)\). They are integral scalar values even if \(y\) itself need not be integral. In every retained residue component they generate a unit. This contradiction closes both physical ending placements, without assigning the virtual sixth/seventh amplitude to the actual fifth, or requiring those virtual amplitudes to be nonzero.

The [native support](../../lean/RKCert/ReviewedNative/SDIRK8NonliteralSixSeven.lean) verifies the star reverse-site elimination and the actual ordinary fifth's nodal quotient implication on Lean/Mathlib 4.36.0. Concrete residues are checked at source level. Run `python3 check_nonliteral_six_seven.py` with `sympy==1.14.0` and `python-flint==0.9.0` in the sibling proof tree; it independently rebuilds and verifies all eight literal/rear cases, including the exact shared arithmetic projector. It makes no availability or exclusivity claim beyond both relevant actual physical sixth/seventh placements.
