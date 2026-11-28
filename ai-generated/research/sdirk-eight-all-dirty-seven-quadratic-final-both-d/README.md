# An all-dirty seven-clock strict SDIRK8 tableau must have a singleton endpoint

Let the coefficient field have characteristic zero. Suppose a strict ten-stage SDIRK tableau has ordinary order at least eight, its ten physical quadratic defects are all nonzero, and it has exactly seven distinct physical clocks. Then **at least one of its two physical endpoint clock labels is a singleton**. Neither the signs of the weights nor the existence of an ordering on the field matter. This is not a general ten-stage exclusion: singleton-ended seven-clock tableaux and the surviving higher clock counts are not covered, and the general 10–11 interval is unchanged.

## Exhaustion of the doubled-endpoint census

Here D denotes a clock with two physical occurrences, and S a singleton clock. The [all-dirty census](../sdirk-eight-all-dirty-clock-census/README.md) gives three D labels and four S labels. The [constant](../sdirk-eight-all-dirty-seven-constant/README.md) and [affine](../sdirk-eight-all-dirty-seven-affine-final/README.md) results force a genuinely quadratic graph. If both endpoint labels are D, their equality is [impossible](../sdirk-eight-all-dirty-seven-quadratic-no-shared-end/README.md). With distinct endpoints, an opening with two additional D rows is [excluded](../sdirk-eight-all-dirty-seven-quadratic-midpoint-vs-arithmetic/README.md); so are the cases of [one additional D at both ends](../sdirk-eight-all-dirty-seven-quadratic-distinct-one-extra-d/README.md) and [one additional D at just one end](../sdirk-eight-all-dirty-seven-quadratic-distinct-mixed/README.md). The [two D,S,S opening result](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) eliminates a star at either end of that final pair. It remains only to exclude genuine D,S,S arithmetic at both ends with distinct endpoint labels. The two observed pairs of S rows consume all four S rows, so in particular the actual fourth row is D.

## Common scalar data and chronology

Normalize the actual diagonal to one, the interval length to \(\ell=1/\gamma=2m\), and write \(h=m-1\) and \(t=x-m\). The D labels are \(-h,h,d\), with physical first and last at \(-h,h\); \(h\ne0\). By [odd projection and graph shape](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md), write
\[
 L_4=t^4-a t^2+b_0,\quad a=6m^2/7,\quad b_0=3m^4/35,\qquad
 Q/B=L_3-\mu tL_4,\quad L_3=t^3-3m^2t/5,\quad
 \mu=(h^2-3m^2/5)/L_4(h)\ne0.
\]
The common singleton graph is \(R=rW\), \(r\ne0\), with monic \(W\) one of:
\[
 \begin{array}{lll}
 \text{even:}&d=0,\quad W=t^2-S,&
 S=(21m^2h^2-15m^4)/(35h^2-21m^2),\\
 \text{split:}&d\ne0,\quad W=t(t+d),\quad d\ne\pm h,&d^2=S.
 \end{array}
\]
The Hermite case \(S=0\) and any allowed D/graph coincidence in the even branch are retained. The coupling polynomial is \(C=A_2+BR\). The four original S labels and the known normalized forward and reverse residues are obtained from the *literal* first three rows of the actual forward and weighted-reflected tableau, not from arbitrary row swaps. For the two gaps \(u,v\), set
\[
 s_1=u-h,\quad s_2=2u-h,\quad s_3=h-v,\quad s_4=h-2v,\qquad
 \kappa(z)=1+2z-z^2,\quad D(z)=-2+z+4z^2-z^3,\quad
 N(z)=(1+4z-4z^2)D(z)+4z^2(3z-2).
\]
The four S values are \(g(s_1)=\kappa(u)/2,\;g(s_2)=N(u)/(2D(u)),\;g(s_3)=\lambda\kappa(v)/2,\;g(s_4)=\lambda N(v)/(2D(v))\), where \(\lambda\ne0\) converts the normalized reverse defects to the original scale. The observed D values are \(g_1=1/2\), \(g_{10}=\lambda/2\). All seven labels are distinct. The literal nonzero guards are \(z,\kappa(z),D(z),N(z),3z-2\) for \(z=u,v\). They are the true nonzero-third-tap arithmetic guards; neither \(u=2\) nor \(v=2\) is pruned as a gap alone.

Let \(W=t^2+b_W t+c_W\). Equating the paired residual values with \(rW\), and clearing only the true \(u\kappa(u)\) or \(v\kappa(v)\), gives the two polynomials
\[
 \mathcal R_f=D(u)(2h-b_W-3u)-(u-2)(3u-2)W(s_1)=0,\qquad
 \mathcal R_r=D(v)(2h+b_W-3v)-(v-2)(3v-2)W(s_3)=0.
\]
Their leading quartic coefficients cancel. Write \(S_4=\prod_{j=1}^4(t-s_j)\). Since \(H=L_4-rWC=H_4S_4\) is a true quartic on these singleton labels, \(H_4\ne0\) and \(H_4S_4\equiv L_4\bmod W\). At a D label \(t=q\), its two residuals are distinct, nonzero, off the graph, and solve the genuine quadratic \(L_4(q)-g(A_2(q)+Bg)=0\) with \(B\ne0\). Its constant term is nonzero. These observations supply the guards in the replays, where no \(W(q)\) at a D label is inverted.

## Even graph, unequal gaps

Modulo \(W=t^2-S\), \(L_4\) is a nonzero constant because \(W\mid Q\) and \(L_4\) is coprime to \(Q\). Writing \(\alpha(z)=3z-2h\), \(\beta(z)=(z-h)(2z-h)\), the \(t\)-coefficient of \(S_4\bmod W\) is
\[
 \alpha(v)(S+\beta(u))-\alpha(u)(S+\beta(v))
   =(v-u)\bigl[3S-3h^2+4h(u+v)-6uv\bigr].
\]
For \(u\ne v\), define \(e_1=u+v\) and \(e_2=uv=(3S-3h^2+4he_1)/6\). Both gaps are roots of the same polynomial \(\mathcal R_f(z)=\mathcal R_r(z)\). The monic \(z^2-e_1z+e_2\) must divide that polynomial; this requirement does not assert the latter has an invertible leading coefficient. An exact resultant in \(e_1\) of the two remainder coefficients, after clearing only \(h\)-guards, has the two irreducible factors
\[
      (8h^4-24h^3-120h^2-108h-27)^2,\qquad (h-1)^3.
\]
Reconstruct the simultaneous remainder gcd after each specialization. For the linear factor it is a unit (no pair). Over the quartic it has degree two in \(e_1\). In both of its geometric branches the candidate monic pair quadratic in \(u\) is eliminated completely by the distinct-clock and literal arithmetic/graph guards. The exact field replay explicitly tests the \(u-v\) guard rather than treating a repeated root as two distinct gaps.

## Even graph, equal gaps

Now \(u=v\); put \(x=u-h\), \(y=2u-h\). The four S labels are \(x,y,-x,-y\), and their distinctness plus \(W(x)W(y)\ne0\) are retained. We have \(\lambda=1\), \(r=\kappa(u)/(2W(x))\), and
\[
 H_4=\frac{S^2-aS+b_0}{W(x)W(y)},\quad
 \widehat C=\frac{L_4-H_4(t^2-x^2)(t^2-y^2)}{W}
       =c_0+c_2t^2,\quad
 c_2=1-H_4,\quad c_0=-a+H_4(x^2+y^2)+Sc_2.
\]
Here \(\widehat C=rC\). Using the true first residual \(1/2\) gives
\[
 B=\frac{4rL_4(h)-2\widehat C(-h)}{r(1-2rW(-h))}.
\]
The last denominator is nonzero by the first D being off the singleton graph. The true terminal equation is consistent with this even algebra.

Impose the [normalized trace](../sdirk-eight-all-dirty-seven-quadratic-five-d-prefix/README.md), \(2\sum_i1/g_i=\ell\sum_i b_i/g_i\), which has the form \(c_{\rm tr}/r+\mathcal T(A_2)=0\). With \(A_2=\widehat C/r-BrW\), multiplying by \(r(1-2rW(-h))\) gives the polynomialized necessary equation after inserting \(B\). The weighted term uses the coefficient of \(t^7\) modulo \(L_4^2\) for the genuine inverse weighted sum. The unweighted term uses quotient traces at \(P=(t+h)(t-h)t\) and \(W\), differentiating the logarithmic derivative in the Hermite branch; the resulting even constant is \(-2(2S-a)/(S^2-aS+b_0)\) before its \(1/r\) factor. Thus the formula is valid at \(S=0\) and does not divide out a possible common D/graph root. The script checks every nonconstant denominator factor against the true guards.

The resultant of the necessary normalized trace and the common cubic has irreducible \(h\)-factor degrees 3, 4 and 38. In each abstract number field, take the exact simultaneous \(u\)-gcd and strip the actual nonzero guards. The degree-3 and degree-4 branches leave unit gcd. In the degree-38 field the gcd is linear. This exact candidate satisfies the trace after reconstruction, so it is not discarded by regularity or reality tests.

Use the [literal fourth equation](../sdirk-eight-all-dirty-clock-census/README.md#3-exact-two-ended-fourth-read-exclusion-on-every-mesh) on that candidate. If \(T_f=a_0+b_1x+c_1x^2\) interpolates the actual forward first-three residuals at the actual normalized clocks and \(J\) is the zero-based primitive, then
\[
 g_4[1-\Lambda(x_4)+b_1+c_1\Delta(x_4)]=T_f(x_4)-JT_f(x_4),\quad
 \Lambda=1+(x-1)/\kappa(u),\quad
 \Delta=\tfrac43+\tfrac{2(\kappa(u)+1)}{3\kappa(u)}(x-1).
\]
For either endpoint label the unused residual is fixed by the product \(-L_4(h)/B\): it is \(-2L_4(h)/B\) at \(-h\), or \(-2L_4(h)/(B\lambda)\) at \(h\). Direct substitution rejects both. At the third D label use the gcd of the fourth affine equation with the true D quadratic; it is a unit. Nothing is divided by the affine coefficient of \(g_4\), including when it vanishes. This exhausts the possible physical fourth row, over all embeddings of the one abstract field.

## Split graph: two exact irreducible factors

Here \(W=t(t+d)\). The four S labels avoid both graph-zero clocks by literal nonzero defects. In particular \(S_4(0)\ne0\) and
\[
 H_4=L_4(0)/S_4(0),\qquad
 E=L_4(d)S_4(0)-L_4(0)S_4(-d)=0 .
\]
Set \(\Theta=(35h^2-21m^2)d^2-21m^2h^2+15m^4\). Project the integer \(E\) using the reverse cubic in \(v\), the forward cubic in \(u\), then \(\Theta\) in \(d\), removing only proved nonzero guards in the coordinates still present at each step. The resulting \(h\) factors are irreducible of degrees 4 and 60, with multiplicities 6 and 2. This implication uses polynomial resultants, not inversion of specialized leading coefficients. For the degree-four factor do *exact* reconstruction in its abstract number field. The \(d\)-gcd has two linear roots; the raw \(u\)-gcd degrees are 1 and 3, respectively. After the required guard strips, any surviving \(u\) component has a raw linear \(v\)-gcd, which is stripped by the remaining true literal guards. No geometric fiber survives.

For the degree-60 factor a fixed **simple good place**, not a test of rationality or finite-prime heuristics, is enough. The irreducible rational factor has simple root \(h=33\) modulo 43 and unit leading coefficient. Hensel gives an embedding of \(\mathbb Q(h)\) into \(\mathbb Q_{43}\) at that root for **any** putative characteristic-zero candidate of that irreducible factor. Extend this embedding first to the algebraic \(d\). The denominator \(35h^2-21m^2\) is a unit at this place, so any root of \(\Theta\) is integral. Its two residue roots are in \(\mathbb F_{43}\). At each of those roots both gap cubics retain degree three and **all** their roots, counted with multiplicity, lie in \(\mathbb F_{43}\). In particular the gap polynomials are nonzero before reduction, so any putative \(u,v\) are algebraic, admit extensions of the embedding into \(\overline{\mathbb Q}_{43}\), and are integral. Their residues are among the recovered roots, even if the original method lives in a nonsplit field or in a transcendental extension of the coefficient field of the mesh.

The only residue pairs obeying \(E=0\) are
\[
                  (d,u,v)=(14,18,22),\quad (29,22,18).
\]
The verifier checks **every** such pair for intact guards: no clock collision, no zero literal arithmetic or singleton graph guard, and none of the denominators needed to reconstruct \(r,\lambda,H_4,\widehat C,B\) vanishes. In particular it does not filter away a guard-zero residue component. Here use \(\widehat C=(L_4-H_4S_4)/W\) and exactly the same first-D formula for \(B\), with \(r=\kappa(u)/(2W(s_1))\) and \(\lambda=2rW(s_3)/\kappa(v)\). These expressions reduce correctly at the two pairs. The terminal D residual
\[
       L_4(h)-(\lambda/2)\bigl(A_2(h)+B\lambda/2\bigr)
\]
is 29 and 23, respectively. It would reduce to zero at every putative actual tableau. No division by \(B\) is needed at this good place, and it is not required to reduce to a unit. This closes the split branch over characteristic zero without asserting nonexistence over other paid characteristics.

## Replay and verification scope

Run in this directory with SymPy 1.14 and python-flint 0.8:
```sh
PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_even.py
PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_split_quartic.py
PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_split_degree60.py
```
The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticFinalBothD.lean) stages only the exact nodal and forward-ratio scalar identities. The rooted-order ingress, finite algebraic projections, trace evaluation, and good-place argument are a paper proof with exact replay, not an end-to-end native Lean theorem. No claim is made over arbitrary commutative rings or in finite characteristic.
