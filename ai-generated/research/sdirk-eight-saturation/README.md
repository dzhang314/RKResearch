# Order eight at the ten-stage nonsingular floor

The strict SDIRK order-eight interval remains **10–11** over the real algebraic numbers. The eleven-stage upper is exact: the existing order-at-least-eight witness has nonzero diagonal, and the order-nine nonsingular quadratic floor is thirteen. These results restrict tableaux at the lower endpoint, but do not exclude or construct a ten-stage method.

## A singleton quadratic zero has a forced clock, weight and diagonal

Let \(A,\boldsymbol b\) be a ten-stage lower triangular tableau of order at least eight over a characteristic-zero field, with every diagonal entry nonzero. Put
\[
\boldsymbol c\coloneqq A\boldsymbol1,\qquad
\boldsymbol g\coloneqq A\boldsymbol c-\tfrac12\boldsymbol c^{\odot2},\qquad
C\coloneqq\operatorname{diag}(\boldsymbol c),\quad
G\coloneqq\operatorname{diag}(\boldsymbol g),\quad
M\coloneqq CA-AC-A^2 .
\]
If **precisely one** component of \(\boldsymbol g\) is zero, at row \(i\), then its clock \(a=c_i\) satisfies
\[
\begin{gathered}
L_4(a)=0,\qquad
L_4(X)\coloneqq X^4-2X^3+\tfrac97X^2-\tfrac27X+\tfrac1{70},\\
 A_{ii}=\frac{4+35a(1-a)}{72},\qquad b_i=2A_{ii},\qquad
 (144A_{ii}-18)^2=30,\qquad i\in\{5,6\}\quad\text{(one-based).}
\end{gathered}
\]
Other weights may be zero, and clocks may repeat. For strict SDIRK, \(A_{ii}\) is the common diagonal \(\gamma\). Its only possible values in an ordered field are \((18\pm\sqrt{30})/144\), with the indicated root required to be in the field. A rational tableau cannot lie in this branch. In fact \(a\) generates a degree-four extension of \(\mathbb Q\): with \(Y=2a-1\), \(35Y^4-30Y^2+3=0\), irreducible by Eisenstein at \(3\). A finite characteristic-zero coefficient field for this branch must have degree divisible by four.

The [native saturation theorem](../../lean/RKCert/ReviewedNative/SDIRKOrderEightSingletonZeroSaturation.lean) proves the clock, diagonal, and weight formula from actual reviewed order and the unique quadratic zero (its input uses the defect \(2\boldsymbol g\)). Its [scalar and rooted-tree interface](../../lean/RKCert/ReviewedNative/SDIRKOrderEightSingletonZero.lean) is separate. The chronological placement and the additional obstructions below are mathematical proofs, not claimed as Lean theorems. The [scalar replay](check_scalar.py), run with Python 3 and no additional packages, checks the arithmetic independently. On Lean/Mathlib 4.36.0 both modules compile without diagnostics. Axiom checks of the guarded gate, full forward theorem, rational exclusion, and eleven-stage order-nine obstruction report only the three ordinary quotient, choice, and propositional extensionality axioms.

### Forward extraction

Normalize each actual \(\boldsymbol\Phi_t(A)\) by multiplying by the product of its child tree factorials. At grade \(j=|t|-1\) its scalar profile is \(X^j\). Let \(E_j\) be the numerical column space through grade \(j\) and \(F_j\) its zero-profile space. Root joining multiplies profiles and \(A\) acts on profiles as the zero-constant primitive \(J\). The [saturated Volterra flags](../clock-localized-tail/tied-stage-floor/README.md) give
\[
(\dim E_j)_{j=0}^{7}=(1,2,4,6,8,9,10,10),\qquad F_{j+2}=ME_j .
\]
A clock-polynomial vector plus a pure defect represents every vector in \(E_j\). Ordinary order pairs a representative \(r\) with the weighted clock polynomial \(P\) as \(I(rP)\), where \(I(X^k)=1/(k+1)\), if the total grade is at most seven.

If \(\boldsymbol v=r(\boldsymbol c)+\boldsymbol d\in E_2\) is supported entirely on \(i\), take \(\deg r\le2\) and \(\boldsymbol d\in F_2\). The four probes \(P=(X-a)X^k\), for \(0\le k\le3\), give zero observations, so \((X-a)r\) is orthogonal to all degrees at most three. The rational \(4\times4\) Hilbert matrix is invertible, hence \(r=0\). Since \(F_2=ME_0=\langle\boldsymbol g\rangle\) and \(g_i=0\), also \(\boldsymbol v=0\). Thus \(G\) is injective on \(E_2\), and \(GE_2=F_4\) by pure multiplication and dimension four. All of \(F_4\) vanishes at \(i\).

By contrast \(G\) cannot be injective on \(E_3\). Otherwise \(GE_3=F_5\) by dimension six, so all of \(F_5\) would vanish at \(i\). But both \(L_3(\boldsymbol c)\) and \(L_4(\boldsymbol c)\) belong to \(F_5\). Indeed \(E_5=\langle\boldsymbol1,\boldsymbol c,\boldsymbol c^{\odot2}\rangle+F_5\), where the scalar summand is detected by the first three probes, and both polynomials are orthogonal to all degrees at most two. Consecutive \(L_3,L_4\) cannot both vanish at \(a\), by the rational Bézout identity in the replay.

The kernel of \(G\) is the single coordinate axis at \(i\). Now we obtain an actual nonzero supported vector \(\boldsymbol v=r(\boldsymbol c)+\boldsymbol d\in E_3\), with \(\deg r\le3\), \(\boldsymbol d\in F_3\). The same four probes show that \((X-a)r\) is orthogonal to all degrees at most three, so \((X-a)r=\lambda L_4\). Here \(\lambda\ne0\); otherwise \(\boldsymbol v\in F_3\subset F_4\) and \(v_i=0\). Thus \(L_4(a)=0\); after normalizing \(\lambda=1\), write
\[
\Pi_a(X)=\frac{L_4(X)-L_4(a)}{X-a}.
\]
The paid zero read for \(F_4\) gives \(v_i=\Pi_a(a)\ne0\). No root-simplicity premise is needed for cancellation: the nonzero supported vector supplies it.

Apply \(A\) to \(\boldsymbol v\). Its literal value at \(i\) is \(A_{ii}v_i\), and its paid grade-four model there is \((J\Pi_a)(a)\). The output also gives \(b_i v_i=I(\Pi_a)\). Exact polynomial identities modulo \(L_4(a)=0\) give
\[
(J\Pi_a)(a)=\frac{4+35a(1-a)}{72}\Pi_a(a),\qquad
I(\Pi_a)=2(J\Pi_a)(a).
\]
Cancel \(v_i\), then substitute into the asserted quadratic. The phrase *Gauss cardinal mass* refers only to this polynomial identity. No selection of all four real roots, root sorting, analytic integration, or positivity is needed. The algebraic argument uses only denominators that are units of \(8!\), and likewise works over fields of characteristic greater than seven; the native modules currently assume characteristic zero.

### The zero row is necessarily in the middle

The reverse spaces \(W_j,Z_j\) use actual rows starting from \(\boldsymbol b^{\mathsf T}\) and right multiplying by \(A,C\); their scalar profiles apply \(J^* f(X)=\int_X^1 f\) or multiply by \(X\). The [bidirectional flag theorem](../../lower-bounds/characteristic-zero/sdirk_saturated_weighted_mirror_duality_20261123.md) gives \(\dim W_j=\dim E_j\), \(Z_{j+2}=W_jM\), and \(Z_{j+2}=\operatorname{Ann}(E_{5-j})\) in the paid grades. Right multiplying \(W_j\) by \(G\) also produces only rows in \(Z_{j+2}\): pair against any forward column in \(E_{5-j}\) and join the pure quadratic at the marked vertex. No transpose tableau or inverse output weight is needed.

The last weight \(b_{10}\) is nonzero by trimming against the floor. The terminal component of \(\boldsymbol b^{\mathsf T}M\) is \(-b_{10}A_{10,10}^2\ne0\), and \(\boldsymbol b^{\mathsf T}G\in Z_2=\langle\boldsymbol b^{\mathsf T}M\rangle\). If the unique zero were terminal, that would force \(\boldsymbol b^{\mathsf T}G=0\), leaving at most one nonzero weight, impossible by the degree-one Hilbert matrix. Thus \(g_{10}\ne0\), and \(\boldsymbol b^{\mathsf T}G\) spans \(Z_2\). Accordingly
\[
 W_2=\langle\boldsymbol b^{\mathsf T},\boldsymbol b^{\mathsf T}C,
          \boldsymbol b^{\mathsf T}C^2,\boldsymbol b^{\mathsf T}G\rangle .
\]
A row supported solely at \(i\) cannot lie nontrivially in \(W_2\): the same pairings with \((X-a)X^k\) kill its scalar polynomial, while its pure part already vanishes at \(i\). Hence \(W_2G=Z_4\) by dimension four, and all reverse pure rows through grade four vanish at \(i\).

On the literal prefix through \(i\), take the four columns \(\boldsymbol1,\boldsymbol c,\boldsymbol c^{\odot2},\boldsymbol g\). The three probes \(\boldsymbol e_i^{\mathsf T}A^k\) for \(0\le k\le2\) read the first three as \(a^{j+k}j!/(j+k)!\) for \(0\le j\le2\) and kill the fourth, by the clean grade-four property. The scalar matrix has determinant \(-a^6/72\ne0\); \(\boldsymbol g\) is nonzero at the first row because its diagonal is nonzero. These four independent columns are all killed by the prefix restriction of \(\boldsymbol e_i^{\mathsf T}M\), which is nonzero at \(i\). The prefix has at least five rows.

On the literal suffix starting at \(i\), take the three rows \(\boldsymbol b^{\mathsf T}(I-C)^j\), \(0\le j\le2\), and the pure row \(\boldsymbol b^{\mathsf T}G\). Read them against \(A^k\boldsymbol e_i\), \(0\le k\le2\). This gives the reflected factorial matrix at \(1-a\), multiplied by \(b_i\ne0\), and kills the pure row, which is nonzero at stage ten. As \(L_4(0)=L_4(1)=1/70\), both scalar probes are nonsingular. All four rows annihilate the suffix restriction of \(M\boldsymbol e_i\), a nonzero column at \(i\), so the suffix also has at least five rows. Lower triangularity permits all these actual restrictions; clocks are not recomputed from a trimmed tableau. Together the width inequalities force \(i=5\) or \(6\).

## Two distinct zero clocks are both Gauss clocks

Assume *exactly two* literal zero quadratic residuals, with distinct clocks \(a,b\). Let \(Z\) be the two-dimensional coordinate space on those two physical rows. Then **both** \(a,b\) are roots of \(L_4\), with no condition on signs or on any output weight.

Indeed, if either clock is not such a root, \(E_2\cap Z=0\): for a supported degree-two scalar profile \(r\), the four vanishing probes \((X-a)(X-b)X^k\), \(0\le k\le3\), force \((X-a)(X-b)r\) to be a multiple of \(L_4\). If either clock is not a root, this multiple has to vanish. The remaining pure \(F_2\) vector vanishes on \(Z\), so the original vector is zero. Hence \(GE_2=F_4\) and both zero rows have clean grade-four reads.

In that branch \(\dim(E_3\cap Z)\le1\): if it were two, each coordinate axis would be supported by a genuine grade-three profile. The same single-axis four-probe argument used above with the corresponding clock would force \(L_4(a)=L_4(b)=0\), a contradiction. Thus \(GE_3\) has dimension at least five. It vanishes on the two zero rows, and \(\dim F_5=6\), so the restriction of \(F_5\) to those rows has rank at most one. Apply this to \(L_3,L_4,L_5\), all orthogonal to degree at most two, hence in \(F_5\). If one \(L_4\) value is zero, its \(L_3\) value is nonzero, which forces the other \(L_4\) value to be zero as well. If neither is zero, both ratios \(L_3/L_4,L_5/L_4\) agree at \(a,b\); but
\[
      L_5(X)/L_4(X)=X-\tfrac12-\tfrac4{63}L_3(X)/L_4(X)
\]
where \(L_4\ne0\), forcing \(a=b\). Thus every case with a non-Gauss zero clock is impossible. Coincident zero clocks and three or more zero rows require a separate analysis. This proof also works in fields of characteristic greater than seven.

### A common-diagonal reflection test on the two distinct zero clocks

The following sufficient conditions for reflection do **not** follow automatically from having exactly two zero rows. Over characteristic zero with common diagonal, if either \(E_2\cap Z\ne0\), or \(E_2\cap Z=0\) and \(E_3\cap Z=Z\), then the two zero clocks satisfy \(a+b=1\). The other branch, \(\dim(E_3\cap Z)=1\) and \(E_2\cap Z=0\), is not decided here.

For the latter hypothesis \(E_3\cap Z=Z\), use the clean grade-four reads and the two actual coordinate axes exactly as in the singleton proof: both diagonals are their half masses. Equality means \(a(1-a)=b(1-b)\), hence \(a+b=1\).

For \(E_2\cap Z\ne0\), the same probes give a genuine nonzero supported vector with normalized trace
\[
r(X)=L_4(X)/[(X-a)(X-b)].
\]
Its values on the two rows are \(r(a),r(b)\ne0\), since \(F_2\) vanishes there and \(L_4\) is simple. Simplicity follows directly from \(35Y^4-30Y^2+3\) in \(Y=2X-1\): a root has \(Y\ne0\) and \(Y^2\ne3/7\), hence nonzero derivative. Pairing with each degree-three cardinal \(\Pi_a/\Pi_a(a)\) or \(\Pi_b/\Pi_b(b)\) shows both literal output weights equal the respective Gauss masses, thus nonzero: the difference between \(r\) and its value at the selected site, multiplied by the cardinal, is a multiple of \(L_4\) with quotient degree at most one.

Here \(g_{10}\ne0\) by the same terminal argument as before (at most two weights cannot pay the order-eight moment Gram). No vector in \(E_1\) or row in \(W_1\) can be nontrivially supported on \(Z\): pairing its at-most-linear trace with \((X-a)(X-b)X^k\) for \(0\le k\le3\) and applying the Hilbert test kills it. Thus \(GE_1=F_3\) and \(W_1G=Z_3\) by dimension two, giving two-sided clean grade-three reads at both zero rows. The actual supported vector has a weighted row in \(W_2\), because its \(F_2\) part is a multiple of \(\boldsymbol g\) and \(\boldsymbol b^{\mathsf T}G\) spans \(Z_2\). Write \(a\) for the chronologically earlier clock and \(b\) for the later one. Forward application of \(A\) at the earlier row and reverse application at the later column see only their respective diagonal terms, and the clean reads force
\[
     \gamma=(Jr)(a)/r(a)=(J^*r)(b)/r(b).
\]
If \(y=2a-1\) and \(z=2b-1\) are not opposite, the other two roots of the centered quartic are \(-y,-z\); write \(p=yz\). Then \(y^2+z^2=6/7\) and \(p^2=3/35\). The centered profile is proportional to \(R(U)=(U+y)(U+z)\) and the common two primitive ratios have a common factor \(1/2\) from variable change. As \(R(y)=2y(y+z)\), \(R(z)=2z(y+z)\), equality of the ratios reads
\[
 z\int_{-1}^y R(U)\,dU-y\int_z^1 R(U)\,dU
       =(p+1/3)(z-y)-2p/7-6/35=0.
\]
Square this equation using \((z-y)^2=6/7-2p\) and reduce by \(p^2=3/35\). The resulting equation is \((176/2205)p+464/25725=0\), so \(p=-87/385\), whose square differs from \(3/35\) by \(-5136/148225\). This is impossible in characteristic zero. The arithmetic uses no ordering; the displayed integrals again stand only for polynomial primitives. This proves the claimed reflection condition.

## No unchanged-residual chronology reversal in the nowhere-zero branch

Here assume **all** \(g_i\ne0\) and the additional symmetry
\[
(c_{11-i},g_{11-i})=(1-c_i,g_i)\qquad(1\le i\le10).
\]
In the [nowhere-zero complete-intersection theorem](../clock-localized-tail/tied-stage-floor/SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md), the ten distinct pairs exhaust the intersection of unique weighted-degree-\((4,5)\) equations \(U(X,Z),V(X,Z)\) with traces \(L_4(X),L_3(X)\), with no intersection at infinity after \(Z=t^2\). Reflection \(X\mapsto1-X\) preserves \(L_4\) and negates \(L_3\); uniqueness makes \(U\) invariant and \(V\) anti-invariant. Thus \(V(1/2,Z)=0\) identically. The coefficient of \(Z^2\) in \(U\) is nonzero, since otherwise both leading forms would vanish at \((X:t)=(0:1)\). Hence \(U(1/2,Z)=0\) has a root over the algebraic closure, necessarily one of the physical pairs by the complete intersection. A chronology reversal on ten rows has no fixed index and would pair this point with an identical physical pair, contradicting distinctness. This argument is characteristic zero and does not use ordering. It excludes unchanged-residual chronology reversal, not all reflected clock sets or the residual-sign-flip case.

## The archived eleven-stage donor has no second diagonal twin

Twins must have the same actual \(c_i,g_i\): their rows after subtracting their respective common diagonal terms have equal sums, and their actions on \(\boldsymbol c\) are identical after diagonal terms are restored at equal clocks. In the archived [literal donor](../../lean/evidence/reviewed-native-sdirk118-witness-20261125/README.md), all eight virtual suffix rows are quadratically clean by the low seed and graft identities in *SDIRK118ChartGlue*. The four prefix clocks, normalized by the common diagonal, are \(1,a_*,s,d\), \(a_*=(1+s)/2\); their residuals in units of \(\gamma^2\) are \(1/2,g_1,0,g_d\). They are distinct clocks on the guarded box \(s\in[13/32,14/32]\), \(d\in(15/4,4)\). Also \(g_1\ne0\) from its literal expression, and \(g_d\ne0\) since \(q_s(d)=d(d-s-3)+s>0\) and the remaining factors and denominator of \(g_d\) are nonzero by the guarded chart. Thus none of the three nonclean prefix rows can be a twin.

In the virtual suffix, the zero-based site list is \([1,5,4,0,3,2,1,0]\), with all six distinct site clocks. The clean prefix row at \(\gamma s\) is the already contracted twin of suffix row \(0\), leaving its only candidate at suffix row \(6\). Row \(6\)'s tap from retained suffix row \(5\) is a nonzero mass ratio times the reverse old entry \(R_{2,1}=\gamma\,2/(h-2)\) with \(h=a_*-1\); the prefix row has no such tap. For the other repeated suffix site, rows \(3,7\), the later row's tap from retained suffix row \(6\) is a nonzero mass ratio times \(R_{1,0}=\gamma h\), absent at row \(3\). Both entries survive the first contraction, which only merged suffix row \(0\) into prefix row \(2\). This exhausts the potentially equal-\((c,g)\) pairs. The result is scoped to the guarded archived tableau, not a different construction or contraction mechanism.
