# Final arithmetic-front / live reflected star chart is impossible

Consider a strict ten-stage SDIRK tableau \(A,\mathbf b\) of ordinary order at least eight over a characteristic-zero field. Let the common diagonal be \(\gamma\ne0\), \(\mathbf c=A\mathbf1\), and \(\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2\). Suppose exactly seven physical residuals vanish, at seven distinct clocks, and the three off-zero clocks are pairwise distinct. The literal first three rows are off in an arithmetic phase, the reflected second residual ratio is nonzero, and physical row 8 is live in the reflected star phase.

**Result.** This chart is impossible over every characteristic-zero field. Together with the [preceding cubic-first-clock exclusion](../sdirk-eight-seven-zero-final-cubic-front/README.md), this eliminates **every** live reflected star in the final seven-distinct zero chart. The [live reflected arithmetic exclusion](../sdirk-eight-seven-zero-supported-quartic/README.md) is already valid over all paid fields. This packet leaves the silent eighth zero, and does not change the general stage interval.

## 1. One scalar parameter for the literal early quartic

Use the [gap-free fourth reverse star equations](../sdirk-eight-seven-zero-final-cubic-front/README.md#2-gap-free-star-constraints-and-fixed-ghost-moments). All off weights are silent, and the last three physical rows are the last three zero rows. Let \(p_4(X)\) be monic with roots the first four physical zero clocks in the **physical reflected** coordinate \(X=1-c_i\). Thus \(p_4\) includes the fourth zero before the trailing three, with reflected clock \(x_e=\gamma e\), where \(e\) is its normalized reflected clock. Write \(I(X^j)=1/(j+1)\), and
\[
 {\cal C}_f(x)=I_X\bigl((f(X)-f(x))/(X-x)\bigr),\qquad
 \ell(X)=\frac{70X^4-140X^3+90X^2-20X+1}{70}.
\]
The three ordinary star constraints are \(H_1=H_0,\ H_2=2H_0,\ H_3=2H_0\) in the centered normalized clock of the preceding proof. The normalized reflected coordinate is two minus that centered clock, so its moments through three are \(H_0(1,1,2,6)\). Dividing clocks by \(D=1/\gamma\) and the early monic polynomial by \(D^4\), there is a nonzero scalar \(\psi=B_t/D^4\), with \(B_t\) the live penultimate cardinal numerator, such that
\[
 I(X^j p_4(X))=j!\gamma^j\psi\quad(0\le j\le3).
\]
The monic solution is exactly
\[
 p_4=\ell+\psi S,\qquad
 \deg S\le3,\qquad I(X^j S)=j!\gamma^j,\quad 0\le j\le3.
\]
This uses only the four-by-four ordinary Hilbert inverse: subtract \(\ell\) and solve for the four lower coefficients. It is independent of any graph pivot or zero-row weight sign.

The gap-free fourth reverse gate, converted from the centered coordinate \(2-e\), is
\[
 F(x_e,\gamma){\cal C}_{p_4}(x_e)+W(x_e,\gamma)\psi=0,\quad
 F(x,\gamma)=x^3-9\gamma x^2+18\gamma^2 x-6\gamma^3,\quad
 W(x,\gamma)=x^2-8\gamma x+11\gamma^2.
\]
Indeed in normalized reflected coordinates the star gap-free gate has the factor \(e-1\), a forbidden collision with the terminal clock, and after its cancellation the coefficient of the normalized divided mean is \(e^3-9e^2+18e-6\). The physical change of scale multiplies that coefficient by \(\gamma^3\) and its scalar partner by \(\gamma^2\). The reflected divided mean changes sign from the original forward one; both conventions are checked by the native identity.

Together with \(p_4(x_e)=0\), the two scalar equations are linear in \(\psi\). Eliminating \(\psi\) without division gives
\[
  A(\gamma)e^2+B(\gamma)e+C(\gamma)=0,                       \tag{1}
\]
where
\[
\begin{split}
 A&=1680\gamma^4-840\gamma^3+180\gamma^2-20\gamma+1,\\
 B&=-6720\gamma^4+4200\gamma^3-1080\gamma^2+140\gamma-8,\\
 C&=2520\gamma^4-1680\gamma^3+540\gamma^2-120\gamma+11 .
\end{split}
\]
The replay certifies this identity from the exact Hilbert reconstruction and the two linear equations. In particular, the normalized latest clock has been reduced to a quadratic, not a projective diagonal approximation. We separately retain both \(A=0\) and singular \(S(x_e)\) in the proof below.

## 2. A division-free forward graph equation

Write \(u\) for the normalized forward second gap; the three literal off clocks in the original forward physical coordinate are \(\gamma,\gamma(1+u),\gamma(1+2u)\). The actual unscaled residual graph on these sites takes the form
\[
 P=P_0+pR_1+qR_2,\quad
 P_0(T)=2\gamma T-\gamma^2-\tfrac12T^2,\quad
 R_1=(T-\gamma)^2,\quad R_2=-\gamma(T-\gamma),\quad q=pu,
\]
where the literal arithmetic tap gives \(pH(u)=3u-2\) and \(H(u)=-2+u+4u^2-u^3\). Thus
\[
 -2p^3+qp^2+4q^2p-q^3-(3q-2p)p=0.                           \tag{2}
\]
This consequence holds even when \(p=0\).

Let \(a,b\) be the first two zero clocks, in original forward physical coordinates. The two [actual supported reads](../sdirk-eight-seven-zero-three-clock-five-label/README.md#2-ordinary-projection-and-actual-supported-forward-reads), with \(J\) the primitive from zero and \(L=70\ell\), are
\[
\begin{split}
 f(P)&=JP(a)-\gamma P(a)=0,\\
 g(P)&=L(a)\bigl[\gamma(b-a)P(b)+aJP(b)-J(TP)(b)\bigr]
       -L(b)\bigl[\gamma aP(a)-J(TP)(a)\bigr]=0 .
\end{split}
\]
They are linear in \(p,q\). Let \(f_i,g_i\) be their values on \(P_0,R_1,R_2\) in order. Set
\(\Delta=f_1g_2-f_2g_1,\ N_p=f_2g_0-f_0g_2,\ N_q=f_0g_1-f_1g_0\).
Then \(N_p=\Delta p,N_q=\Delta q\), without assuming \(\Delta\ne0\). Equation (2) gives the necessary scalar
\[
 -2N_p^3+N_qN_p^2+4N_q^2N_p-N_q^3-(3N_q-2N_p)N_p\Delta=0.    \tag{3}
\]
No possibly singular graph pivot is discarded in the projected equation.

## 3. Exact fraction-free ordered-root projection

For \(A\ne0,\ S(x_e)\ne0\), recover \(\psi=-\ell(x_e)/S(x_e)\). Introduce \(\widehat e=Ae\), a root of the monic polynomial \(\widehat e^2+B\widehat e+AC\). As \(x_e=\gamma\widehat e/A\), the quantities
\(S_* = A^3 S(x_e),\ L_* = A^4\ell(x_e),\ M=A S_*\)
are polynomial expressions in the monic \(\widehat e\) algebra, and \(\psi=-L_*/M\). Define the monic polynomial
\[
 \widehat p_4(Z)=M^4\ell(Z/M)-M^3L_* S(Z/M).
\]
It is polynomial in the same algebra, and its known root \(Mx_e=\gamma\widehat e S_*\) is removed by exact monic division. On the remaining monic cubic, take one generic root for the first chronological zero, and a generic root of the monic complementary quadratic for the second. This finite-free ordered-root computation has ranks \(2,3,2\), and includes all directed actual choices.

Use the scaled original forward clocks \(M-Z_a,M-Z_b\), diagonal \(M\gamma\), and endpoint \(M\) in the graph functionals; \(L_M\) is the corresponding degree-four polynomial. The exact rescaling does not change \((p,q)\). Equation (3) in this algebra gives a necessary polynomial in \(\gamma\) by taking the determinant of multiplication on each successive monic quotient. If an actual directed pair satisfies (3), evaluation at its roots is a homomorphism and forces the determinant to vanish. This does not rely on natural order of the polynomial roots.

The raw projection has degree **8868**. At the two generic scales the proof keeps their base zero sets as separate cases. Let \(S_{99},S_{76}\) be the two monic degree-twelve factors of the norm of \(S_*\), identified at the residues \(99,76\) modulo 101, respectively; the rest of that norm is the quartic \(A\) to the third power, up to units. Exact division of the raw projection by
\[
 \gamma^{48} A_{\rm monic}^{990} S_{99}^{198} S_{76}^{126}
\]
leaves the degree-972 generic polynomial, with exact irreducible factor degrees and multiplicities \(612^1,48^3,12^{18}\). The division verified by the script is exact, not a factor guessed by sampling. The other possible base zeros \(A,S_{99},S_{76}\) remain in the independent exceptional checks.

## 4. All generic and exceptional fibers

The generic factors are coprime to the scales \(A\) and \(\operatorname{Norm}(S_*)\). Two degree cases have one genuine forbidden \(e\)-branch, found by exact norms **before** any residue deletion:

* At the degree-48 factor, the exact norm of the scaled early quartic discriminant vanishes; thus at least one of the two \(e\)-roots gives a repeated early clock. The selected good reduction has two simple \(e\)-roots and exactly one repeated-clock branch. It identifies the exact forbidden branch by uniqueness, rather than discarding every \(e\) over that \(\gamma\).
* At the degree-12 factor, the exact norm of \(L_*\) vanishes, so at least one \(e\)-root has \(\psi=0\), impossible because the penultimate weight and its nodal derivative are nonzero. The selected reduction again identifies one, and only one, such branch.

At \(A=0\), the linear equation for \(e\) has a unit coefficient in the selected reduction. At a scale guard \(S(x_e)=0\), use the other (fourth-reverse) coefficient \(F{\cal C}_{S}+W\) whenever it is a unit and check the first equation as well. If the first pivot guard is exact and has a unique zero residue, its exact \(e\)-branch may instead be rejected with \(\ell(x_e)\ne0\) verified there. These checks retain the other \(e\)-root when a pivot branch fails.

At every admitted reduced \(e\)-fiber, reconstruct \(\psi,p_4\), and test all six directed orders of the three earlier clocks distinct from \(x_e\). Use the cleared graph \(P_\sharp=H(u)P_0+(3u-2)(R_1+uR_2)\). The literal first and second equations are cubics or lower in \(u\), with at least one preserving unit degree three for every pair. The extra supported cubic \(R_{\rm off}=(T-\gamma)(T-\gamma(1+u))(T-\gamma(1+2u))\) gives the necessary second-row equation
\[
 L(a)\left[P_\sharp(a)(\gamma R_{\rm off}(b)-JR_{\rm off}(b))
              +(JP_\sharp(b)-\gamma P_\sharp(b))R_{\rm off}(a)\right]
 -L(b)P_\sharp(a)(\gamma R_{\rm off}(a)-JR_{\rm off}(a))=0 .
\]
This is the actual \(F_4\) line read with the first-zero pivot cleared and no weight divided. At the dominant factor one reduced first/second common-gap candidate remains, and this cubic read removes it. All other tested tables already have constant first/second gcd; the script also contains the optional third forward determinant as a cross-check.

| Exact diagonal factor | \(p\) | Simple geometric residue factor for \(\gamma\) | Directed pairs |
|---|---:|---|---:|
| Generic degree 612 | 101 | \(\gamma^2+95\gamma+35\) | 12 |
| Generic degree 48, one repeated-clock \(e\) | 103 | \(\gamma+85\) | 6 |
| Generic degree 12, one zero-cardinal \(e\) | 101 | \(\gamma^3+93\gamma^2+78\gamma+33\) | 6 |
| Leading quartic guard \(A\) | 101 | \(\gamma+11\) | 6 |
| First degree-12 scale guard | 101 | \(\gamma+2\) | 12 |
| Second degree-12 scale guard | 101 | \(\gamma+25\) | 6 |

One such simple residue factor per irreducible **exact** factor suffices. An actual root generates that exact number field; choose its embedding lifting this residue factor and extend it to the reconstructed algebraic clocks. The leading \(e\) coefficients or the actual linear guard, one \(\psi\) pivot at each admissible branch, and the monic early quartic ensure all these coordinates are integral. The degree-three unit from the front equations does the same for any actual \(u\). The replay checks every \(e\) and every early-clock ordering over the selected geometric field, not only base-field roots. Consequently these computations exclude the characteristic-zero branches and do not assert that absence over a single residue field by itself would suffice.

## 5. Replay and native scope

Run `python check_star.py` with SymPy 1.14 and python-flint 0.8. The fraction-free norm and exact guard division take about twenty seconds; the six fixed residue checks are much shorter. The full tableau ingress, exact number-field projections, and finite geometric fiber checks are recorded separately above.
