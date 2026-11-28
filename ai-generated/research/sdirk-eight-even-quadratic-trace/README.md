# Paid exclusion of the even quadratic supported trace at three distinct strict SDIRK8 zeros

Let a strict ten-stage SDIRK tableau have ordinary order at least eight, nonzero common diagonal $\gamma$, $c=A1$, and $g=Ac-c^{\odot2}/2$, over a field of characteristic zero or greater than seven. There are exactly three physical zero entries of $g$, at three distinct clocks. Use the saturated order spaces $E_j,F_j,W_j,Z_j$ and centered clock $y=2c-1$.

**Result.** There is no nonzero supported degree-two vector with trace $r(y)=y^2+q$, i.e. an even monic quadratic in centered time. No symmetry of the tableau is assumed. The scope is this centered-even trace, not an arbitrary quadratic trace or a general ten-stage exclusion. The [prior paid support exclusions](../sdirk-eight-three-zero-silent-paid/README.md) force all ten weights and all three zero-site values of $r$ nonzero in this case. They also force the seven off-zero rows to have distinct clocks, with $g$ a nonzero multiple of $r(2c-1)$ there.

## 1. Three-site Hankel and a diagonal identity

Use $I(y^j)=1/(j+1)$ for even $j$ and $I(y^j)=0$ for odd $j$, with unit total mass. Put
$$m_0=q+1/3,\quad m_2=q/3+1/5,\quad m_4=q/5+1/7.$$
The signed three-site quadrature of density $r$ has exact moments through five, by the supported weighted grade-two read. Its $3\times3$ Hankel is nonsingular (Vandermonde and three nonzero signed weights). Thus $m_2(m_0m_4-m_2^2)\ne0$. The monic nodal polynomial is $P(y)=y^3-wy$ with $w=m_4/m_2$: the centered signed moment equations force this polynomial by uniqueness. The three sites are distinct, so $w\ne0$. The signed weights at the two nonzero sites are $m_2/(2w)$, and the signed weight at zero is $m_0-m_2/w$. The ordinary weights on the three zero rows are obtained from these by dividing by $w+q$ and $q$ respectively, both nonzero by supported cleanness.

Here is the diagonal calculation, with no positivity. Let $v=r(2c-1)+\alpha g$ be the actual supported column and $B=\operatorname{diag}(b)$. Restrict $S=BA+A^{\mathsf T}B-bb^{\mathsf T}$ to the three zero coordinates, and multiply its $ij$ entry by $r(y_i)r(y_j)$ to form $T_{ij}$. The clean grade-three forward and reverse reads give $S v=0$ on these coordinates: they are $Jr$ and $J^*r$ respectively, whose sum is $I(r)$, also the supported output read of $v$. Thus $T$ has row sums zero. Its quadratic contraction $y^{\mathsf T}Ty=0$ is the paid grade-seven self-pair of the supported grade-three vector $yv$; on scalar traces $2I(f Jf)=I(f)^2$. The identity $P'(y_i)+P'(y_j)=(y_i-y_j)^2$ on a distinct pair of cubic roots implies
$$\sum_i b_i(2\gamma-b_i)r(y_i)^2P'(y_i)
=\sum_i T_{ii}P'(y_i)=y^{\mathsf T}Ty=0.$$
Using the exact symmetric signed weights, this is $2\gamma A_0=B_0$, with
$$A_0=3m_2 I(y^2r^2)-m_4 I(r^2)
=\frac{2(q+1)^2(7q+3)}{105},$$
$$B_0=2m_0m_2^2-m_4m_0^2
=\frac{(3q+1)(35q^2+90q+51)}{4725}.$$
Accordingly, if $A_0\ne0$ the forced diagonal is
$$\gamma=\frac{N}{L},\qquad
N=(3q+1)(35q^2+90q+51),\quad L=180(q+1)^2(7q+3).$$

## 2. Actual endpoint chronology

The first two rows in either direction are off-zero: the first is a nonzero diagonal's quadratic defect, and if the second defect vanished the actual leading pure relation would concentrate every off-zero clock at $\gamma$, contrary to the seven distinct clocks. Reflection is legitimate since all weights are nonzero, and gives the same $\gamma$ and a reflected pure residual proportional to the physical one. Thus the centered graph is unchanged. Write
$$R=(2\gamma-1)^2+q,\quad D=R+4\gamma^2,\quad U=2R-2\gamma(4\gamma-2).$$
The normalized second gap $u\ne0$ is prescribed by $Du=U$ in each direction. If $D=0$, this equation gives $U=0$ and forces $(\gamma,q)=(1/4,-1/2)$, where $2\gamma A_0-B_0=1/2700$, never zero in a paid field. Thus $D\ne0$ and the gaps agree.

A star third cannot occur. Its first two off-zero residual values at rows two and three agree, so distinctness and the even quadratic graph give $c_2+c_3=1$. The star phase has $c_2+c_3=4\gamma$, so $\gamma=1/4$ and $U=2D$ then give $u=2$, which duplicates the first clock in a star. Therefore both ends are in the arithmetic phase, with the same actual third residual ratio and both off-zero (**A/A**) or both zero (**Z/Z**). With $H(u)=-2+u+4u^2-u^3$ the actual adjacent tap ratio $t$ satisfies $tH=2u(3u-2)$. In A/A the quadratic graph reads $Rt=Du$, so the necessary homogeneous gate in $D,U$ is
$$F=-2D^3+UD^2+4U^2D-U^3-2R(3U-2D)D=0.$$
In Z/Z the two extreme zero sites are on the actual third rows, with opposite centered clock $z/D$ for $z=2\gamma(D+2U)-D$. They are distinct, so these are the two noncentral roots. The gates are
$$Q=4U^3-12U^2D+3UD^2+2D^3=0,\qquad m_2 z^2-m_4 D^2=0.$$

For either phase the earliest supported zero in either direction reads its scalar primitive with only the common diagonal. In centered units the primitive equality is
$$2y^3-12\gamma y^2+6qy+2+6q-12\gamma q=0.$$
At least one of the two chronological extreme sites is noncentral. At such a root use $y^2=w$, eliminating its sign to obtain the necessary polynomial
$$m_2(2m_2+6qm_2-12\gamma(m_4+qm_2))^2
-m_4(2m_4+6qm_2)^2=0.$$

If $A_0=0$, we also need $B_0=0$. The displayed factorizations leave only characteristic 11, with $q=-3/7=9$. There $w=1$. In either direction the negative endpoint $y=-1$ cannot be an earliest zero (its primitive is zero but its diagonal read is nonzero), so the required noncentral anchor is $y=1$. It forces $\gamma=9$. The actual gap is then $u=1$, with arithmetic tap ratio 1 and nonzero third residual ratio 3. Its graph instead expects $r(2\gamma(1+2u)-1)=2$ whereas $R=1$. This excludes the singular diagonal.

## 3. Complete paid prime support, including nonsplit coefficients

For $A_0\ne0$, substitute $\gamma=N/L$ homogeneously, term by term with a single common power of $L$, in each of the four polynomial gates. All rational coefficient denominators have prime support in $2,3,5,7$. Only integer primitive factors of known nonzero guards are removed: $q,m_2,m_4,m_0m_4-m_2^2,m_4+qm_2,L,N$, and the homogeneous nonzero graph and gap denominators $R,D$. In particular the integer content of each gate is retained. The trimmed gate degrees are 10 (A/A arithmetic), 21 and 21 (Z/Z residual and pin), and 11 (noncentral anchor).

The exact resultant of the two A/A polynomials, after stripping only paid prime factors, is $11^6\cdot965179\cdot3535032504307\cdot3489226706289835873$. In Z/Z take the gcd of resultants of the residual gate against the pin, anchor, and their sum: its stripped value is $11^{12}\cdot1439\cdot420941\cdot48029\cdot434112360658085729$. Every listed factor is certified prime by the literal recursive full-factor Lucas/Pocklington data in `prime_certificates.py`, independently verifying each $p-1$ factorization and its modular witness. This is an exact integer characteristic support, not a sampled finite-prime run.

In each listed characteristic we compute the full reduced common polynomial in $q$. In characteristic 11 both ordinary phase gcds are $(q+2)^2$, which returns the already rejected singular diagonal. At each other listed characteristic there is exactly one linear common factor for the listed phase and no root in the other phase. The noncentral anchor at those $q,\gamma$ is linear with nonzero leading coefficient in $y$ after substituting $y^2=w$, so it gives its actual oriented root in the prime field; in Z/Z the same root is fixed by the actual third clock. The other two zero clocks are its reflection and $1/2$. These rules cover roots over algebraic closures, not just roots searched in the prime field.

## 4. Seven literal finite controls and fourteen contradictions

For each remaining finite control, interpolate the first three normalized residuals by a quadratic $P_3(X)$. All three actual clocks are distinct in the controls; the first two are off-zero. Since $A(g-P_3(c))$ has scalar trace $-JP_3$ and pure part in $\langle g,Cg\rangle$, the first two reads determine the affine pure coefficient $\xi+\eta X$. On the actual fourth stage the preceding values of $g-P_3(c)$ are zero; hence
$$(JP_3)(x)-\gamma P_3(x)+g_x(\gamma-\xi-\eta x)=0.$$
Impose the known quadratic graph for a nonzero fourth residual, or the corresponding zero read at one of the three supported clocks. In A/A the off-zero cubic has all its three roots at preceding off-zero clocks, which cannot repeat; the only fourth zero is the actual earliest one. In Z/Z the off-zero cubic has the two preceding off-zero roots and one new simple off-zero root, with no available fourth zero. The only candidate fourth zero there would be the remaining center, since the two noncentral zero sites already occur at the two third rows. The same conclusions hold at the reflected end. The cubic's complete factorizations also justify the fourth clock choices in field extensions.

Thus six off-zero clocks are forced and come in three reflected pairs. Let $I_0$ be ordinary integration minus the already known symmetric three-zero-row weighted functional. For the product $Q_6$ of the forced six distinct off-zero factors, $I_0(Q_6)\ne0$ in an actual tableau: it is the seventh site's nonzero weight times its nonzero evaluation of $Q_6$. Reflection gives $I_0(XQ_6)=I_0(Q_6)/2$, so the seventh off-zero clock is $1/2$. This and the remaining zero clock $1/2$ occupy physical rows five and six in one of the two orders. The remaining seven ordinary weights are determined by the degree-six Vandermonde; the replay reconstructs and checks all scalar moments through seven and all six scalar pure-residual moments. A failed scalar test is not needed: each of the fourteen arrangements pays those checks.

Use the genuine grade-four read $A c^{\odot3}$. On the first four actual coordinates solve for $P=\pi_0+\pi_1 c+\pi_2 c^2+\rho g$ matching $c^3$ (the four-by-four prefix is invertible in every candidate). At any of the first five rows, the lower triangular read of $A(c^3-P)$ is just $\gamma(c^3-P)$, because its predecessor differences are zero. The reads of $A1,Ac,Ac^2,Ag$ in $AP$ are known: $Ac=c^2/2+g$, and the grade-three pure remainders of $Ac^2$ and $Ag$ are affine multiples of $g$ with coefficients determined by their actual first two reads. This gives the first five actual values of $A c^{\odot3}$ without solving the unknown full tableau.

Next solve for an actual row $b^{\mathsf T}[H(C)+(\beta+\eta C)G]\in W_3$, $\deg H\le3$, vanishing on the last five physical sites. All its coefficients, including the literal weights, are computed from the known rows. It must pair with $A c^{\odot3}$ to give $I(HX^4/4)$ by the original grade budget $3+4=7$; it sees only the protected five values. The literal nonzero pair differences, in the order with the extra off-zero center at row 6 and then row 5, are:

| Characteristic | Ends | Fourth front clock | Two protected differences |
|---:|:---:|---:|---:|
| 965179 | A/A | 473960 | 327053, 372905 |
| 3535032504307 | A/A | 2304862098039 | 274684677964, 2883704798279 |
| 3489226706289835873 | A/A | 1101643917088851657 | 3184654386934665632, 559218082341581846 |
| 1439 | Z/Z | 1039 | 825, 1318 |
| 420941 | Z/Z | 204686 | 204773, 83426 |
| 48029 | Z/Z | 11446 | 45959, 7256 |
| 434112360658085729 | Z/Z | 116112499031277963 | 80272079603567541, 238261968342116336 |

These exact contradictions rule out an even centered quadratic trace over all paid fields. The same reconstruction certifies the four distinct predecessor clocks where needed, the side choices and the exact row order. It makes no claim about all-active graphs with a nonzero centered linear term.

## Replay and Lean scope

Run `python prime_certificates.py`, `python check_projection.py` and `python check_prefixes.py` with SymPy 1.14 and Python-flint 0.8 (the primality checker alone uses only the standard library). `RKCert.Research.SDIRKEightEvenQuadraticTrace` checks the three-site diagonal symmetry identity, the protected triangular diagonal read, and the explicit nonzero typed defect residues. The full rank reduction, resultants and finite projection are the exact source proof and independent replays above, not one end-to-end native `HasOrder` theorem. The attached native audit is from Lean/Mathlib 4.36.0.
