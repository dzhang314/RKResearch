# Four quadratic zeros: the first clean row cannot be physical 5 in the canceled-clock case

Let $A,\mathbf b$ be a strict ten-stage SDIRK tableau of ordinary order at least eight over a paid field (characteristic zero or greater than seven). Its common diagonal is $\gamma\ne0$, its clocks are $\mathbf c=A\mathbf1$, and the physical quadratic defects are $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$. Suppose exactly four physical residuals are zero. The [preceding characteristic census](../sdirk-eight-four-zero-gaussian-rear/README.md) leaves no characteristic-zero case, and only the stated positive-characteristic controls. All four zero rows are live and have the four distinct Gaussian clocks. The degree-two support is zero, $E_2\cap\ker G=0$ for $G=\operatorname{diag}(\mathbf g)$, and $F_3=GE_1$, $F_4=GE_2$ are clean at all four zeros.

**New result.** Suppose there is one active off-zero clock $d$ and its off-zero aggregate is zero. Then the zero rows must be **physical 6, 7, 8, 9**, and the only two active off-zero stages are one among rows 2–5 and terminal row 10. Their $(c,g)$ pairs coincide and their weights are opposite. The same calculation also excludes the no-active-off-zero chart with zero rows 5, 6, 9, 10 and a silent row 8. Other placements in the no-active-off-zero chart are not addressed here. No numerical stage bound changes.

## 1. The fourth-row primitive gate and the first clean read

Work with normalized $A'=A/\gamma$, $\mathbf x=\mathbf c/\gamma$, and $\boldsymbol\eta=\mathbf g/\gamma^2$. Let $u=x_2-1$, $\kappa=1+2u-u^2$. The first three literal clocks are distinct, and they are off-zero, so $\kappa\ne0$. The star phase has $x_3=3-u$, zero strict tap into row 3 from row 2, and $u\notin\{0,1,2\}$. The arithmetic phase has $x_3=1+2u$, normalized adjacent tap $2u(3u-2)/H$ and $H=-2+u+4u^2-u^3\ne0$. Its tap and third residual are nonzero. These are the [literal first-three identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md), with all paid guards retained.

Let $P$ be the normalized quadratic defect interpolator on the first three clocks, $R(X)=\prod_{i=1}^3(X-x_i)$, and write $J f(X)=\int_0^Xf(t)\,dt$ for the polynomial primitive. If the fifth row is the first zero at normalized clock $a$, the [two exact first-clean reads](../sdirk-eight-four-zero-low-support-active-clock/README.md) and the clean read on $R(\mathbf x)$ give
$$
D=P(a)-JP(a)=A'_{54}(\eta_4-P(x_4)),\quad
N=aP(a)-J(XP)(a)=x_4D,\quad
B=JR(a)-R(a)=A'_{54}R(x_4).
$$
From the literal degree-three identities,
$$
A'\boldsymbol\eta=\bigl[1+(\mathbf x-\mathbf1)/\kappa\bigr]\odot\boldsymbol\eta,\quad
A'\mathbf x^{\odot2}=\mathbf x^{\odot3}/3+\lambda(\mathbf x)\odot\boldsymbol\eta,\quad
\lambda(s)=4/3+\frac{2(\kappa+1)(s-1)}{3\kappa}.
$$
The first identity is the pure residual transition. For the second, $F_3=\langle\boldsymbol\eta,\mathbf x\odot\boldsymbol\eta\rangle$ and its affine coefficient is read at the first two physical rows. In row 4, all strict donors have $\eta_i=P(x_i)$ because $i<4$. Therefore its $A'\boldsymbol\eta$ read gives
$$
\sigma\eta_4=\rho,\qquad
\sigma=-\frac{x_4-1}{\kappa}+P_1+P_2\lambda(x_4),\qquad
\rho=P(x_4)-JP(x_4),
$$
where $P_j$ are the polynomial coefficients. Eliminate the literal tap and residual without dividing by $\sigma$ or $B$:
$$
\mathcal G=B\,[\rho-\sigma P(x_4)]-D\sigma R(x_4)=0.\tag{1}
$$

The symbolic tests can use the interpolator $P=\widetilde P/H$. For the star phase set $H=1$, $j=0$; for the arithmetic phase use $H$ above and $j=3u-2$. In both cases
$$
\widetilde P=H(X-X^2/2)+j(X-1)(X-1-u).
$$
This follows by checking the first three normalized residuals, including the actual adjacent tap in the arithmetic phase. Clearing $H$ introduces no roots with $H=0$ into the allowed chart. All univariate gcd calculations remove roots only through the displayed literal guards: $u=0$, $\kappa=0$, and either $u=1,2$ (star) or $H=0$, $3u-2=0$, or zero literal third residual (arithmetic).

The preceding census fixes the five possible characteristics and reflects the necessary two rear Gauss roots $c_8,c_9$, with $c_{10}=d$. Stage 1 is silent since $\gamma\ne d$. When a live off-zero row lies at stage 2 or 3, its known clock $d/\gamma$ pins $u$ for either front phase, and $a$ is one of the two remaining Gaussian clocks divided by $\gamma$. At all 48 exact possibilities, $D\ne0$ and (1) fails at $x_4=N/D$. This excludes either early active position whether or not stage 4 is live. If stage 4 is live instead, $x_4=d/\gamma$ is fixed and $u$ is not. In each of the 28 geometric charts use at once $x_4D=N$ and (1), after clearing only paid denominators and the guarded $H,\kappa$. The univariate gcd is constant after removing forbidden roots. The factor calculation tests arbitrary extensions of the Gaussian control field. Thus if the first zero is physical 5, then the first four weights are all zero.

## 2. A second consecutive clean read

For the rest of the first-clean-fifth proof, test $D=N=0$ first. Exact univariate gcds leave no permitted root in any chart used below. Thus $D\ne0$ and $x_4=N/D$; the paid tap equation also ensures $\eta_4-P(x_4)\ne0$. Write $\mathbf q=\boldsymbol\eta-P(\mathbf x)$; it vanishes at the first three rows. Use the two columns in $E_3$
$$
\mathbf V_1=R(\mathbf x)-(B/D)\mathbf q,\qquad
\mathbf V_2=(\mathbf x-x_4\mathbf1)\odot\mathbf q.
$$
They vanish on the first four rows because $A'_{54}R(x_4)=B$ and $A'_{54}q_4=D$. Their scalar traces are $r_1=R+(B/D)P$ and $r_2=(x_4-X)P$. At each Gaussian zero they equal those scalar evaluations. The column
$$\mathbf v=r_2(a)\mathbf V_1-r_1(a)\mathbf V_2$$
therefore vanishes on the first five rows, with scalar cubic trace $s=r_2(a)r_1-r_1(a)r_2$. A consecutive clean sixth row at normalized clock $b$ must satisfy $(Js-s)(b)=0$, by its diagonal read of $\mathbf v$. This inference is valid even if both coefficients used to form $\mathbf v$ vanish. Simultaneous gcds with (1) by themselves exclude all 28 canceled-clock charts, and all 12 no-active-off-zero charts having a silent row 8 and live Gaussian zeros 5, 6, 9, 10. The normalization uses only the guarded $D,H,\kappa$ and paid factors.

## 3. A live off-zero sixth row

In the canceled-clock case there is exactly one off-zero row among 5, 6, 7, since stages 8, 9 are Gaussian zeros and stage 10 is off-zero. If row 5 is zero then, since the first four weights are silent, that one off-zero row must be active to cancel the nonzero terminal weight. The consecutive-clean exclusion places it at row 6. Its clock is fixed at $x_6=d/\gamma$. This remaining case has an additional exact test at the nonzero value $\eta_6$.

Use $\mathbf v$ from the previous section. It vanishes on the first five actual coordinates, so $A'\mathbf v$ does too and the row-6 action is purely diagonal. The two pure grade-four vectors
$$ A'\mathbf v-(Js)(\mathbf x),\qquad L(\gamma\mathbf x) $$
belong to $F_4=GE_2$. Here $L(c)=70c^4-140c^3+90c^2-20c+1$; its scalar order moments against degree at most three vanish, so the second vector is pure. The first four evaluations of $\mathbf 1,\mathbf x,\mathbf x^{\odot2},\boldsymbol\eta$ are invertible: the first three scalar clocks are distinct, and the missing pivot is $\eta_4-P(x_4)\ne0$. All four residuals are nonzero. Hence we may recover each degree-two trace-plus-residual polynomial of these pure vectors by dividing its first four values by $\eta_i$, then interpolating. Those values before division are $-(Js)(x_i)$ and $L(\gamma x_i)$ respectively. Thus the actual diagonal read and the Legendre evaluation at $x_6$ are two explicitly determined polynomials of degree at most two in unknown $\eta_6$.

More precisely, the first pure vector is $\boldsymbol\eta\odot[q(\mathbf x)+\beta\boldsymbol\eta]$ and the second is $\boldsymbol\eta\odot[\ell(\mathbf x)+\mu\boldsymbol\eta]$ with $\deg q,\ell\le2$. If the column $\mathbf v$ has the representation $s(\mathbf x)+m(\mathbf x)\odot\boldsymbol\eta$, the required scalar equations at $x_6$ are
$$
\beta \eta_6^2+[q(x_6)-m(x_6)]\eta_6+(Js-s)(x_6)=0,\qquad
\mu \eta_6^2+\ell(x_6)\eta_6-L(d)=0.
$$
At every admissible irreducible factor of the cleared opening equation (1), the exact degree-two gcd in the residue polynomial field is constant. Counts at $13,17,103,131,7793$ respectively are $28,14,15,36,15$ factors across the Gaussian controls and both opening phases. This includes two singular factors at characteristic 17 where $\sigma=\rho=0$: the independent cubic $B(\eta_4-P(x_4))=D R(x_4)$ has $B\ne0$, so it still recovers $\eta_4$ uniquely. Neither a free $\eta_4$ branch nor a singular $D=N=0$ branch is dropped. Factoring the opening polynomial over the entire Gaussian control field and taking a gcd over each resulting exact quotient proves the result in any higher algebraic extension as well.

## 4. Remaining chronology and verification

Every physical zero occurs at an index at least five, so the canceled-clock case must now start at exactly 6 and has zeros $6,7,8,9$. All its live off-zero residuals were shown in the preceding census to be the same. No repeated $(c,g)$ pair can occur in the first five rows: the first three clocks are distinct; a fourth equal pair would be a literal twin by three scalar primitive probes. Thereafter the first four $E_3$ evaluations are independent, using four scalar powers for different clocks or three powers and the residual when a clock repeats. All $E_4$ evaluations depend only on $(c,g)$ since $F_4=GE_2$. A fifth equal pair therefore has the same $A E_3$ reads and the row-merge argument with four independent predecessor evaluations produces an actual literal twin. Thus there is at most one active stage at the canceled pair among rows 1–5. There must be one to cancel row 10, and row 1 cannot be it. This proves the stated necessary structure; it does not construct or rule out the remaining pair.

Run `python check_pinned_early.py`, `python check_pinned_fourth.py`, `python check_consecutive_clean.py`, and `python check_live_sixth.py` with Python-flint 0.8. `RKCert.Research.SDIRKEightFourZeroFirstCleanFive` kernel-checks the two elimination identities and singular fourth-residual recovery over their stated structures. It does not formalize the full rooted-tableau and geometric ingress. The attached stock Lean/Mathlib 4.36.0 audit records the axioms.
