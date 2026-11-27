# No uniform midpoint triple at either end of a ten-stage nowhere-zero SDIRK8 tableau

Let a ten-stage strict SDIRK tableau over a characteristic-zero field have ordinary order at least eight and no zero quadratic residuals. It **cannot** start with three uniform midpoint substeps. The same restriction holds at the other physical end, interpreted as the opener of the chronological weighted adjoint. Equivalently, in unscaled coordinates the second clock cannot be $3\gamma$, and the penultimate clock cannot be $1-3\gamma$, where $\gamma$ is the common diagonal. This is not a lower bound for arbitrary ten-stage tableaux; the real-algebraic unrestricted stage interval remains 10–11.

This packet closes the cross-fed reverse case of the [repeated-first-clock chart](../sdirk-eight-repeated-first/README.md), including the rank-deficient quartic fit. Its last step also removes the earlier literal assumption that the repeated pair occupies specifically row four.

## The sixth-corner reduction and the actual repeated pair

Normalize the common diagonal to 1 and the integration endpoint to $2m=1/\gamma$. Write $t=x-m$ for centered clocks, $g$ for the normalized quadratic residual, and $h=1/2$. The first three literal midpoint pairs are $(1,h),(3,h),(5,h)$ in uncentered coordinates. The [low-order pure flag](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) gives $Ag=xg$. Subtract $A(h1)=hx$, and at the first actual departure from $g=h$ the strict lower taps read only previous zeros of $g-h$. Thus that row has $g-h=x(g-h)$ and its clock is 1. There is a departure by the paid $\sum b_i=1,\ \sum b_i g_i=0$.

The [complete-intersection theorem](../clock-localized-tail/tied-stage-floor/SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md) says pairs are distinct and $U(t,h)$ is a monic quartic in $t$. Hence at most four pairs with $g=h$ can precede the departure. It is row 4 **or row 5**, and its pair $(1,d)$ with $d\ne h$ is independent of the first three and last three physical pairs. It can never be row 7, the reflected fourth. Both earlier star and double-uniform arguments still apply: the [reverse-star exclusion](../sdirk-eight-repeated-first/README.md) uses the repeated pair only in $U,V$ and in excluding recurrence of that pair at row 7, while the [double-midpoint exclusion](../sdirk-eight-double-midpoint/README.md) makes no assumption about its location. Thus it remains only to examine a nonuniform cross-fed reverse triple.

Let $\beta=3-m,\ t_0=1-m$, and
$$
 P_3(t)=(t-\beta)((t-\beta)^2-4),\quad
 S(t)=2[L_4(t)-P_3(t)(t+3\beta)] .
$$
Here $L_4$ and $L_3$ are the monic shifted Legendre polynomials in the centered coordinate for $[-m,m]$. The two equations must be
$$
 U=L_4(t)-g[S(t)+B(g-h)],\qquad
 V=(1-g/h)L_3(t)+(g/h)\lambda P_3(t)-g(g-h)F(t),
$$
where $F$ is affine and $B\ne0$. The repeated pair fixes $d=-2L_4(t_0)/B$ and $F(t_0)=-L_3(t_0)/(hd)$.

The reverse normalized clocks are $1,1+u,1+2u$ with residual ratios $1,k,q$. The actual right-end centered clocks are $t_i=m-1-i u$ ($i=0,1,2$), with residuals $H r_i$, $r=(1,k,q)$, $H=g_{10}$, and
$$
 k=1+2u-u^2,\quad
 r=\frac{2u(3u-2)}{-2+u+4u^2-u^3},\quad
 q=1+4u-4u^2+2ru.
$$
The strict cross feed has $r\ne0$; the nonuniform opposite end has $u\ne2$. All three residual ratios and $H$ are nonzero. Set $Y_i=L_4(t_i)/r_i$, $S_i=S(t_i)$, $J=H^2B$. Exact subtraction of the first terminal quartic equation from the other two gives
$$
 Y_i-Y_0=H(S_i-S_0)+J(r_i-1),\qquad i=1,2 .
$$
Write $\delta$ for this $2\times2$ determinant. Once its solution or a candidate $\delta=0$ scale is specified, the three actual $V$ equations give the $3\times2$ fit in $\lambda$ and the slope of $F$ described above, with an exact augmented determinant.

## Regular terminal fit: complete factor exhaustion

When $\delta\ne0$, solve linearly for $H,J$. The original un-subtracted equation $Y_0=HS_0+J(1-h/H)$ and the augmented determinant are rational expressions in $(m,u)$. Since a genuine method has all chart denominators and indicated scalar guards nonzero, factors supported on those guards can be discarded. The remaining guarded quartic numerator has bidegree $(12,15)$; the maximal quintic-fit factor has bidegree $(21,27)$, together with one $m$-only factor and one linear-$u$ factor. The resultant degrees in $m$ are respectively 15, 12 and 574. The complete archived rational factorization is reconstructed from these literal expressions by `arith_model.py`. All resultants are nonzero, so each surviving $m$ is algebraic.

The smaller rational factors are checked as follows. For each irreducible factor $p(m)$, work in its exact rational polynomial quotient field. Determine known bad divisors of the two specialized $u$ polynomials: a scalar guard fails, a third pair would occupy the already exhausted first clock, or two literal known corner pairs are identical. Both their clock **and** residual must agree for the latter rule. Using ordinary exact division, count the common bad divisors with multiplicity. An upper bound for the *entire* rational gcd degree is supplied by one good finite reduction of those two polynomials that preserves their degrees. Indeed the nullity of the Sylvester map equals the gcd degree, and cannot decrease on such specialization. The counted divisors exhaust that upper bound at every smaller factor. This reduction step does not try to reduce the candidate tableau or treat a modularly zero guard as an exactly zero guard. The exact divisions prove the bad branches before the modular degree bound is applied. The separate $m=1$ factor is impossible immediately: the terminal clock repeats the already occupied first clock, with no third available residual.

The single remaining factor has degree 172. At prime 43 its primitive leading coefficient survives, and it factors into degrees $2,3,5,60,102$. In each residue field:
* Both entrance polynomials preserve their leading degrees, so an algebraic entrance gap cannot reduce to projective infinity. Their specialized gcd is linear.
* All scalar pivots survive at the recovered gap, and the two remaining quintic coefficients are solved linearly. The projection $g=Q(t)/P(t)$ comes from canceling $g^2$ between $U,V$. The common factor $t-t_0$ of $P,Q$ accounts for the two distinct pairs at the first clock. After removing it, the polynomials are coprime, and the eight-clock projection has unit leading coefficient.
* Divide the eight-clock polynomial by its five known nonvertical physical clock factors, giving a cubic for the remaining clocks. Its gcd with the polynomial for the actual reflected fourth read is 1. The reflected fourth gate is obtained by applying the matrix to $g-T$, where $T$ interpolates the three literal reverse residuals, and using the common diagonal at its first new coordinate. Its arithmetic is literal in `check_dominant.py`.

This is characteristic-zero good reduction. An algebraic $m$ may be reduced at 43 because its primitive leading coefficient is a unit. In any extension place, the entrance gap must be finite by its preserved leading coefficients; then all recovered scalar data and the remaining clock polynomial have unit pivots. A genuine reflected fourth clock must be an integral root of that cubic at the place, so its reduction would give the forbidden shared root. This never assumes integrality of arbitrary tableau entries. The same reasoning applies to any characteristic-zero coefficient field containing the necessary algebraic subfield.

## Singular terminal fit: complete factor exhaustion

When $\delta=0$, consistency requires $(Y_1-Y_0)(q-1)-(Y_2-Y_0)(k-1)=0$. Their guarded numerators, after removing the excluded $u=0,2$, have degrees two and seven in $u$. Their exact resultant projects only to $m=2$ or one irreducible degree-27 factor. At $m=2$, the first condition specializes to $-23(3u-2)=0$, but $u=2/3$ is not cross-fed.

On the degree-27 factor, reduce at 43. The three residue factors of degrees $5,5,17$ all preserve their entrance leading degrees and give a unique linear gap. Since $k-1$ is nonzero in the nonuniform branch, solve for $J=J_0+J_1 H$ from the first subtraction. The original terminal quartic becomes the scale quadratic
$$
 (S_0+J_1)H^2+(J_0-hJ_1-Y_0)H-hJ_0=0.
$$
The leading coefficient survives in every residue field, hence $H$ cannot reduce to infinity. For the exact three-row quintic determinant use $d=-2L_4(t_0)H^2/J$ and the corresponding $F(t_0)$. Clear denominators and cancel the common nonzero $H$ from each row over characteristic zero before reducing. The actual polynomial and the terminal scale quadratic are coprime in every one of the three residue fields. `check_singular.py` verifies all these pivot and coprimality statements with exact arithmetic.

## Replay and formalization

With Python-flint 0.8 and SymPy 1.14, run `arith_model.py`, `check_dominant.py`, `check_small.py` and `check_singular.py`, preferably with `PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint`. The smaller-factor replay uses the adjacent reverse-star packet's `rational_field.py` and may take longer than the other scripts. The complete archive contains exact polynomial factors, not printed floating roots or a finite-height enumeration.

`RKCert.Research.SDIRKEightUniformOpener` formalizes the first-departure clock, five-point quartic obstruction, the resulting row-4-or-5 departure from uniform residual given the paid gate hypotheses, and the singular terminal quadratic. The algebraic factor and rooted-tableau bridge is proved by the exact replays and arguments above rather than a native end-to-end `HasOrder` theorem.
