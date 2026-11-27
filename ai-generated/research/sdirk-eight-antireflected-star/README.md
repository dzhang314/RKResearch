# No opposite-residual reflected star at the ten-stage SDIRK8 floor

Over any characteristic-zero field, a ten-stage strict SDIRK tableau of ordinary order at least eight cannot simultaneously have:

1. Every literal quadratic stage residual $g_i=(A\mathbf c)_i-c_i^2/2$ nonzero.
2. Opposite-residual **chronological** reflection, $(c_{11-i},g_{11-i})=(1-c_i,-g_i)$ for every $i$.
3. A literal star in the first three rows, $a_{32}=0$ in one-based indexing.

This excludes the subclass over $\mathbb Q$, real algebraic fields, and the reals. It does not exclude a cross-fed opener, a symmetric set in a different chronology, other nonzero branches, or branches with zeros. The unconditional real-algebraic interval stays **10–11**.

## Reduction from the rooted-order flags

Use [the first-three-row identities](../clock-localized-tail/tied-stage-floor/FIRST-THREE-ROWS-AND-PHYSICAL-LEVEL-OBSTRUCTIONS.md) and [the simple complete intersection](../clock-localized-tail/tied-stage-floor/SIMPLE-LEGENDRE-COMPLETE-INTERSECTION-AND-WEIGHTS.md). Their ingredients here are nonsingular Volterra flags, the rational moment pairing with nonzero Hilbert determinant, and polynomial identities over characteristic zero. Divide $A,\mathbf c,\mathbf g$ by $\gamma,\gamma,\gamma^2$, respectively, for the nonzero common diagonal $\gamma$. The normalized interval is $[0,2m]$, with $m=1/(2\gamma)$. For $t=x-m$, $v=d^2$, and $k=2-v$, the only initial star has pairs
$$
 (x,g)=(1,1/2),\quad(2+d,k/2),\quad(2-d,k/2).
$$
Here $d\ne0$, $v\ne1$, and $k\ne0$. The stage set has ten distinct pairs. Chronological reflection sends $(t,g)$ to $(-t,-g)$, so no two first-five rows are in the same orbit.

The complete intersection has monic scalar traces $L_4(t)=t^4-6m^2t^2/7+3m^4/35$, $L_3(t)=t(t^2-3m^2/5)$. Uniqueness with the reflection signs gives
$$
 U=L_4(t)-g(A t+B g),\qquad V=L_3(t)-g(D+E t^2+Ftg).
$$
Here $BF\ne0$ by the coprime leading forms and the absence of a relation with $L_3$ trace in grade four. The $U$ equations at the three opener points, by difference and mean at $2\pm d$ and the value at 1, give
$$
 0=(v-1)[f_0(m)v+f_1(m)],\qquad
 \begin{aligned}
 f_0&=2m^4-20m^3+80m^2-140m+70,\\
 f_1&=14m^4-140m^3+420m^2-420m+105.
 \end{aligned}
$$
The replay checks coprimality, so $v=-f_1/f_0$. Let $\alpha=1-m,\ \beta=2-m,\ h_0=1/2,\ h=k/2,\ n=3m^2/5$. The analogous $V$ equations give $E C=C_h$ with
$$
 C=(\beta^2-v)+\alpha^2-2\beta h_0\alpha/h,\qquad
 C_h=\alpha(\alpha^2-n)/h_0+2\beta(\beta^2-v)/h-h_0\alpha(3\beta^2+v-n)/h^2.
$$
The three irreducible factors of the numerator of $C$ are exhausted as follows:
* A quadratic gives $C_h=0,\ v=3,\ k=-1,\ (2m-3)^2=3$. The mirror $(2m-1,-1/2)$ of row 1 is an earlier star leaf, impossible in this chronology.
* One quartic gives $C_h\ne0$, so there is no fit.
* The other quartic gives $v=1$, which the opener excludes.

## Fourth and fifth rows

Let $E_j$ be the evaluation space of polynomials with weights $1$ on $x$ and $2$ on $g$ and grade at most $j$. The true rooted profile of $A f$ for $\deg_{\rm w} f\le j$ is the zero-constant primitive $J f(x,0)$, up to $g E_{j-1}$. The first two actual rows determine the affine coefficients:
$$
 (A g)(x)=g[1+(x-1)/k],\qquad
 (A x^2)(x)-x^3/3=g[4/3+2(k+1)(x-1)/(3k)].
$$
The weight-two polynomial $f_2=g-(-x^2/2+2x-1)$ is zero on the first three rows. Triangularity with diagonal one gives $(A f_2)_4=(f_2)_4$. Using $A1=x$ and $Ax=x^2/2+g$ gives
$$
 D_4(x)g=N_4(x),\qquad D_4=2[4k-(k+4)(x-1)],\quad N_4=k(x^3-9x^2+18x-6).
$$
This condition is local to row 4, not an equation on all later points.

Let $w=t^2$, $L(w)=w^2-6m^2w/7+3m^4/35$, $D_0=B(D+Ew)-F A w$, $K_0=B(w-n)-F L(w)$. Every pair satisfies the linear pivot identity $gD_0(w)=tK_0(w)$, by combining $U,V$. The replay only divides by this pivot at checked nonzero values.

If $D_4=0$, then $N_4=0$ too. Their resultant has irreducible factors of degrees 4 and 12. The first gives $k=0$; the second has one common clock, an earlier clock where $D_0\ne0$, so the pivot repeats its exact earlier pair. Therefore substitute $g=N_4/D_4$ at row 4, clear denominators in $U,V$, and divide both by $(x-1)((x-2)^2-v)$. A fourth row cannot reuse an earlier clock here since $D_4$ determines its residual. Calling the resultant of the two quotients over $\mathbb Q(m)$ gives numerator factors of degrees 5,12,16,28. No division by either polynomial's leading coefficient is made. The exact checks are:

| Degree | Fourth-row result |
|---:|---|
| 5 | Its pair is an already-used opposite-reflection orbit. |
| 12 | $D_4=N_4=0$, already excluded. |
| 16 | Its pair is an already-used opposite-reflection orbit. |
| 28 | It is a new pair and the $E_2$ prefix has rank four. |

In the degree-28 field, $D\ne0$ forbids a centered pair. For $w\ne0$, a necessary orbit polynomial is
$$
 (w-n)D_0^2-K_0 D_0(D+Ew)-F w K_0^2.
$$
It has the three known opener heights $\alpha^2,(\beta\pm d)^2$ and a monic residual quadratic. The check verifies distinct, nonzero heights and coprimality with $D_0$. Thus the other residual quadratic root is the forced fifth height $w_5$. Its two signed pairs have $x=m+T,\ g=T K_0(w_5)/D_0(w_5)$ with $T^2=w_5$.

For each $H=x^3,xg$, subtract the unique $h\in E_2$ matching $H$ at the first four rows. Write $f=H-h$. The actual relation $A f=Jf+g q$ with $q\in E_2$ forces the four chronological prefix values of $q$ and hence fixes it. At row 5 the diagonal would require $f=Jf+gq$. Each discrepancy has the form $A_0+T B_0$, and both **exact norms** $A_0^2-w_5 B_0^2$ are nonzero. Neither sign can satisfy the row-5 gate in any extension of the rational quotient field. In particular no assumption about which roots are real was used. Every possible parameter $m$ is algebraic by the resultant, so the proof extends even to characteristic-zero fields containing other transcendental coefficients.

## Replay and formalization

Run `PYTHONDONTWRITEBYTECODE=1 SYMPY_GROUND_TYPES=flint python check_star.py` with SymPy 1.14 and Python-flint 0.8. It reconstructs the exact rational functions, divides and factors the resultants, and checks every quotient-field guard and the two norms. `arithmetic.py` uses rational polynomial Euclid and exact arithmetic in the algebra $T^2=w$, not a numerical solver.

`RKCert.Research.SDIRKEightAntireflectedStar` formalizes the scalar identities for the star fit, fourth-row recovery, residual projection, exceptional reflected opener, and norm guard. It was typechecked on Lean 4.36.0 with pinned Mathlib. The elimination and bridge to existing rooted-order flags are the paper proof and exact replay above, not a native `HasOrder` exclusion theorem.
