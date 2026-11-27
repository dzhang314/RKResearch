# A nonsymmetric repeated first clock: the reverse-star branch is empty

Assume a ten-stage strict SDIRK tableau over a characteristic-zero field has ordinary order at least eight, every quadratic residual nonzero, its first three physical rows the uniform midpoint triple, and its fourth physical clock equal to its first but with a different quadratic residual. If the chronological weighted adjoint starts with a nonuniform star (third strict tap from row two zero), this is impossible. The new result allows repeated clocks by design and does **not** assume reflection of the pair set or reflection of the chronology. It does not exclude a cross-fed nonuniform reverse opener, a later first departure, or a zero-containing method.

Use the [two-ended inverse design](../sdirk-eight-two-ended/README.md): normalize the common diagonal to one, write the endpoint as $2m=1/\gamma$, and use centered clock $t=x-m$. The initial uniform pairs at clocks $1,3,5$ have common residual $h=1/2$. The fourth is at clock 1 with residual $d\ne h,0$. The saturation flags give the simple two-coordinate complete intersection
$$
 U=L_4(t)-g(A(t)+Bg),\qquad V=L_3(t)-g(D(t)+F(t)g),
$$
with degrees in $t$ at most $2,3,1$ for $A,D,F$ and $B\ne0$. The reverse opener has pairs at $t_1=m-1$ and $t=b\pm\sqrt v$, $b=m-2$, with residuals $H$ and $g_R=H(2-v)$, respectively. Here $H,v,v-1,2-v$ are nonzero; swapping the two star leaves is permitted.

## Two scalar gates

Set $\beta=3-m$, so that at residual $h$ the quartic must be
$$
  U(t,h)=(t-\beta)((t-\beta)^2-4)(t+3\beta).
$$
Therefore $U(t,g)=L_4(t)-g[S(t)+B(g-h)]$, where $S(t)=2[L_4(t)-U(t,h)]$ is a known quadratic. At $t_0=1-m$, the two occupied distinct residuals exhaust the roots of the quadratic in $g$:
$$
 d=-2 L_4(t_0)/B.
$$

Let $P_3(t)=(t-\beta)((t-\beta)^2-4)$. The same argument with $V(t,h)$ gives some scalar $\lambda$ such that
$$
 V(t,g)=(1-g/h)L_3(t)+(g/h)\lambda P_3(t)-g(g-h)F(t).
$$
At the repeated clock $F(t_0)=-L_3(t_0)/(hd)$, so only the slope of $F$ and $\lambda$ remain. The actual reverse three pairs give a $3\times2$ linear fit in those unknowns; its augmented determinant must vanish.

On the regular reverse-star branch subtract the two leaf quartic equations, and use their mean and the terminal quartic equation. Writing $S_2$ for the quadratic coefficient and $a_2=-6m^2/7$, one obtains
$$
 g_R=\frac{4b(b^2+v)+2a_2 b}{S_1+2bS_2},\qquad
 J=\frac{\overline{L_4}/(2-v)-L_4(t_1)-H(\overline S-S(t_1))}{1-v},
 \quad B=J/H^2 .
$$
Bars are the arithmetic means at the two reverse leaves. The remaining un-subtracted constraint is $L_4(t_1)=H S(t_1)+J(1-h/H)$. Expressions `star_model.py` and `check_star.py` do these two eliminations symbolically over $\mathbb Q(m,v)$, removing only factors whose actual pivots are guarded nonzero. The two factors of the quartic constraint are each linear in $v$; their resultants with the four guarded quintic-fit factors lead to 15 distinct ordered factor cases over $\mathbb Q[m]$.

Four require invalid parameters, one requires zero terminal residual, four would give a third physical pair at the already exhausted first clock, and two give ordinary clock collisions where exact projection is singly valued. Three are the singular slope cases addressed below. There is exactly one remaining regular factor, degree eight with primitive constant term 69825. In that exact rational quotient field, the polynomial for the projection of the other eight points has eight allowed degrees and no second vertical clock. Divide by the five known nonvertical clock factors, leaving a cubic for the three noncorner pairs. The actual reflected fourth row has the normalized star gate
$$
 2[4k-(k+4)(y-1)]g_{\rm reflected}=k(y^3-9y^2+18y-6),
 \qquad k=2-v,\quad y=m-t .
$$
Substitute the exact one-valued projection for $g/(2H)$. Its polynomial is coprime to the residual cubic. Thus the reflected fourth remains impossible even over the algebraic closure of that coefficient field. The elimination has not used a real-root ordering or a numerical height bound.

## The exceptional leaf difference

The vanishing leaf slope $S_1+2bS_2$ factors into $m-2$ and $32m^2-224m+371$. Both must be treated since the two right leaves are actual distinct pairs.

* At $m=2$, the quartic is even in $t$, and the terminal clock is centered at $t=1$, already occupied at residual $h$. Thus the terminal residual equals $d$ (the second quartic root at $t=-1$). The two exact quintic reads at $t=\pm1$ give $F(t)=Ct$ with $hCd=3m^2/5-1$. Adding the right leaf quintic reads forces $\lambda(v-1)=0$, hence $\lambda=0$. At their common residual $g_R\ne h$, the remaining constraint is $v-n+(2-v)(n-1)=0$, $n=12/5$, forcing $v=1$. If $g_R=h$ instead, the two leaves must occupy roots $\pm1$ or $\pm3$ of $U(t,h)$. The first option is already forbidden; the second repeats the physical initial pair $(t,g)=(3,h)$.
* At the quadratic $32m^2-224m+371=0$, the leaf quartic difference gives $v=21/8$. Since $(2m-7)^2=v$, one reverse leaf is at the original clock 5, with residual $g_R\ne h$ there. Its quartic Vieta relation forces $B=-2L_4(5-m)/(H(2-v))$. The terminal quartic then fixes $H$ linearly. The two repeated clocks determine both coefficients of $F$ and the terminal quintic fixes $\lambda$. At the other reverse leaf the resulting quintic discrepancy is
$$
 \frac{140638940355589}{11280486751786} m-\frac{29055889337995}{805749053699},
$$
nonzero at both roots. `check_exceptional.py` uses exact arithmetic modulo that irreducible quadratic.

## Verification and remaining cross-fed case

Run `SYMPY_GROUND_TYPES=flint python check_star.py` and `python check_exceptional.py` with SymPy 1.14 and Python-flint 0.8. The assertion ledger identifies all 15 ordered factor cases and checks every guard, remaining degree and needed coprimality. The scalar specialization from quadratic/rational quotient fields is valid in every characteristic-zero extension.

`RKCert.Research.SDIRKEightRepeatedFirst` proves the terminal-corner linear subtraction, repeated-root Vieta identity, corresponding quintic linear pivot, and the two singular scalar identities. The rooted-order and elimination bridges are paper and exact replay, not a native `HasOrder` proof.

The separate finite appendix `finite_repeated.cpp` includes both reverse branches. In the arithmetic case or more generally write the three right residuals as $H(1,k,q)$ and divide the quartic readings by $1,k,q$. Subtracting the first right reading gives two linear equations in $H,J=H^2B$. The determinant-zero consistent cases are enumerated over the finite field as well. Test the original terminal residual, the distinct fourth Vieta root at clock 1, weighted leading forms and all eligible remaining pairs, then both causal fourth reads and graded chronology. `finite-prime-probes.log` records exact finite attempts at selected primes 43–1031; even the surviving ten-pair sets have no reverse-fourth placement. They do not replace the characteristic-zero proof and do not exclude cross-fed arithmetic reverse over untested fields.
