# Pure five-zero SDIRK8 with a silent third reverse stage

Let a strict ten-stage SDIRK tableau $A,\mathbf b$ of ordinary order at least eight over a field of characteristic zero or greater than seven have exactly five physical quadratic zeros. Write $\mathbf c=A\mathbf1$, $\mathbf g=A\mathbf c-\mathbf c^{\odot2}/2$, $C=\operatorname{diag}(\mathbf c)$, $G=\operatorname{diag}(\mathbf g)$, $U=\ker G$, and $\gamma\ne0$ for the common diagonal.

**Result.** In the pure-polynomial support chart, all five off-zero weights cannot vanish if physical stage 8 is silent. The [four-ordinary-site exclusion](../sdirk-eight-five-zero-pure-four-ordinary/README.md) covers that possible count; the new result below excludes the five-distinct-ordinary-site case with a silent stage 8 as well. A live stage 8, graph support, and genuinely live off-zero clocks are outside this theorem.

## 1. Actual outer chronology and the grade-four line

The [support-rank classification](../sdirk-eight-five-zero-support-rank/README.md) gives $d_2=1$ and two physical off-zero clocks in this chart. The supported trace is $r_{\mathrm{phys}}(X)=(X-\gamma)(X-\gamma(1+u))$, where the actual first two physical rows are off-zero and the third is zero. The [front endpoint argument](../sdirk-eight-five-zero-pure-four-ordinary/README.md) gives
$$
Q(u)=4u^3-12u^2+3u+2=0,\qquad c_3=\gamma(1+2u).
$$
Since all mass is on the five zero stages and the four-ordinary-site case is impossible, those five have distinct clocks and nonzero weights. Thus a silent physical stage 8 is off-zero. Stages 9 and 10 are live zero rows at distinct clocks, $c_{10}=1-\gamma$, and the [literal silent-eighth gate](../sdirk-eight-four-zero-gaussian-rear/README.md) gives
$$
v=(c_{10}-c_9)/\gamma,\qquad v^3-4v^2-v+2=0,\qquad c_8=2c_9-c_{10}.
$$
Here $v\ne0$ and $\kappa(v)\ne0$. The two possible physical off-zero clocks for stage 8 give the two guarded formulas
$$D=1/\gamma=2+2v\quad\hbox{or}\quad D=2+u+2v.$$

Normalize $T=X/\gamma$, $A'=A/\gamma$, and let $a=1+2u$, $h=D-1-v$, $s=D-1$ be the normalized clocks of stages 3, 9, 10. The supported quadratic trace becomes $r(T)=(T-1)(T-1-u)$, after nonzero rescaling. The primitives below are polynomial operations, not analytic integration. We use $J$ from zero, and the scalar mean $I_D(T^j)=D^j/(j+1)$. Define
$$L(T)=70T^4-140DT^3+90D^2T^2-20D^3T+D^4.$$

The pure grade-three columns are clean on $U$ since $F_3=GE_1$ for two distinct off-zero clocks. Thus $A'_U r(\mathbf c_U/\gamma)=(Jr)(\mathbf c_U/\gamma)$. For the supported cubic $Tr$, its next primitive discrepancy lies in $F_4|_U$, which has dimension at most one because $GE_2$ has codimension one in $F_4$ and vanishes on $U$. The polynomial $L$ gives a vector in $F_4$, nonzero on $U$ because five distinct clocks cannot all be roots of a quartic. Hence $F_4|_U$ is its line. Moreover it is nonzero at the first zero $a$: the vector $M r_{\rm phys}(\mathbf c)\in F_4$ reads $-\gamma^2 r_{\rm phys}(c_3)\ne0$ there, since both strict predecessors are off-zero and both clocks differ from $c_3$. Therefore $L(a)\ne0$.

At the first zero the $Tr$ read is purely diagonal. At the next zero, of normalized clock $b$, any strict supported tap sees only the first zero. The two literal reads give the necessary relation without division by the tap:
$$
g(b)=0,\qquad
g(T)=L(a)[a(Jr)(T)-(J(Tr))(T)+(T-a)r(T)]
       -L(T)[a r(a)-(J(Tr))(a)].
$$
All indices remain physical: a silent stage between these zero rows contributes nothing to either supported input.

## 2. Moment determinant and guarded elimination

The two as-yet-unknown interior live zero clocks are the roots of $T^2+kT+q$. For $P=(T-a)(T-h)(T-s)$, let $m_i=I_D(T^iP)$ for $0\le i\le4$. Ordinary quadrature through degree seven forces
$$m_i q+m_{i+1}k+m_{i+2}=0\quad (i=0,1,2).$$
In particular the symmetric $3\times3$ Hankel determinant $H_m=\det(m_{i+j})_{i,j=0}^2$ vanishes. If $\Delta=m_0m_2-m_1^2\ne0$, the cleared interior equation is
$$
F_2(T)=\Delta T^2+(m_1m_2-m_0m_3)T+(m_1m_3-m_2^2)=0.
$$
It must have a common root with $g(T)$. The zero pivot is kept separate; it is not excluded by an unjustified division.

For each diagonal denominator, calculate norms by successive ordinary resultants against the *monic* gap cubics $Q/4$ and $v^3-4v^2-v+2$. All rational coefficients, including the primitive and moment denominators, are paid. Direct calculation gives:

| $D$ | Gcd after paid factors: norms of $H_m$ and $\operatorname{Res}_T(F_2,g)$ | Gcd after paid factors: norms of $H_m$ and $\Delta$ |
| --- | ---: | ---: |
| $2+2v$ | $17$ | $1$ |
| $2+u+2v$ | $62753^6$ | $62753^2$ |

The norms are nonzero rational numbers, excluding characteristic zero. Each candidate pair is handled in the complete splitting field of both cubics, with extension degree doubled to split any possible interior quadratic. Thus the parameter projections are valid on the full algebraic closure, not only on prime-field roots. The two resulting primes are verified by trial division.

## 3. Complete finite fibers and rank drop

At 17 in the first denominator chart, there are exactly two moment-zero gap pairs. They have $u=16$ and the two roots of $v^2+2v-6=0$ for $v$. Both have $\Delta=9$ and their two interior normalized clocks are $1$ and $D+1$. Neither can be the first interior clock: the exact cleared gate values are
$$12g(1)=2v+2,\qquad 12g(D+1)=-6v-6.$$
They are nonzero because $(v+1)^2=7$. This handles both chronologies without guessing an ordering of the algebraic roots.

At 62753 in the second denominator chart, there is a unique moment-zero pair $(u,v)=(55124,35190)$ across the full two-cubic splitting field. It is precisely the singular Cramer case, with moments $(57172,0,0,0,0)$. Here $D=2+55124+2\cdot35190=2\cdot62753=0$, impossible since $D=1/\gamma$. Thus the rank drop does not create a free interior family for an actual tableau. There are no remaining paid-field cases.

## 4. Replay

Run `python check_norms.py` and `python check_fibers.py` with SymPy 1.14 and Python-flint 0.8. The former checks every rational denominator and the exact resultant gcds; the latter checks complete cubics and both inner orders, and includes the literal singular denominator guard. `RKCert.Research.SDIRKEightFiveZeroPureSilentEighth` verifies the supported second-zero elimination, the nonzero quadratic-root test, and the literal singular denominator calculation. It does not claim native rooted ingress or symbolic resultants. Stock Lean/Mathlib 4.36.0 audit attached.
