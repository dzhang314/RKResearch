# DIRK10/11: eight active dirty clocks are impossible in characteristic zero

This strengthens the separate eight-label endpoint census, not the
unrestricted stage lower bound. Let $r=\#\{c_i:b_i g_i\ne0\}$ count
distinct numerical clock labels of individually active dirty stages,
where $g=Ac^2-c^3/3$. The $r=8$ branch is impossible over every
order-ten field except possibly characteristics **137, 62969, 112249**.
There is no ordering, positivity, real-closed, or analytic assumption.
Smaller $r$ remain, so the unrestricted 11–12 interval is unchanged.
Indices in this note are 1-based.

## Paid ranks and exact evaluation at the three clean sites

Use the preceding eight-label census: there are eight active dirty
rows with distinct clocks and exactly three clean rows at $0,y,1$,
all eleven individual weights are nonzero, and
$$
 g_i=U(c_i)\quad\text{on the dirty rows},\qquad
 (x-y)U(x)=u J_4(x),\qquad
 J_4=x^4-2x^3+4x^2/3-x/3+1/42,
$$
where $u\ne0$. The quartic condition is $42\rho^2-14\rho+1=0$
for $\rho=y(1-y)$, which ensures $y\ne0,1$ and $J_4'(y)\ne0$
in every paid field. Thus $h=U(c)-g$ is supported on the three
clean sites, nonzero at each. Their indicators are $h$ times
polynomials of degree at most two and belong to $E_5$.

The native ranks are $\dim E_3=5,\dim E_4=7,\dim E_5=9,
\dim F_5=3$ (filtered stages and defects; the grade of $c$ is one).
For $e=3,4,5$, $E_e$ is spanned by clock polynomials of degree
at most $e$ and $C^j h$ for $0\le j\le e-3$. Independence follows
by evaluation on the eight distinct dirty nodes and three clean
nodes. A column in $E_e$ has a unique formal scalar profile of
degree at most $e$: if the column is zero, the scalar has value
zero at the true physical origin, and its five paid clock tests
force it to be zero by the anchored Beta matrix. The basis
columns and their profiles agree at all clean sites, hence so
do all true $E_e$ columns.

The eight-label branch **itself** forces $\dim E_6=10$. The three
clean indicators together with seven clock columns of degrees
0 through 6 are independent. Also $Bg$ is a nonzero annihilator
of $E_6$ by paid grade $3+6=9$, with $B=\operatorname{diag}(b)$.
The true reflected cubic defect divided by the weights is
therefore proportional to $g$: its weighted row annihilates
$E_6$ and is nonzero at the last active nonterminal clock by
$D(2)$ and the triangular single-pivot test. No external
grade-six surplus is needed.

Write $A^*=B^{-1}A^TB$, $C=\operatorname{diag}(c)$, and
$R=CA-AC-A^2$. This does not assume that the transposed tableau
is itself an order-ten method. Forward Volterra closure gives
$R(E_3)\subset F_5=g\mathcal P_2(c)$, the last equality by the
three independent paid defects $g,Cg,C^2g$. In the pairing
$\langle a,v\rangle_B=\sum_i b_i a_iv_i$, $R^*E_3$ annihilates
$E_4$ by $R(E_4)\subset F_6$ and grade $3+6=9$. Its last
component is zero since $R$'s last column is zero. The terminal
indicator is not in $E_4$: a clock polynomial of degree at most
four vanishing at eight distinct dirty clocks is zero, while an
affine multiple of $h$ cannot isolate the terminal from two
other distinct clean clocks. Thus the terminal-zero constraint
reduces the four-dimensional weighted annihilator to dimension
three. It contains $g,Cg,C^2g$, proving
$R^*(E_3)\subset g\mathcal P_2(c)$.

For any true $E_e$ column $w$ of profile $Q$, $e=3,4$,
$$
 A^*w-(JQ)(c)\in \operatorname{Ann}_B E_{8-e},
 \qquad JQ(x)=\int_x^1 Q(t)\,dt .
$$
Test on $v\in E_{8-e}$, pay $e+(8-e)+1=9$ in
$\langle w,Av\rangle_B$, and use formal integration by parts.
The difference is zero at the terminal. For $e=3$ the
annihilator of $E_5$ is exactly $g\mathcal P_1(c)$; for $e=4$
its terminal-zero analogue is $g\mathcal P_2(c)$ as above.
Thus $A^*w$ has genuine grade at most $e+1$ and formal profile
$JQ$, with exact clean-site evaluation.

At the sole clean interior row, $A(Ch)$ gives
$$
 d=\frac{\int_0^y xU(x)\,dx}{yU(y)}=\frac{5+42\rho}{120},
$$
since its exact grade-five profile can be read at that row and
only its own diagonal can act there on $Ch$. Likewise the
indicator $C(1-C)h/[y(1-y)U(y)]\in E_5$ gives the exact middle
weight $b_y=7(1+6\rho)/60$. Substitute $U/u=J_4/(x-y)$ for these
formulas. If $d=0$, the quadratic equation at $\rho=-5/42$ gives
$137=0$. We keep that characteristic as exceptional.

## The forced overlap is exactly stages 5, 6, 7

Let $H_F$ be the monic cubic vanishing on the first three dirty
clocks in physical order, and put
$$
 P=H_F-H_F(0)U/U(0),\qquad v=P(c)+[H_F(0)/U(0)]g.
$$
Then $v$ vanishes at the origin and its dirty values are $H_F$.
The profile $P\ne0$ since $U$ does not vanish at a dirty clock.
If the clean interior site precedes the fourth dirty site, its
$v$ value must vanish: all previous inputs are zero, $(Rv)_k=0$
by the clean rule, and $R_{kk}=-d^2\ne0$. By causality $Rv$
therefore vanishes on the first three dirty rows. Its density
in $g\mathcal P_2$ is zero at these three distinct clocks, so
$Rv=0$. The first nonzero entry of $v$ is exactly at the fourth
dirty row.

Similarly $H_B$ vanishes on the last three dirty clocks;
$Q=H_B-H_B(1)U/U(1)\ne0$ and $w=Q(c)+[H_B(1)/U(1)]g$ has
its last nonzero entry at the fifth dirty row, with $R^*w=0$.
The weighted row $\lambda=w^TB$ is the genuine reverse cubic
kernel since the reflected defect is proportional to $g$ and
$Q(1)=0$. These specific kernels have zero diagonal pivots.
The reviewed adjacent-pivot contradiction applies to this pair.
The fourth and fifth dirty rows would be adjacent unless
separated by the unique clean interior row. Thus these are
stages 5 and 7, with the clean site at stage 6. The gap-two test
gives live neighboring taps and distinct clocks, though neither
extra conclusion is needed below.

## Second primitive, one middle site

Use formal antiderivatives $IP(x)=\int_0^x P$ and
$JQ(x)=\int_x^1 Q$, and set $F=IP$ and $G=JQ$. These have
degrees at most four and are divisible by $x^2$ and $(1-x)^2$.
The exact clean-site evaluations of $Av,A^*w$ are $F(y),G(y)$.
Stage 5 has diagonal zero and no preceding $v$, so $(Av)_5=0$
and $(A^2v)_6=d(Av)_6$. Comparing with its grade-five profile
gives $(IF)(y)=dF(y)$. The exact reverse grade-five rule
similarly gives $(JG)(y)=dG(y)$.

Now $Av$ is supported from stage 6 onwards and $A^*w$ through
stage 6. Their overlap is the single clean row. The same is
true with $A^2v$ instead of $Av$. The three genuine paid reads
(grades $8,9,9$) are therefore
$$
 \int_0^1 FG=b_yF(y)G(y),\qquad
 \int_0^1 (x-y)FG=0,\qquad
 \int_0^1 (IF-dF)G=0.
$$
Here the third follows by comparing $\langle Av,A^*w\rangle_B$
and $\langle A^2v,A^*w\rangle_B$ on the sole overlapping row.
Equivalently $A^2$ factors through the one middle site on the
3-by-3 overlap, $ACA=y A^2$, and $A^3=d A^2$. These are
ordinary products of true stage columns with audited formal
profiles, not products of arbitrary marked rows.

## Exact scalar obstruction

A basis for the two-dimensional admissible space for $F$ is
$$
 F_0(x)=x^2(x-y)(5x-3y),\qquad
 F_1(x)=x^2[(4y-12d)x-(3y-12d)y].
$$
Both satisfy the local primitive constraint, with point values
$0,y^4$. The degree-four coefficient of $F_0$ is $5$. The
constraint on $x^2,x^3$ has at least one nonzero coefficient
because their primitive-to-point ratios $y/3,y/4$ differ.
Use the simultaneous $x\mapsto1-x,y\mapsto1-y$ reflections
for the $G$ basis. The four tensor entries are
$(a_0b_0,a_0b_1,a_1b_0,a_1b_1)$ for the two coefficient pairs.
This tensor is nonzero and rank one.

Multiply the scalar rows by $126000,252000,15120000$,
respectively, and reduce entries modulo $42\rho^2-14\rho+1$.
The accompanying exact script checks the moment entries.
The signed maximal-minor row, scaled by $49/75000$, is
$$
\begin{split}
 N_0&=3(95466y^2-95466y+21965),\\
 N_1&=30(93100y^3-93625y^2+21651y-166),\\
 N_2&=-30(93100y^3-185675y^2+113701y-20960),\\
 N_3&=200(11235y^2-11235y+2641).
\end{split}
$$
The cofactor vector satisfies
$$
 N_0N_3-N_1N_2=1250(2729314\rho-646271).
$$
If its linear factor vanished, the quadratic clock equation
would imply
$$
 2729314^2-14(2729314)(646271)+42(646271)^2
 =296864705802=2\cdot3\cdot7\cdot62969\cdot112249=0 .
$$
Outside the stated characteristics this cannot hold. Hence
the $3\times4$ system has rank three and its null line is
spanned by a rank-two, not rank-one, tensor. Contradiction.

All fixed denominators in the integrations, reductions, and
row scaling have prime factors only $2,3,5,7$, already excluded
by paid order ten. The three exceptional characteristics
are sufficient guards, not claims of feasibility.
