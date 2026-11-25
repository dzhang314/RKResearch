# Weak-four quartic: both first intervals contain three strict Q roots

2026-11-25. Exact sign-class extension of [the uniform crossing proof](01-crossing.md), independent of every diagonal, fixed physical fibre, and extra degree-12 test. Not compiled. The comparison references below are abstract positive measures (not trial values of an RK chart).

## Raw packet and normalization

The native roles are $a,c$, last and next-to-last physical contrast rows, and $d,h$, first and next-to-first, **all in the reflected numerical coordinate**. The four marks are distinct and different from 0 and 1. The actual source is `ERKOrder16WeakFourRemaining`, `WeakFourChronologicalPorts`, and `Width24RankThreeWeakMask.forward_prefix`, as detailed in the preceding note. In notation with $F=QZ$ monic of degree 8, the raw scalar laws are
$$
 \int_0^1 X F T=0\quad(\deg T\le6),
 \quad \int_0^a XQ=\int_0^a X^2Q=\int_0^c X(X-a)Q=0,
 \quad \int_d^1(1-X)Q=\int_d^1(1-X)^2Q=\int_h^1(1-X)(d-X)Q=0.
$$
The global law is before-weight degree 14, raw degree 15; local primitive tests are raw degree at most 6. There is a selected ordered extension in which all $F$ roots are simple, at most one is not strict unit, and $Q$ has at least three strict unit roots. Primitive positivity, rational bounds, and final clock inequalities do not depend on putting these selected roots in the base. The preceding note supplies the complete root/source proof, the crossing $d<a$, the auxiliary $J_7,J_8,K_7,L_7$ reference brackets, and the two-node reference test.

**Conclusion.** Both $(0,a)$ and $(d,1)$ contain at least three of the strict unit $Q$ roots. In particular, if four $Q$ roots are strict unit then $d<r_2<r_3<a$. If exactly three are strict unit then $d<r_1<r_2<r_3<a$ and $r_1<c,h<r_3$. The remainder is the true at-least-three-root crossed region, not a closed quartic branch.

Here is the complete case audit. Let $a>0,d<1$: in the sole-exterior-mark case the wrong-way first endpoint gives a signed definite polynomial on the wrong side of 0 or 1. Each first interval has at least two roots by the two-affine-test sign separator. To exclude exactly two on one side, it is enough to handle the original orientation $w=X$, and the reflected orientation $w=1-X$, where after replacing $X$ by $1-X$, the marks are relabeled
$$
(a,c,d,h)_{\text{new}}=(1-d,1-h,1-a,1-c)_{\text{old}} .
$$
The local tests have exactly the displayed form in the new orientation. The global law uses $w$ instead of $X$, and now the two possible exterior endpoint regimes are $e\le0$ or $e\ge1$, including equality when it is a $Q$ root. Reflecting does not require equal global densities.

## Comparisons used below

Use $t_i$ for the sorted strict-unit roots of $F$ (seven or eight). Let $u_j=r_j/a$ for the two $Q$ roots below a proposed exact-two left stop. The notation $S(s)$ means a positive-definite affine localizer at threshold $s$, making $u_1>s$; $B(s)$ means one positive affine direction, making $u_2>s$. For an exactly-two right stop apply the corresponding statement in right-reflected clock. Each evaluator is strictly contradicted by the displayed upper bound.

In the tables, a custom reference $(R,S)$ means density $Y(R-Y)(S-Y)$, with $R,S$ no larger than the normalized exterior factors, in order. When only one $R$ is displayed, the density is $Y(R-Y)$; use this when the other $Q$ root $e\le0$, since the missing factor $Y-e/a$ is positive and increasing. In both cases the actual/reference ratio is nondecreasing. The default two-factor $S(.2),S(.226)$ use $(1,1)$; the default $B(.55)$ uses $(1,1)$; $B(.72)$ with $(1.5,1.7)$, $S(.265)$ with $(1.14,1.36)$ were checked in the first note. All other positivity checks are below. Every finite decimal is exact.

For the **original** global density and eight interior roots, $K_{7,i-1}\le t_i\le L_{7,i}$ when indexed inside those displayed sequences, together with the all-node bound relative to the $J_8$ roots according to the sign of $\tau$ in $F=J_8+\tau J_7$. The upper bound for $t_1$ is $L_{7,1}$, and the lower bound for $t_8$ is $K_{7,7}$. For $e\ge1$ the seven nodes lie between $L_7,J_7$, and for $e\le0$ between $J_7,K_7$. For **reflected** global density, write $J'_n=(\text{reflected }J_n)$ as sorted root tuples and $K'_7=(\text{reflected }K_7)$. Orthogonality and the monic quasi-orthogonal pencil then give $L_{7,i-1}\le t_i\le K'_{7,i}$ for eight interior roots (and the same relative bound using $J'_8$ and the sign of its own pencil parameter). For a high exterior root the two envelopes are $K'_7,J'_7$. For a low exterior root they are $J'_7,L_7$. The Jacobi $L_7$ root tuple is reflection symmetric, either by coefficients directly or by orthogonality/monicity.

Two abstract intermediate references are used only to correlate rough exterior bounds. Let $M^+$ be the degree-seven orthogonal polynomial for $X(3/2-X)$, and $M^-$ for $X(X+1/40)$. They are computable at once as constant-positive multiples of
$$
 [J_8-J_8(e_0)J_7/J_7(e_0)]/(X-e_0)
$$
with $e_0=3/2,-1/40$, respectively, independent of actual marks. The seven interior roots increase in $e$ separately on $e\ge1$ and $e\le0$, by the increasing ratio of the two positive densities at fixed distinct parameters. The comparison only needs $M^+_2<.1722,\ M^+_5>.7193,\ M^-_2<.2191,\ M^-_5>.757$, verified below.

## Step 1: neither can both sides have exactly two

With four strict roots $r_1<r_2<r_3<r_4$, crossing and exactly two on both force $r_2<d<a<r_3$. If $c<a$, $r_1<c<r_2$; otherwise $c>r_3$. If $h>d$, $r_3<h<r_4$; otherwise $h<r_2$. The inward assertions follow by splitting a zero masked integral at its stop and using one sign change on each subinterval; the outward ones by the difference from the first port. Consequently, in the original coordinate:
- Eight interior and $m=\#\{c,h<a\}$ equal to 0: $r_1=t_1,a=t_4$, $u_1<.051/.399<.2$.
- $m=2$: $r_4=t_8,d=t_5$, right reflected small ratio $<.021/.318<.2$.
- $m=1$: $r_2=t_3,a=t_5$, $u_2<.319/.585<.55$.
- One high exterior mark, necessarily $c$: if $h>d$, $r_1=t_1,a=t_4$, $u_1<.057/.5<.2$; else $r_2=t_3,a=t_5$, $u_2<.353/.68155<.55$.
- One low exterior mark, necessarily $h$: if $c<a$, $r_4=t_7,d=t_4$ and right small ratio $<.023/.414<.2$; else $r_1=t_1,a=t_4$, $u_1<.089/.547<.2$.
Use the default comparisons.

With three strict roots the other $Q$ root is exterior to the open unit interval; all four marks are strict unit. Exact-two on both forces $r_1<d<r_2<a<r_3$. The inward/outward alternatives are $r_1<c<r_2$ or $c>r_3$, and $r_2<h<r_3$ or $h<r_1$. The dual-outward case was excluded independently in the first note. For the pairs (in,in), (in,out), (out,in), the bounds when $e\ge1$ are left small $<.057/.68155,\ .18025/.838,\ .057/.5$, respectively (thresholds $.2,.226,.2$); when $e\le0$ use right-small $<.023/.6,\ .023/.414,\ .115/.773$, respectively (all $.2$). The indices follow from the displayed ordering and the exact two inward intervals.

## Step 2: four strict Q roots, exactly two on left and at least three on right

The only possibilities are
$$
 \text{II: }r_1<d<r_2<a<r_3<r_4,\qquad
 \text{III: }d<r_1<r_2<a<r_3<r_4 .
$$
For II, $c$ is inward $(r_1,r_2)$ or above $r_3$; $h$ is inward $(r_2,r_4)$ or below $r_1$. A high exterior mark is necessarily $c$, a low exterior mark necessarily $h$. For III, $h$ must be inward in $(r_1,r_4)$ (no root below $d$ to permit an outward masked zero); a high exterior mark can only be $c$, a low one only $d$. An exterior $c<0$ or $h>1$ is impossible by the sign of the masked integral on the corresponding exterior stretch.

Two rank configurations recur when $w=X$:
- **Config A**: all-eight interior, $r_1=t_2,a=t_5,r_3\ge t_6,r_4\ge t_7$. If $\tau\ge0$, $u_1<.145/.585<.248,\ (U,V)>(.759/.629,.896/.629)>(1.2,1.42)$; use $S(.248)$ at $(1.2,1.42)$. If $\tau\le0$, $u_1<.162/.628<.258,\ (U,V)>(.785/.682,.908/.682)>(1.15,1.33)$; use $S(.258)$ at $(1.15,1.33)$.
- **Config B**: sole high exterior mark, $r_1=t_2,a=t_5,r_3=t_6,r_4=t_7$. At $e\le3/2$ the left small ratio is $<.1722/.68155<.253$; at $e\ge3/2$ it is $<.18025/.7193<.253$. Both ranges have $(U,V)>(.838/.735,.949/.735)>(1.14,1.29)$; use $S(.253)$ at $(1.14,1.29)$.

### Position II
For eight interior and $h$ inward, $r_1=t_1,a\ge t_4$: $u_1<.051/.399$ for $w=X$, or $<.021/.318$ for $w=1-X$; default $S(.2)$. If $h$ outward and $c$ inward: $r_1=t_2,a=t_6$; the original bound is $<.162/.759$, the reflected even sharper $<.104/.5$; default $S(.226)$. If both outward, $r_1=t_2,a=t_5,r_3=t_6,r_4\ge t_7$; Config A for original, or $u_1<.104/.5<.226$ reflected.

For one high exterior mark $c$, with $h$ inward use $r_1=t_1,a\ge t_4$: the original ratio is $<.057/.5$ and reflected $<.023/.414$, both below $.2$. With $h$ outward use Config B for original, or $u_1<.115/.600<.2$ reflected from $r_1=t_2,a=t_5$. For one low exterior mark $h$, $r_1=t_1,a\ge t_4$: original $<.089/.547$, reflected $<.051/.452$, both below $.2$.

### Position III
For eight interior, $d=t_1,r_1=t_2$. If $m=\#\{c,h<a\}$, then $a=t_{4+m}$. In case $m=0$, $r_2=t_3,r_3\ge t_5,r_4\ge t_7$; the last assertion uses $h<r_4$. Original, splitting at its pencil parameter zero, $u_2<.287/.399$ or $<.319/.454$, both below $.72$; $U>.585/.5\ge1.17,\ V>.896/.5>1.79$. Use $B(.72)$ at $(1.17,1.79)$. Reflected $u_2<.215/.318$ or $<.241/.371$, both below $.7$; $U>.5/.415>1.2,\ V>.838/.415>2$. Use $B(.7)$ at $(1.2,2)$. If $m=1$, use Config A for original. If $m=2$, original gives $u_1<.162/.759<.226$. For both $m=1,2$ reflected gives $u_1<.104/.5<.226$.

For one high exterior mark $c$, if $h>a$ then $r_2=t_3,a=t_4,r_3\ge t_5,r_4=t_7$. Original $u_2<.353/.5<.71,\ U>.68155/.548>1.24,\ V>.949/.548>1.73$, use $B(.71)$ at $(1.24,1.73)$. Reflected $u_2<.266/.414<.7,\ U>.600/.453>1.2,\ V>.911/.453>2$, use $B(.7)$ at $(1.2,2)$. If $h<a$, use Config B for original or $u_1<.115/.600<.2$ reflected from $r_1=t_2,a=t_5$.

For one low exterior mark $d$, $r_1=t_1,a\ge t_3$. Reflected $u_1<.051/.265<.2$. Original if $a\ge t_4$, $u_1<.089/.547<.2$. Otherwise $a=t_3,r_3\ge t_4,r_4\ge t_6$; $u_1<.089/.352<.253,\ U>.547/.4>1.36,\ V>.885/.4>2.2$; use $S(.253)$ at $(1.36,2.2)$.

## Step 3: three strict Q roots, exactly two on left and three on right

Now $d<r_1<r_2<a<r_3$, $r_1<h<r_3$, and $c$ is in $(r_1,r_2)$ or above $r_3$. All marks are strict unit. Always $d=t_1,r_1=t_2$. With $m=\#\{c,h<a\}$, $a=t_{4+m}$; if $m=0$ then $r_2=t_3,r_3=t_6$; if $m=1$ then $r_3\ge t_6$; if $m=2$, $r_3=t_7$. The remaining $Q$ root $e$ is outside the strict unit interval.

For **original global density, high exterior**:
- $m=0:\ u_2<.353/.5<.72,\ (U,V)>(.838/.548,1/.548)>(1.5,1.7)$; $B(.72)$ at $(1.5,1.7)$.
- $m=1:\ u_1<.18025/.68155<.265,\ (U,V)>(.838/.735,1/.735)>(1.14,1.36)$; $S(.265)$ at $(1.14,1.36)$.
- $m=2:\ u_1<.18025/.838<.226$; default.

For **original global density, low exterior**, use one-factor comparisons ($Y-e/a$ is positive increasing):
- $m=0:\ u_2<.4/.547<.74,\ U>.885/.586>1.5$; $B(.74)$ at $R=1.5$.
- $m=1:\ u_1<.2191/.734<.3$ for $e\le-1/40$, or $u_1<.227/.757<.3$ for $e\ge-1/40$ (intermediate $M^-$ bracket in the appropriate direction). $U>.885/.760>1.16$. Use $S(.3)$ at $R=1.16$.
- $m=2:\ u_1<.227/.885<.27$; $S(.27)$ at $R=1$.

For **reflected global density, high exterior**, $m=0$ gives $u_2<.266/.414<.7,\ (U,V)>(.773/.453,1/.453)>(1.2,2)$, use $B(.7)$ at $(1.2,2)$. For $m=1,2$, $u_1<.115/.600<.2$. For **reflected global density, low exterior**, $m=0$ gives $u_2<.319/.452<.72$, $B(.72)$ at $R=1$; otherwise $u_1<.162/.647<.27$, $S(.27)$ at $R=1$.

All cases with one side exactly-two are excluded. In the remaining three-strict-root case all marks are strict unit. No root remains between $a$ and $1$ or between 0 and $d$, so each secondary must be inward by its masked primitive, and the two splitting integrals require $r_1<c,h<r_3$. In the remaining four-strict-root case $r_3<a$ and $d<r_2$ are immediate. This is the precise phase reduction. It does not assert that a crossed packet exists.

## Additional exact checker

Run this independently with standard Python fractions after [the crossing bracket checker](checks/check_crossing.py). It checks the nondefault Gram tests and exterior reference brackets. Numerical ratio comparisons use strict upper quotients and weak lower quotients, because the numerator/denominator root brackets furnishing the actual lower quotients are already strict.

Run [`checks/check_first_root_count.py`](checks/check_first_root_count.py) with `python3`.


## Consequence: all four Q roots must be strict unit

This is a separate, short root-parity closure of the entire three-strict-root class; it uses no diagonal. Put $W=X(1-X)Q$. The reverse first pair gives $\int_0^a W=0$ by subtracting its $X^2$ test from its $X$ test; the forward first pair gives $\int_d^1 W=0$ by subtracting its $(1-X)^2$ test from its $(1-X)$ test. Add common interval parts to obtain
$$
\boxed{\int_0^d W=\int_a^1 W.}
$$
If $Q$ had three simple strict unit roots, the other root would be the only non-interior root of $F$, so all four actual marks would be strict unit. The count theorem just established gives $0<d<r_1<r_2<r_3<a<1$. The three strict $Q$ roots change the sign three times, so $Q$ has opposite strict signs on the two nonempty open tails; $X(1-X)>0$ on each. The actual finite positive affine rule, with raw degree 6, therefore makes the two tail integrals strictly opposite, contradiction. A possible fourth root $e=0$ changes nothing, since only open tails are used. Thus **every remaining quartic has four simple strict unit Q roots** and the actual first marks obey $d<r_2<r_3<a$. The argument does not rule out the remaining possibility of one exterior Z mark.

The same tail identity is valid for all orientations and all exterior labels. As a further simple consequence, if the high exterior mark is specifically $c>1$, then $r_3<a<r_4<c$ and $\int_a^c X(X-a)Q=0$ by the paid secondary plus the first masked difference. Let $k=(1-r_4)/(r_4-a)>0$. On $(a,1)$, $W-kX(X-a)Q$ is strictly negative apart from $r_4$: the factor difference is the sign of $(1-X)/(X-a)-k$, which decreases through zero at $r_4$, while $Q$ changes from negative to positive there. On $(1,c)$, $-kX(X-a)Q$ is strictly negative. Integrating and summing gives $\int_a^1 W<0$. The shared left tail is therefore negative, forcing $r_1<d$ (if $d<r_1$ it would be positive). So both first intervals contain exactly three roots in this exterior-secondary class. Reflect to obtain the corresponding statement for a sole $h<0$ (the argument uses only the local moments, so the reflected global density is irrelevant).
