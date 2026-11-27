# The final two six-site charts of the SDIRK9 twin-port family are impossible

This excludes both $(N,t,s_r)=(6,1,4)$ and $(6,2,5)$ at thirteen stages. Here $N$ counts distinct scalar nodes, $t$ counts old paid reverse terminal means, and $s_r$ counts old reverse stages. With the [six-site three-terminal](../real-sdirk9-six-site-three-terminal/README.md), [seven-site three-terminal](../real-sdirk9-seven-site-three-terminal/README.md) and [seven-site two-terminal](../real-sdirk9-seven-site-two-terminal/README.md) results, this closes the **entire specified regular twin-port, grouped, two-disjoint-literal-merge thirteen-stage family**. It is not a lower bound for unrestricted strict SDIRK9. No thirteen-stage method was constructed; the recorded real-algebraic interval remains 13–14.

The forward hypothesis is the six-row dense size-four return with two actual locally size-five pure rows, whose shifted decoder rows supply the two literal merges. Its size-five residual is the full three-dimensional space of degree-at-most-four polynomials vanishing at the two ports. The ports are from the regular cubic/quartic/cubic tower described in the [six-site three-terminal proof](../real-sdirk9-six-site-three-terminal/README.md#exact-reduction-covers-every-regular-port-conjugate). The reverse hypothesis is the grouped physical identity from the same proof, with the old return dense through word length two, exact old terminal means through length three, and one fresh representative at every remaining site. We permit signed physical shares, exterior sites, and repeated earlier physical occurrences within a site.

## Why these are the final possible counts

The physical count $6+s_r+(N-t)-2\le13$ is $s_r+N-t\le9$. The two-port forward mixed frame is injective on the $N-2$ non-port sites, with dimension three. Its annihilator thus has dimension $N-5$. For $t\le3$, at least $d=\max(0,t-(N-5))$ independent combinations of old terminal means become exact through length four: their next primitive discrepancies have rank at most $N-5$, and the next multiplication is already exact individually. The invertible commutator packet then requires $s_r\ge4+d$ (a top block of size $d$ and the lower blocks of sizes three and one). Also $s_r\ge t+2$: the length-three first-excess packet requires $6-\dim V$ old rows, where the actual cubic residual satisfies $\dim V\le4-t$.

The scalar moment rank requires $N\ge5$. At $N=5$ the node polynomial would lie in the shifted Legendre pencil $P_5+\eta P_4$. It would have to contain the two forward ports and the first reverse clock. In the normalized physical **forward** variable these are $\gamma v,\gamma w,1-\gamma$. The two cross-polynomials for this pencil have degree at most nine in $\gamma$ and have full degree and coprime reductions at $p=37,(v,w)=(3,19)$. This excludes the five-site case. If $t\ge4$, the old cubic residual would vanish at four distinct sites. A zero top residual would require a cubic return and would make all four old means pay the next primitive; the commutator packet then requires at least eight old rows. With two fresh protected representatives that exceeds the nine-row reverse budget. The inequalities for $N\ge6,t\le3$ leave precisely
$$
 (6,1,4),\quad(6,2,5),\quad(6,3,6),\quad(7,2,4),\quad(7,3,5).
$$
The last three were excluded in the linked packets.

## Actual primitive constraints in the last two counts

Use normalized physical reflected clocks $Y$ for the mixed discrepancy. Off the two ports there are four scalar sites. Any three coordinate rows of the mixed frame are independent (divide by the two nonzero port factors and use quadratic interpolation). Therefore its annihilator is a line with nonzero projection to **each** coordinate. For each old top residual $K\in V$, the weighted primitive discrepancies off the ports lie in that line. At any old terminal the discrepancy is a nonzero common scalar times $-(JK)(y)$, because its actual row of $S$ is a unit coordinate and $K(y)=0$. At the earliest live representative $r$, it is the same scalar times $-(J-\gamma I)K(r)$: protected fresh columns are unit columns of $S$, terminal $K$ values are zero, and there is no earlier live tap.

- **Single terminal, four old rows.** The equation at the earliest live site is proportional to the terminal primitive equation. It is an independent linear condition on the cubics vanishing at the terminal $t$: take $K=H'$ with $H=Y(Y-t)^2(Y-r)$ for $r\ne0$, or remove the factor $Y-r$ for $r=0$. In either case $K(t)=H(t)=0$ and $(J-\gamma I)K(r)\ne0$. Thus $\dim V\le2$, and the first-excess packet for four rows gives equality.
- **Two terminals, five old rows.** Neither old terminal can be at $Y=0$. At a zero terminal its primitive discrepancy vanishes, forcing the whole line of discrepancies to vanish at both terminals and refunding two exact length-four targets, which would cost six old rows. If $\dim V=2$, it fills all cubics vanishing at both terminals $t,u$. The two primitive tests on the quadratic hull and its first mark are independent: their determinant is $t^2u^2(t-u)^3/24$ up to sign. This violates the rank-one discrepancy restriction. Thus $\dim V=1$. Exactly one high combination $\mathbf m$ of the two old terminal means is paid through length four, and both coefficients in this combination are nonzero (a nonzero discrepancy line has nonzero entries at both terminal sites).

In unit-diagonal coordinates let $\Theta=CA-AC-A^2$, with $C$ diagonal on the actual clocks. It is invertible triangular and has formally zero polynomial action. The lower actual word span through length two is the four-dimensional frame
$$
 \mathbf 1,\quad\mathbf c,\quad\mathbf c^2,\quad
 \mathbf g=A\mathbf c-\mathbf c^2/2 .
$$
The full length-three pure span has dimension two in both cases. For the lower bound, $\Theta$ sends the independent length-one clock frame into pure errors. For the cap, the $4-\dim V$ linear functionals on cubics annihilating $V$ give that many independent actual length-three-exact covectors by composing with the decoder. They are independent even after restriction to quadratics: $V$ contains a polynomial with nonzero cubic term. Every such covector annihilates the actual pure span. The old row counts give the dimension two.

In the five-row case, physical old row five belongs to a terminal group. Otherwise $\mathbf m e_5=0$. Since $\mathbf m$ is high paid, $\ker\mathbf m=\Theta W_2$, where $W_2$ is the four-dimensional lower word span. The last old coordinate $e_5$ is a common right eigenvector of $A,C$ and $\Theta e_5=-e_5$; hence it would lie in $W_2$. Its polynomial model $P$ has degree at most two and vanishes at both nonzero terminal clocks. Both $(X-a_5)P$ and $(J-I)P$ then belong to the line $V$ by applying the actual clock and primitive eigenrelations. If $P\ne0$, comparison of leading coefficients makes
$$
 JP=\frac{X-a_5+m+1}{m+1}P,\qquad m=\deg P.
$$
Differentiating yields $P\propto(X-a_5+m+1)^m$, and the zero of $JP$ at zero forces $a_5=m+1$. Thus $P\propto X^m$, impossible at a nonzero terminal. If $P=0$, the actual $e_5$ would be in the pure lower line spanned by $\mathbf g$, impossible since $g_1=1/2$.

Because old row five is terminal, $\mathbf m e_5\ne0$, and $(\mathbf m\Theta)e_5=-\mathbf m e_5$ is also nonzero. The lower word span is the kernel of $\mathbf m\Theta$. Its projection to the first four coordinates is therefore an isomorphism. In the four-row case that lower frame is already full. This common paid first-four property rules out physically duplicate initial rows, in particular $a=1$ for the second old clock.

## Chronology reduces the terminal gate to three finite algebraic branches

A terminal group cannot be completed by the first two rows; if it is completed by row three, the [actual repeated-mean test](../real-sdirk9-seven-site-three-terminal/README.md#the-actual-first-four-reverse-rows-are-forced) forces the first three clocks
$$
 1,\quad a=(1+s_r)/2,\quad s_r,\qquad s_r^3-9s_r^2+18s_r-6=0.
$$
A six-site precision-eight rule cannot contain these clocks after scaling plus the two ports. With no protected collision among the early clocks, five distinct prescribed factors give three scalar affine equations in the sixth clock; two full-degree (degree ten) minors are coprime at good residues. With one collision, the pin fixes $\gamma$ and the two unassigned nodes give a quadratic factor. Its three moment equations have a nonsingular $3\times3$ Hankel matrix. Both nonterminal early clocks cannot coincide with the ports: it would express $w$ in $\mathbb Q(s_f,v,s_r)$, an extension of $\mathbb Q(s_f,v)$ of degree at most two, but $w$ has degree three. This excludes a **completed** row-three terminal, not an earlier occurrence repeated in a later mean. The first terminal is thus completed by old row four in both counts.

Write the first three old clocks as $1,a,b$ and the third-to-second strict tap as $u_3$. Let $\mathbf d=A\mathbf c^2-\mathbf c^3/3$ be the next monomial discrepancy. Both $\mathbf d$ and $A\mathbf g,C\mathbf g$ belong to the actual pure word span of length three. The precise remaining branches are as follows.

1. **$g_2\ne0$.** The independent $\mathbf g,C\mathbf g$ span the pure space. Comparison on the first two literal rows gives
   $$
     A\mathbf g=\mathbf g+(C-I)\mathbf g/(2g_2),
     \qquad \mathbf d=\tfrac23(A+C)\mathbf g.
   $$
   On row three, the second identity gives $u_3(a-1)(2a-b-1)=0$. If $u_3\ne0$, this is the regular arithmetic progression $b=2a-1$. If $u_3=0$, the first identity gives $g_3=g_2$, since $b\ne1$ (otherwise row three duplicates row one). Moreover $b\ne a$ by the same duplicate argument. For the two single-parent rows $g_j=2c_j-1-c_j^2/2$, so $b=4-a$. These are the sibling clocks.
2. **$g_2=0$.** The vector $A\mathbf g$ is nonzero on row two, whereas both $\mathbf g,C\mathbf g$ vanish there. Rank two forces $C\mathbf g=\mathbf g$ (use the first clock $1$ to determine the factor). Thus $a^2-4a+2=0$, and the pure space is spanned by $\mathbf g,A\mathbf g$; again $\mathbf d=\tfrac23(A\mathbf g+\mathbf g)$. If $b=1$, the third row comparison gives $u_3(2a-1)=0$, so it duplicates row one, impossible. If $b=a$, the clock and quadratic-defect values duplicate the second row in the full first-four lower frame, also impossible. Thus $g_3=0$. Eliminating the literal third tap from its two equations gives the exact factor
   $$
       (b^2-4b+2)(ab-5a-b+3)=0.
   $$
   Hence $b=4-a$ or $b=2a-1$, now with $a$ already fixed algebraically. This fixed triple is incompatible with a six-site rule: the zero-collision degree-ten minors and all six one-pin Hankel determinants are certified at $p=41,(s_f,v,w,a)=(30,3,18,19)$. The two-pin case would express $w$ in the degree-at-most-two adjunction of $a$. The $a$-quadratic is irreducible over the forward tower by good reduction at $p=37$.

For the sibling case from item 1, the first-three defect interpolant is $\widehat g(Y)=2Y-1-Y^2/2$. The row-four terminal's strict mean has support in the first three old rows even if it includes an older occurrence. Its actual response on the three distinct clock columns must equal $\mu_t=E_t(J-I)$, and it must kill the old defect. Consequently $\mu_t\widehat g=0$, so $t^3-9t^2+18t-6=0$. The complete scalar sieve includes $t=a$ or $t=b$ as a repeat, but never $t=1$. In the unpinned nonrepeat case the sibling pair contributes $Y^2-4\gamma Y+L$, with the one free product $L$. Three scalar affine equations on this coefficient give the degree-nine minors. In the pinned cases the proof uses, as appropriate, an affine extra node, a two-node quadratic Hankel determinant, or the rank-one constraint on the four cofactor entries for $(1,L,d,Ld)$ when the first clock is pinned and the last node is free. A terminal repeat fixes the middle clock parameters as $t,4-t$; if it coincides with two early pins, it would express $w$ in a quadratic adjunction. Both relative cubic-root classes are checked with exact residue pairs. None of these scalar gates assumes that a signed terminal is an individually pure stage when there is an earlier occurrence.

The remaining regular AP branch $g_2\ne0,b=2a-1$ is ruled out by the [p-adic compactification and exact 59-case replay](AP-COMPACTIFICATION.md). This eliminates all possible charts in the stated family.

## Reproduction and scope

With the six-site three-terminal packet alongside this directory:

    sha256sum -c sources.sha256
    PYTHONDONTWRITEBYTECODE=1 python3 check.py

The independent SymPy replay verifies the raw polynomial gates and number-field reductions, then checks the 13 full-degree Bézout pairs, 38 pinned or cofactor values and all 59 AP compactification/finite systems. The [native audit](../../lean/evidence/sdirk9-six-site-last-two-20261127/README.md) kernel-checks the emitted smaller coprimality and nonzero certificates on Lean 4.34.1, 4.35.0, 4.36.0 and 4.37.0-rc1. The AP Gröbner bases, actual tree-to-mixed reduction, and characteristic-zero compactness argument are recorded as independent exact arithmetic and mathematical proofs, not native Lean theorems.
