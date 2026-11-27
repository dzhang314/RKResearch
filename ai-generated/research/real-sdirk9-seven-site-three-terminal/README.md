# Seven sites and three paid terminals also fail at thirteen-stage SDIRK9

This excludes the two-disjoint-port grouped $(N,t,s_r)=(7,3,5)$ chart at thirteen stages, with the same six-row forward family as the [six-site exclusion](../real-sdirk9-six-site-three-terminal/README.md). The nominal count is $6+5+4-2=13$. The new part is a classification of the **actual** first four reverse rows, including all possible repeated-clock signed means, followed by a complete algebraic elimination of the site placements.

## The actual first four reverse rows are forced

Until the scalar test below, use unit-diagonal reverse coordinates. Let $A$ be the old five-row reverse primitive matrix and $\mathbf c=A\mathbf1$ its clocks. The first two rows have clocks $1,a$. For an actual normalized same-site mean $\mathbf m$ at $y$, exactness through word length three requires
$$
 \mathbf m(A-I)F(\mathbf c)=\mu_y F\quad(\deg F\le2),
 \qquad
 \mathbf m(A-I)\mathbf g=0,\qquad
 \mu_y=E_y(J-I),\quad
 \mathbf g=A\mathbf c-\mathbf c^2/2.
$$
Indeed the input profiles $1,Y,Y^2$ are literal clock words, and $\mathbf g$ is a length-two zero-density word. The primitive letter raises their lengths by one. These tests use the strict row of the actual group, not just its scalar clock. Exactness also kills the length-two defect $\mathbf m\mathbf g$.

The first two rows cannot individually pay length three. The first has $g_1=1/2$; the second, if its defect $g_2$ vanishes, has $(A\mathbf g)_2=(a-1)/2$, which could vanish only at $a=1$, where $g_2=1/2$. A mean of both early rows would require $a=1$, and then both rows are identical with nonzero quadratic defect. Thus each of the three terminal groups needs one of physical rows three, four and five, exactly one per group.

For the group containing row three, $\mathbf m(A-I)$ is supported in the first two coordinates. If $a=1$, its zero response on the two equal early defect values forces its total mass $y-1=0$; then its primitive condition on $Y$ fails. If $a\ne1$, test the polynomial $(Y-1)(Y-a)$, which vanishes on both read coordinates. A repeated group at $y=1$ would require $a=1/3$, and one at $y=a$ would require $a=0$ or $3$. None kills the actual early $\mathbf g=(1/2,2a-1-a^2/2)$:
- At $a=1/3,y=1$, the strict mass is zero, its first clock moment is $-1/2$, and the early defect values differ.
- At $a=y=0$, the unique two-coordinate strict row is $-e_2$, while $g_2=-1$.
- At $a=y=3$, the two early defect values are both $1/2$, and the strict mass is $2$.

Therefore row three is individually exact at a new clock $s_r$. If its second strict tap is $u$, put $m=s_r^2/2-2s_r+1$. The tests on $Y,Y^2,\mathbf g$ give
$$
 (a-1)u=m,\qquad
 (a+1)m=s_r^3/3-s_r^2-s_r+1,\qquad
 s_r-1+(3-a)m=0 .
$$
Here $m\ne0$, since $m=0$ would imply $s_r=1$, which gives $m=-1/2$. Elimination and substitution show
$$
 s_r^3-9s_r^2+18s_r-6=0,\qquad a=(1+s_r)/2.
$$

For the group containing row four, $\mathbf m(A-I)$ is supported in the first three coordinates. The moments on $1,Y,Y^2$ uniquely prescribe $\mu_y$ applied to their degree-two interpolant. The actual early defect interpolant is
$$
 \widehat g(Y)=\frac{3(Y-s_r)(Y-s_r/3)}{2(1-s_r)(3-s_r)}.
$$
Evaluating it at $1,a,s_r$ gives the three genuine defect values, using the cubic and the individually paid third row. The strict mean must annihilate it. The shifted primitive factors as a nonzero constant times
$$
 (y-s_r)\bigl(y^2-(s_r+3)y+s_r\bigr).
$$
The row-four group cannot have the earlier terminal clock $s_r$. The quadratic is $-2$ at $1$ and $-((s_r+1)^2+4)/4$ at $a$; thus signed repeated means at either early clock do not work. Row four is individually exact at one root $t_r$ of this quadratic. The fifth group may repeat $1$ or $a$, so the elimination below permits either possibility without treating those clocks as new.

## Two causal primitive gates, not just scalar quadrature

Write $Y$ for the normalized physical reflected variable on $[0,1]$ and $\gamma$ for the common diagonal. The two protected sites are $1-\gamma v,1-\gamma w$, and the three terminal sites are $\gamma s_r,\gamma t_r,u$. Let $b_1,b_2$ be the earlier and later unprotected fresh representatives in reverse chronology. The genuine top reverse residual is the line of the terminal monic cubic
$$
 K(Y)=(Y-\gamma s_r)(Y-\gamma t_r)(Y-u).
$$
It is nonzero because the lower return has degree at most two, while a length-three clock word has nonzero cubic density.

The two protected physical columns have no strict later taps. Testing the actual grouped row identity on either protected representative coordinate therefore makes its column of $S$ the corresponding unit coordinate, since that fresh coordinate has nonzero share and the decoder only uses the old reverse rows. Inputs at the three terminal sites have $K=0$. Thus the only possibly relevant strict tap between nonterminal sites goes into the later live row $b_2$. Put
$$
 G(Y)=(Y-(1-\gamma v))(Y-(1-\gamma w))(Y-b_2).
$$
Both $G$ and $YG$ lie in the exact forward size-five mixed test space after reflection. They kill that last tap as well as the protected output rows. The actual rooted bridge proof in the six-site packet now gives
$$
 \mathcal I(Y^j G(J-\gamma I)K)=0,\qquad j=0,1,
$$
where $\mathcal I f=\int_0^1 f(Y)\,dY$ and $J$ is the physical primitive from zero. The term $-\gamma I$ is retained here: the earlier live site does not vanish under $G$. These tests pay the actual next primitive, not just a terminal evaluation. Precision eight also requires
$$
 \mathcal I(Y^j G(Y-b_1)K)=0,\qquad j=0,1,
$$
since $G(Y-b_1)K$ is the seven-site node hull.

## Complete placement elimination

The first two genuine clocks $\gamma,a\gamma$ are distinct. Neither can equal $\gamma s_r,\gamma t_r$; therefore each is one of the two ports or one of $u,b_1,b_2$.

- **Neither is a port (six placements).** Prescribe two of $u,b_1,b_2$ to be $\gamma,a\gamma$, and write $z$ for the remaining one. The four equations are affine in $z$. All $2\times2$ minors of the four rows of coefficients on $(1,z)$ vanish. If $b_1$ is free, the quadrature rows have degree at most six in $\gamma$, and the $z$-independent primitive rows have degree at most seven. Thus these minors have degree at most thirteen. If $u$ or $b_2$ is free, each row has degree at most six because one cubic factor lost one affine clock factor; then the minors have degree at most twelve. In each placement the replay selects two full-degree minors with resultant nonzero.
- **Exactly one is a port (twelve placements).** Anchoring $k\gamma=1-\gamma v$ or $1-\gamma w$, with $k=1$ or $a$, fixes $\gamma$. If the other anchor is $u$ or $b_2$, the two primitive equations are affine in the one remaining variable they use, so a $2\times2$ coefficient determinant must vanish. If the other anchor is $b_1$, all four equations are bilinear in $u,b_2$; the $4\times4$ coefficient matrix on $(1,u,b_2,ub_2)$ must be singular. All twelve determinants are nonzero.
- **Both are ports (two placements).** The clock equations would give $w=v+1-a$ or $w=v+a-1$. Over $\mathbb Q(s_f,v)$, where $s_f$ is the forward seed root, adjoining the reverse seed root $s_r$ has degree at most two. But the forward $w$ is irreducible of degree three over $\mathbb Q(s_f,v)$, by the tower proof in the six-site packet. Neither relation is possible.

For the modular proof, there are just two relative reverse root classes. If $s_r=s_f$, the quadratic for $t_r$ is irreducible over the forward tower by good reduction at $p=37,(s_f,v,w)=(8,3,19)$. If $s_r\ne s_f$, its quadratic factor $X^2+(s_f-9)X+s_f^2-9s_f+18$ is irreducible by good reduction at $p=13,(s_f,v,w)=(9,6,2)$. The next $t_r$ quadratic is irreducible at $p=43,(s_f,v,w,s_r)=(26,16,39,28)$. The simple-root Hensel and monic-integrality arguments are as in the six-site packet. Thus each relative class is a field, not an unresolved product. For the actual eliminants use $p=43,(s_f,v,w)=(26,16,39)$ and the simple roots $(s_r,t_r)=(26,18),(41,2)$ respectively. The full-degree Bézout pairs and selected determinants are nonzero there, so their characteristic-zero lifts are nonzero for every conjugate branch.

## Replay and scope

    sha256sum -c sources.sha256
    python3 check.py

The exact SymPy replay independently rebuilds the four polynomial moment equations, all eighteen tested placements in both relative root classes, and the modular receipts. It shares only irreducibility and root helpers with the neighboring six-site packet. A separate [native Lean audit](../../lean/evidence/sdirk9-seven-site-three-terminal-20261127/README.md) checks twelve emitted degree-preserving Bézout identities and twenty-four nonzero determinant residues. The direct reverse chronology and characteristic-zero transfer are mathematical. This eliminates the entire specified seven-site three-terminal chart, not any unrestricted tableau class.

Together with the six-site exclusion, the unresolved two-disjoint-port counts are $(6,1,4),(6,2,5),(7,2,4)$. No thirteen-stage method is claimed.
