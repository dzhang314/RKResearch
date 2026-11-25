# Causal elimination of the attained order-seven and order-eight DIRK profiles

This paper strengthens the [weighted profile reduction](../weighted-profile-reduction.md). At the nonsingular stage floors, the first two and the last two clocks are different, even with unequal diagonals and zero intermediate weights. On the full-weight chart, the profiles determine both the forward and weighted-transpose actions on the four-dimensional degree-two space. Their simultaneous realization needs only prefix and suffix span tests and a small global moment equality. At order seven there is at most one tableau parameter left, and none if either four-stage end has full degree-two rank. At order eight there are at most six parameters, constrained by just four residual scalar equations; with regular four-stage ends there is at most one parameter, and in the usual five-stage rank cell there is none after those four tests. These are structural results, not an existence or nonexistence claim for either floor. All proofs are mathematical; the companion Python checker is not a Lean kernel receipt.

## 1. A lower-triangular interpolation lemma over any field

Given matrices $X,G\in K^{n\times a}$, $U,H\in K^{n\times b}$, and a prescribed diagonal $D$, seek a lower-triangular $B$ satisfying
$$
 BX=G,\qquad U^{\mathsf T}B=H^{\mathsf T},\qquad \operatorname{diag}B=D.
$$
Here $D$ denotes the diagonal matrix with the prescribed entries. Write $W=G-DX$, $Z=H-DU$ and use zero-based chronology. Such a $B$ exists **if and only if**
$$
\begin{aligned}
 W_i&\in\operatorname{span}\{X_j:j<i\} &&(0\le i<n),\\
 Z_j&\in\operatorname{span}\{U_i:i>j\} &&(0\le j<n),\\
 U^{\mathsf T}W&=Z^{\mathsf T}X .
\end{aligned}\tag{1}
$$
Rows are treated as vectors. Empty spans are zero; no rank genericity is required.

For the proof, choose the forward greedy pivot rows of $X$ and the backward greedy pivot rows of $U$. For each forward nonpivot $j$, let $f_j=e_j-\sum_{k<j}c_{jk}e_k$ express $X_j$ using earlier pivot rows only. Thus $f_j^{\mathsf T}X=0$. Similarly, for each backward nonpivot $i$, choose $g_i=e_i-\sum_{k>i}d_{ik}e_k$ using later backward pivots, so $U^{\mathsf T}g_i=0$.

Necessity is immediate. For sufficiency, first make $N_0X=W$ row by row, supporting each row on strictly earlier forward pivots. For each forward nonpivot $j$, the second condition in (1) gives a column $c_j$ supported strictly after $j$ with $U^{\mathsf T}c_j=Z_j^{\mathsf T}$. Set $N=N_0+\sum_j c_j f_j^{\mathsf T}$. Then $N$ is strictly lower, $NX=W$, and $Z^{\mathsf T}-U^{\mathsf T}N$ vanishes on the nonpivot columns. Its product with $X$ is zero by the third condition of (1); independence of the forward pivot rows makes the remaining columns zero too. Take $B=D+N$.

All homogeneous solutions have the explicit basis
$$
       g_i f_j^{\mathsf T},\qquad j<i,\quad
       j\text{ a forward nonpivot},\quad i\text{ a backward nonpivot}.\tag{2}
$$
Indeed, every row of a homogeneous solution is uniquely a combination of $f_j^{\mathsf T}$ with $j$ strictly before that row. In matrix form the coefficient of $f_j^{\mathsf T}$ is a column supported strictly after $j$. Its product by $U^{\mathsf T}$ must vanish, and the applicable $g_i$ are precisely a basis of that suffix kernel. This proves spanning and independence. Counting crossed nonpivot pairs gives the exact fibre dimension, not just an upper bound. Both the construction and the tests work even if one input matrix is rank deficient.

## 2. Paid dual observability without nonzero-weight assumptions

Hereafter let $(p,n)=(7,8)$ or $(8,10)$. Let $B=zA$ be a lower-triangular tableau of the indicated order with all $d_i=B_{ii}\ne0$, $z\ne0$. Write $x=B\mathbf1$, $C=\operatorname{diag}x$, $R=CB-BC-B^2$, and $\beta=b^{\mathsf T}$. All vector powers and products are componentwise. We use the actual graded column and defect spaces $E_j,F_j$, their exact paid ranks, the quadrature $\beta x^j=z^j/(j+1)$, $RE_j\subset F_{j+2}$, and D1, $\beta B=z\beta-\beta C$, proved in the linked paper. In particular $E_{p-2}=K^n$. No sign condition, ordering, or characteristic-zero hypothesis is required; the affordable integer divisors are units under the order assumption.

**Finite dual basis.** In each of these lines, the listed covectors are a basis of the entire dual, without requiring any specified nonzero output weight:
$$
\begin{array}{c|l}
p=7& \beta C^{0,1};\quad \beta C^{0,1,2,3}R;\quad \beta C^{0,1}R^2\\
p=8& \beta C^{0,1};\quad \beta C^{0,1,2,3}R;\quad \beta C^{0,1,2}R^2;\quad \beta R^3 .
\end{array}\tag{3}
$$
A list of exponents denotes separate rows. To prove this, recursively append $R$ on the right of the previous rows at degree $r-2$, and add the rows $\beta C^j$, $0\le j\le q=\min(r,p-1-r)$; start at $r=0$ or 1 with the pure rows. Right multiplication retains independence since $R$ is invertible with diagonal $-d_i^2$. The rows ending in $R$ annihilate $1,x,\ldots,x^q$: the first physical $R$ applied to a power puts it in the defect flag, further $R$'s increase the defect budget by two; this follows by expanding $R$ in the two genuine advances $B,C$. The total cost is at most $r+q\le p-1$. The added pure rows pair with these powers by the nonsingular paid Hankel matrix. Thus the ranks add at each step. At $r=p-2$ the counts are eight and ten, respectively. In particular a nonzero $R$-eigenvector cannot be invisible to all clock rows.

**The two ends.** The last and penultimate weights are nonzero and the last two clocks are *always distinct*, including for unequal diagonals. Set $l=n-1$, $j=n-2$. If $b_l=0$, the last atom $e_l$ is an invisible $R$-eigenvector, impossible by (3). D1 then gives
$$
 x_l=z-d_l,\qquad b_l B_{lj}=(z-x_j-d_j)b_j.\tag{4}
$$
If $b_j=0$, the link in (4) vanishes, and $e_j$ is again an invisible eigenvector. If $x_j=x_l$, set $v=b_l e_j-b_j e_l\ne0$. Now (4) gives $Bv=d_jv$, and $Cv=x_l v$. Hence $Rv=-d_j^2v$ and $\beta C^k v=0$ for all $k$, a contradiction. No equal-diagonal hypothesis is used.

More generally, a constant-clock terminal block of size at least two cannot occur: its coordinate subspace is $B$-invariant by the lower triangle and $C$ is scalar there. D1 makes the kernel of its restricted output row invariant under its restricted $B$. This kernel is nontrivial and has an eigenvector over the *original field*: the characteristic polynomial of the restriction to the kernel divides the split characteristic polynomial of the triangular block. On that eigenvector $R=-B^2$ and all clock observations vanish. The same proof excludes any $B$-invariant coordinate subset of size at least two on a single clock, not just a terminal subset. More generally, no nonzero $B,C$-invariant subspace lies in $\ker\beta$, immediately from (3).

There is also a quantitative terminal support bound, still allowing zero weights. On a terminal segment of length $h$, let $q$ count the distinct clocks having at least one nonzero *individual* weight in that segment. Restriction of the basis (3) to the segment has rank $h$. The segment is $R$-invariant, and the restriction of the rows $\beta C^j R^k$ at fixed $k$ has rank at most the smaller of $q$ and the number of displayed consecutive powers. Thus
$$
 h\le 2\min(q,2)+\min(q,4)\quad(p=7),\qquad
 h\le \min(q,2)+\min(q,4)+\min(q,3)+\min(q,1)\quad(p=8).
$$
In particular the last seven stages at order seven and the last eight stages at order eight must each contain at least three distinct clocks with active weights. Summing weights within a clock is not needed.

The first two clocks are distinct as well. If they coincide, then on rows zero and one every application of $B$ to a column equal at these positions again has equal values there, since both row sums have the common clock. Coordinatewise products preserve that equality. All elementary columns would agree there, contradicting $E_{p-2}=K^n$. This argument does not use either first output weight.

## 3. Recovering four forward and four reverse actions from the profile

Now assume every $b_i\ne0$. Fix the data $z,d,b,x,s,t$ of the [weighted profile theorem](../weighted-profile-reduction.md), with $s=2Bx-x^2=-R\mathbf1$, $t=Rx$ on an actual tableau. Its 23 or 30 scalar tests, the open rank conditions, and $Cs\in F_3=\operatorname{span}(s,t)$ are retained. Let
$$
 P_2=\operatorname{span}(\mathbf1,x,x^2,s),\qquad
 P_3=P_2+\operatorname{span}(x^3,t),\qquad
 D_b=\operatorname{diag}(b).
$$
These are exactly $E_2,E_3$ at attainment. Use $B^\dagger=D_b^{-1}B^{\mathsf T}D_b$ and $\langle u,v\rangle=u^{\mathsf T}D_b v$. The paid dual flag identities are $F_k=E_{p-1-k}^{\perp}$ in the needed range. This weighted scalar product need not be positive.

For a chronological initial block $\left(\begin{smallmatrix}a&0\\ u&d\end{smallmatrix}\right)$ with clocks $a,d+u$, its local seed and cubic columns are
$$
 (s_0,s_1)=(a^2,2au+d^2-u^2),\qquad
 (t_0,t_1)=(-a^3,-2a^2u+au^2-d^3-d^2u).
\tag{5}
$$
Their two-row determinant is $-a^2d^2(d+u-a)\ne0$ by Section 2. Check these entries with $a=d_0,d=d_1,u=x_1-d_1$. The column $g=Bs$ lies in $F_3$, so it is uniquely recovered from
$$
 g_0=a s_0,\qquad g_1=u s_0+d s_1 .
$$
In particular if $a=d$, then $g=-t$; equality of the other diagonals is not needed. Define
$$
 X=[\mathbf1,x,x^2,s],\qquad
 G=\left[x,\ (x^2+s)/2,\ (x^3+Cs-2t-g)/3,\ g\right].\tag{6}
$$
The earlier profile equation is now exactly $BX=G$.

For the dual construction read chronology backwards and set $\bar x=z\mathbf1-x$, $\bar C=zI-C$, $\bar R=\bar C B^\dagger-B^\dagger\bar C-(B^\dagger)^2=R^\dagger$. D1 gives $B^\dagger\mathbf1=\bar x$. Paid duality gives $R^\dagger E_k=F_{k+2}$ for $k=0,1$: pair against $E_{p-3-k}$, use $RE_{p-3-k}\subseteq F_{p-1-k}$, and compare dimensions using invertibility. Likewise $B^\dagger F_2\subset F_3$ by pairing against $E_{p-4}$ and $BE_{p-4}\subset E_{p-3}$. Thus
$$
 \bar s=-R^\dagger\mathbf1\in F_2=K s,\qquad
 \bar t=R^\dagger\bar x\in F_3,\qquad
 \bar g=B^\dagger\bar s\in F_3.
$$
The first two reversed rows have initial data $a=d_l,d=d_j,u=\bar x_j-d_j$ from D1. Use (5) on the positions $l,j$ in this order. First recover $\bar s=d_l^2 s/s_l$ and check both endpoint entries. Recover the unique $\bar t\in F_3$ with the two entries in (5), and the unique $\bar g\in F_3$ with $\bar g_l=a\bar s_l, \bar g_j=u\bar s_l+d\bar s_j$. These are necessary guards, not guesses: $s_l\ne0$, and (5) applied to $\bar s,\bar t$ has nonzero determinant since $x_j\ne x_l$. Thus restriction of $F_3=\operatorname{span}(s,t)$ to the final two coordinates is invertible. Reject a profile if any boundary check fails, in particular if $x_0\ne d_0$ or $x_l\ne z-d_l$.

Use (6) with bars on $x,C,s,t,g$ to get $\bar X,\bar G$. Then $B^\dagger\bar X=\bar G$ follows from the algebraic identities $2B^\dagger\bar x=\bar x^2+\bar s$ and $B^\dagger(3\bar x^2+\bar s)=\bar x^3+\bar C\bar s-2\bar t$. No order-preservation theorem for a general transposed RK method is assumed. Both $X$ and $\bar X$ have column span $P_2$. Apply (1) with
$$
 U=D_b\bar X,\quad H=D_b\bar G.
\tag{7}
$$
This produces the complete candidate affine space $B_0+\mathcal K$ with the prescribed two actions, together with the rank-one basis (2).

## 4. What remains at cubic degree

The statements below are **necessary and sufficient**, keeping the listed profile tests and boundary guards. To see this without attributing order to a truncated test, start with (5) of the [original complete profile theorem](../weighted-profile-reduction.md). Its original primitive/advance tests are
$$
 BD_k\subset D_{k+1}\ (2\le k\le p-3),\qquad
 m Bx^{m-1}-x^m\in D_m\ (4\le m\le p-2).
\tag{8}
$$
Here $D_2=K s,D_3=\operatorname{span}(s,t)$, and $D_k=P_{p-1-k}^{\perp}$ for $k\ge4$, with $P_0=K\mathbf1,P_1=\operatorname{span}(\mathbf1,x)$. Apply (8) to $B_0$ for the following fixed checks: any pairing with input in $P_2$ is already fixed by (6); any pairing with test in $P_2$ is fixed by (7). These fixed checks must still pass unless verified to follow from other scalar data. They do not constrain the coordinates of $\mathcal K$.

At **order seven**, all tests in (8) are fixed in this way. Indeed $BD_2\subset D_3$ follows from (6); for $k\ge3$ all target tests belong to $P_2$, as do the target tests for every primitive in (8). Thus either the entire affine space produced by (1) is of order seven or none of it is.

At **order eight**, the only variable pairings are $BD_3\subset D_4=P_3^\perp$ on the input $t$, and $4Bx^3-x^4\in D_4$; test against the two extra vectors $x^3,t$ in $P_3/P_2$. All other instances of (8) are fixed, including $BD_4\subset D_5=P_2^\perp$. Write $L=[x^3,t]$. The last test in the coordinates of $\mathcal K$ is exactly
$$
 L^{\mathsf T}D_b B L=
 \begin{pmatrix}
    \langle x^3,x^4\rangle/4 & 0\\
    \langle t,x^4\rangle/4 & 0
 \end{pmatrix}.\tag{9}
$$
For (2) its coefficient matrices are the outer products $(L^{\mathsf T}D_b g_i)(f_j^{\mathsf T}L)$. So (9) is solved by a rank test on a matrix with just four rows. In particular no nonlinear verification of a solved tableau is being deferred. Homogeneous freedom invisible to (9) is genuine freedom between methods of the same order with the same profiles.

## 5. Uniform fibre bounds and the precise one-parameter exception

The first three rows of $X$ are independent at attainment. The first two clocks are distinct. If the third row were dependent, its coefficients on the first two rows would sum to one, and testing against $1,x,x^2$ forces its clock to equal one of those two and its row to equal that earlier $X$-row by interpolating $(T-x_0)(T-x_1)$. In particular its seed and clock agree with row $h<2$. Since the first two rows of $[1,x]$ are independent, the row equations on $B\mathbf1,Bx$ now force $B_{2,<2}=B_{h,<2}-d_2e_h^{\mathsf T}$. Every column that agrees at coordinates 2 and $h$ is sent by $B$ to another such column. Products preserve agreement, contradicting $E_{p-2}=K^n$.

The first three rows of $\bar X$ in *reverse* chronology are likewise independent. The same argument would force two mirrored coordinates to agree on every column obtained from $\mathbf1$ by $B^\dagger,\bar C$, since the duplicate clocks also agree. But under $D_b^{-1}$ the transposes of the basis (3) are $(R^\dagger)^k C^j\mathbf1$; all are generated by these operators and they span $K^n$. No assumption that $B^\dagger$ has full tree order was used. With nonzero weights the same suffix ranks hold for $U=D_b\bar X$.

Consequently a forward nonpivot has $j\ge3$ and a backward nonpivot has $i\le n-4$.
* **Order seven, eight stages:** only $j=3,i=4$ can survive (2). The tableau with this profile is unique if the first four or last four rows of $P_2$ have rank four. If both four-row blocks have rank three and a solution exists, (2) is exactly a line and *every member* of that line has the prescribed order-seven profile.
* **Order eight, ten stages:** at most the six strict pairs $3\le j<i\le6$ survive; the four equations in (9) are the whole remaining tableau test. If both four-row ends have rank four, only $j=4,i=5$ can survive. Its coefficient in (9) is nonzero precisely when the first five and last five rows of $P_3$ each have rank five: the respective rank increments are detected by $f_4^{\mathsf T}L\ne0$ and $L^{\mathsf T}D_b g_5\ne0$. Thus the tableau with the fixed profile is unique when both five-row ends have rank five. If either fails under the regular four-row hypotheses, (9) is a compatibility check only and a feasible profile has an exact affine line.

There is a useful physical description of the last exception. Suppose the first four rows of $P_2$ have rank four, but the first five rows of $P_3$ have rank four. Express row 4 of $P_3$ as an affine combination of the first four. Since $CP_2\subseteq P_3$ and the first four $P_2$ rows are independent, every nonzero coefficient must be on a row with clock $x_4$: subtract $x_4$ times the relation on $P_2$ from its relation on $CP_2$. If it were a singleton, row 4 would equal an earlier physical $P_3$-row. As $BP_2\subseteq P_3$, independence of the first four $P_2$-rows would force the same duplicate-row operator identity as above, impossible. Thus the fifth row must repeat a clock already represented at least twice in the first four. The reverse statement uses $\bar C P_2\subseteq P_3$, $B^\dagger P_2\subseteq P_3$ from (6)–(7), and (3) to exclude merging. In particular, if both four-row ends are regular and neither five-row end has a triply repeated clock, then every feasible order-eight profile has a unique tableau. These tests range over all profiles in their hypotheses; they do not enumerate fixed coefficients or assert that an exceptional cell is nonempty.

The [stdlib checker](check.py) independently compares the causal criterion and nullity with the full strict-entry equations, including rank-deficient and inconsistent fixtures. It also verifies the two-by-two endpoint identities over several fields. It does not establish attainment or turn the proof above into a kernel-checked formalization.
