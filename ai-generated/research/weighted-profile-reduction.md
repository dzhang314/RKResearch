# Weighted profile reduction at the nonsingular Runge–Kutta order-seven and order-eight floors

## Abstract

At the nonsingular lower-triangular stage floors $(p,n)=(7,8)$ and $(8,10)$, the attained rooted-tree conditions force exact primal and dual flags. When all output weights are nonzero, these flags determine every defect space from degree four onward using only the clocks, the output weights, and two low-degree defect columns. Consequently, for fixed profiles every remaining condition on the tableau is affine-linear. Separately, for a singly diagonally implicit tableau with exactly four distinct physical clocks, a nonzero first output weight forces stringent endpoint multiplicities: at order seven every weight is nonzero and the multiplicities are either $2,2,2,2$ or $3,3,1,1$; at order eight each endpoint clock requires at least three nonzero weights and at least eight weights are nonzero overall. The support result does not assume that the other weights are nonzero.

The companion [Lean rank-two packet](../lean/RKCert/ReviewedNative/DefectRankTwoPacket.lean) checks the reduction of low-degree products to four and ten generators under its explicit cubic cover. The full profile theorem below is a mathematical proof, not an end-to-end Lean check.

## 1. Exact flags at attainment

Let $K$ be a field and let $A$ be a lower-triangular $n\times n$ Runge–Kutta matrix with nonzero diagonal, with output row $\beta=b^{\mathsf T}$. Write $B=zA$ for any $z\in K^\times$, $x=B\mathbf1$, and $C=\operatorname{diag}(x)$. Define
$
 M_j(v)=\beta C^jv,\qquad
 R=CB-BC-B^2,\qquad
 e_m=mB x^{m-1}-x^m,\qquad s=e_2,\quad t=Rx.
$
Column powers and products are componentwise. The order predicate is the full denominator-cleared reviewed rooted-tree predicate, not an order condition for chains alone. For $B$, its scaled scalar identity at a tree of size $d$ is $z^{d-1}$. In particular
$
 (j+1) M_j(\mathbf1)=z^j,\qquad 0\le j<p. \tag{1}
$
Thus every cast $1,\ldots,p$ is a unit.

Let $E_j$ be the span of genuine elementary columns through grade $j$, where grade is tree size minus one. Let $F_j$ be the span of differences of forest-factorial-normalized columns of equal grade at most $j$. Multiplication of columns adds grades; multiplication of a defect by an affordable column remains a defect. This follows by joining roots, since normalized columns multiply under that operation. Multiplication by $C$ or application of $B$ advances grade by one. In particular $M_k(F_j)=0$ when $k+j+1\le p$.

The Volterra expression gives $R E_j\subseteq F_{j+2}$ in the relevant budget. For example, on a normalized column of size $d$, its three attachments with two added vertices have normalized values $dCBv$, $(d+1)BCv$, and $d(d+1)B^2v$. The combination of their differences with coefficients $d+1$ and $-d$ is $d(d+1)Rv$. Since $R_{ii}=-B_{ii}^2$, the lower-triangular $R$ is invertible. The $q+1$ clock columns of degrees $0,\ldots,q$ are independent modulo $F_{j+2}$ if $q\le j+2$ and $j+q+3\le p$: the paid clock moment tests have an invertible Hankel matrix, a nonzero diagonal rescaling of the Cauchy matrix $(1/(i+k+1))_{0\le i,k\le q}$. This gives
$
 \dim E_{j+2}\ge \dim E_j+q+1. \tag{2}
$
The first two ranks are $1,2$. At degree two the elementary columns are spanned by $\mathbf1,x,x^2,Bx$, and (2) with $j=0,q=2$ gives rank four. At order seven the useful reverse bounds are $r_5\ge r_3+2$ and $r_6\ge r_4+1$. At order eight they are $r_5\ge r_3+3$, $r_7\ge r_5+1$, and $r_6\ge r_4+2$, where $r_j=\dim E_j$. Combining with $r_j\le n$ gives the exact ranks:
$
\begin{array}{c|rrrrrrrr|rrrrrr}
 &\multicolumn{8}{c|}{\dim E_j,\ j=0,\ldots,p-1}
 &\multicolumn{6}{c}{\dim F_j,\ j=2,\ldots,p-1}\\
p=7&1&2&4&6&7&8&8&-&1&2&4&6&7&-\\
p=8&1&2&4&6&8&9&10&10&1&2&4&6&8&9
\end{array}
$
Here the upper bounds on $\dim F_j$ subtract the independent paid clock packet of degrees $0,\ldots,\min(j,p-1-j)$; the lower bounds use $R E_{j-2}$. They coincide. Thus
$
 F_j=R E_{j-2},\qquad
 E_j=F_j\oplus\operatorname{span}\{\mathbf1,x,\ldots,x^{\min(j,p-1-j)}\}. \tag{3}
$
In particular $F_2=\operatorname{span}(s)$, $F_3=\operatorname{span}(s,t)$, and $E_2,E_3$ are the pure clock columns through those grades plus their indicated defects. These are consequences of attainment, not additional rank assumptions.

The first adjoint equation is also forced:
$
 \beta B=z\beta-\beta C. \tag{4}
$
Indeed on a normalized column $v$ of size $d\le p-1$ the three values $\beta v,\beta Bv,\beta Cv$ are $z^{d-1}/d,\ z^d/(d(d+1)),\ z^d/(d+1)$. Equation (4) therefore holds on $E_{p-2}=K^n$.

## 2. An exact affine-linear profile construction

**Theorem 1.** Fix $(p,n)=(7,8)$ or $(8,10)$, a field $K$, $z\ne0$, and a prescribed nonzero diagonal $d_i$. Assume all entries of $\beta$ are nonzero. Then the space of attained normalized tableaux $B=zA$ admits the following exact profile description. For fixed profiles $(\beta,x,s,t)$, the remaining feasibility problem in the strictly lower entries of $B$ is affine-linear.

**Profile data.** Set $D_0=D_1=0$, $D_2=\operatorname{span}(s)$, $D_3=\operatorname{span}(s,t)$, and
$
 P_0=\operatorname{span}(\mathbf1),\quad P_1=\operatorname{span}(\mathbf1,x),\quad
 P_2=\operatorname{span}(\mathbf1,x,x^2,s),\quad
 P_3=\operatorname{span}(\mathbf1,x,x^2,x^3,s,t).
$
Orthogonality is with respect to the nondegenerate form $\langle u,v\rangle=\beta(uv)$. For $j\ge4$ define $D_j=P_{p-1-j}^{\perp}$. Require $s,t$ independent, $Cs\in D_3$, the pure moments (1), and the following scalar zeros:
$
\begin{array}{c|c}
\text{column}&\text{indices }j\text{ with }M_j=0\\\hline
s&0,\ldots,p-3\\
t&0,\ldots,p-4\\
s^2&0,\ldots,p-5\\
st&0,\ldots,p-6\\
t^2&0,\ldots,p-7\\
s^3&0\\
s^2t&0\ \text{only at }p=8 .
\end{array}
$
Together with (1) there are 23 listed scalar checks at $p=7$ and 30 at $p=8$. No claim of algebraic independence is made.

**Matrix feasibility.** In addition to the prescribed diagonal and zero entries above it, solve
$
\begin{gathered}
 B\mathbf1=x,\qquad 2Bx=x^2+s,\qquad B(3x^2+s)=x^3+Cs-2t,\qquad
 \beta B=z\beta-\beta C,\\
 B D_j\subseteq D_{j+1}\quad(2\le j\le p-3),\qquad
 m Bx^{m-1}-x^m\in D_m\quad(4\le m\le p-2).
\end{gathered} \tag{5}
$
These are affine-linear because the columns and subspaces appearing in them are specified by the profiles. Each inclusion is tested on a basis of its prescribed domain, against the known linear target. Consequently equality of the ordinary and augmented ranks is an exact matrix-feasibility test after the profile checks.

**Necessity.** The paid pointwise product rule gives $F_j\subseteq E_{p-1-j}^{\perp}$. Nondegeneracy and the ranks of Section 1 give equality. Thus for an attained tableau the displayed $P_i,D_j$ are exactly the actual spaces. The scalar tests are genuine affordable moments. The third equality of (5) is precisely the column identity $2Rx=(C-B)s-e_3$, obtained by expanding $R$; all other equations now follow from the genuine flags and (4).

**Sufficiency.** The first three equations identify $x,s,t$ with the actual columns and place $e_3$ in $D_3$. The scalar profile checks ensure $CD_3\subseteq D_4$, by testing against the clock and defect columns of the defining $P_i$. They also give $CD_2\subseteq D_3$ by the specified membership, and $CD_j\subseteq D_{j+1}$ above degree three by self-adjointness of $C$ and the low-column inclusions $CP_i\subseteq P_{i+1}$. In degree four the product $s^2$ is tested against $P_2$ or $P_3$; this is why $s^3$ and, at order eight, $s^2t$ occur. The products $D_2D_3$ and $D_3D_3$ are paid by the stated square and mixed moments. The remaining products are automatic: at order seven $D_4\perp s$; at order eight $D_4\perp s,Cs,D_3$ and $D_5\perp s$. The last advance follows from (4) on $D_{p-2}=\ker M_0\cap\ker M_1$, and the last primitive has zero mass by (1) and (4). Thus $B,C$ advance the actual proposed spaces, all affordable products have their target grade, and all $D_j$ have zero mass.

For completeness, writing $\nu_u$ for the forest-factorial-normalized column, the reviewed tree recursion is $\nu_{r\triangleleft u}=\nu_r\cdot(|u|B\nu_u)$. The grade closure just verified shows inductively $\nu_u-x^{|u|-1}\in D_{|u|-1}$. Using (1) gives every scaled tree identity. Homogeneity then gives the original reviewed order for $A=z^{-1}B$. This proves exactness of the description on the stated full-weight chart.

## 3. Four-clock endpoint support without a full-weight assumption

**Theorem 2.** Suppose $A$ attains one of the two floors, its nonzero diagonal is common, its physical clocks have exactly four distinct values, and $b_0\ne0$. At order seven all eight output weights are nonzero, and the clock multiplicities are $2,2,2,2$ or $3,3,1,1$, with both endpoint clocks triple in the latter case. At order eight there are at least three nonzero output weights in each endpoint clock group and at least eight nonzero output weights in total.

**Visibility of the last stage.** This preliminary argument uses no full-weight assumption and no common-diagonal hypothesis. The nonzero row $\beta R$ annihilates $E_{p-3}$, so (3) identifies that hyperplane with $\ker(\beta R)$. If $Rv=\lambda v$, $\lambda\ne0$, and all $M_j(v)=0$, then $v\in E_{p-3}$. In the split (3) the paid probes remove the clock part, giving $v\in F_{p-3}=R E_{p-5}$. Invertibility and the eigenvalue then give $v\in E_{p-5}$. Repeat the argument: the descents are $E_4\to E_2\to E_0$ and $E_5\to E_3\to E_1$, respectively. The last pure clock packet is visible, so $v=0$. The last coordinate, an $R$-eigenvector, therefore has $b_{n-1}\ne0$.

The row $L_s(v)=\beta(sv)$ also kills $E_{p-3}$ by its exact grade-two cost, so $L_s=\mu\beta R$ for some $\mu$, which may be zero. Normalize the common diagonal to one. Then $x_0=s_0=1$, and (4) at the last coordinate gives $x_{n-1}=z-1$. Here $b_0\ne0$ implies $L_s\ne0$, so $\mu\ne0$, and comparison at the visible last coordinate gives $s_{n-1}=-\mu\ne0$.

**Clock groups.** Write $\xi_g$ for the four different normalized clocks, $W_g=\sum_{i:x_i=\xi_g} b_i$, and let $P(X)=\prod_g(X-\xi_g)$. The four-clock Hankel matrix is the clock Vandermonde times $\operatorname{diag}(W_g)$ times its transpose. Its invertibility from pure moments through degree six gives $W_g\ne0$ for every group.

The midpoint is not a clock. The monic nodal polynomial $P$ pairs to zero against $1,X,X^2$ using the pure moments. On polynomials of degree at most four that joint kernel is two-dimensional, by the degree-two Hankel matrix, and is spanned by the two scaled shifted Legendre polynomials
$
 L_3=20X^3-30zX^2+12z^2X-z^3,\qquad
 L_4=70X^4-140zX^3+90z^2X^2-20z^3X+z^4.
$
Their orthogonalities follow directly from (1). At $X=z/2$ they have values $0$ and $3z^4/8$, respectively. The degree-four coefficient of $P$ is nonzero, so $P(z/2)\ne0$. In particular $x_0\ne x_{n-1}$, since equality would give $z=2$ and make that common clock the midpoint.

The groupwise first seed moments vanish, by the Vandermonde selector on the four paid probes of $s$. Put $m_g=\sum_{i:x_i=\xi_g}b_i s_i^2$. At order eight the four paid probes of $s^2$ give $m_g=0$ for every group. At order seven three probes give $m_g=\eta/P'(\xi_g)$ for some $\eta$, since this nonzero barycentric vector spans the annihilator of the evaluations of $1,X,X^2$. Thus either all $m_g$ vanish or none do.

A group with $W_g\ne0$, zero first and second seed moments, and at most two nonzero weights has zero seed at every active stage. With two weights $a,d$ and seeds $u,v$, substitute $v=-au/d$ into the second moment to obtain $a(a+d)u^2/d=0$. The one-weight case is immediate. The distinct endpoint groups both have nonzero active seeds. Consequently at order eight each needs at least three nonzero weights, and the other two nonzero group masses give at least two more. At order seven, if $m\ne0$, every group needs at least two nonzero weights; with eight stages the four groups must all be pairs. If $m=0$, the endpoint groups require three each and the other two at least one each, exhausting all eight stages. This proves the asserted support statements.

These theorems do not assert that four clocks are necessary, that $b_0$ must be nonzero, or that either stage floor is attained or unattainable in general.
