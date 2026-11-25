# No strictly interior three-change weak-five quartic

**Result.** Let $K$ be an ordered field. Let $q,Z,c$ satisfy the actual `WeakFive16.Moments` with $\deg q=4$, and put $(u,a,h,z)=(c_1,c_2,c_3,c_4)$. If all four nonorigin marks lie in $(0,1)$, then $q$ cannot have exactly three sign-changing roots in $(0,1)$ over an ordered real closure of $K$. The accompanying checker verifies a finite rational certificate on the entire continuous density and pencil domains. This is a mathematical proof with an independently rerunnable, standard-library checker, not a Lean check, not a fixed physical fibre, and not a stage lower bound.

These are the original paid scalar inputs. Write $w=X(1-X)$, $N=(X-u)(X-a)(X-h)(X-z)$; all displayed integrals are polynomial formal integrals. The four marks are pairwise distinct, and $q$ is nonzero at each. The six global words say $I_{0,1}(wqN H)=0$ for $\deg H\le5$. The end pairs say $I_{0,u}(Xq)=I_{0,u}(X^2q)=I_{z,1}((1-X)q)=I_{z,1}((1-X)^2q)=0$. The two inner words are $I_{0,a}(X(X-u)q)=I_{h,1}((1-X)(z-X)q)=0$. All identities, strict orders, and the positive rational 19-node grid exact through degree 19 persist in the ordered real closure. This is the only extension needed; the argument then consists of polynomial factorizations, exact integrations, finite inequalities and algebraic IVT. In particular it does not rely on an Archimedean field, moving-root derivatives, or empirical parameter tests.

## 1. Reduction to nine actual root orders

Make the quartic monic by a nonzero scaling. Its three sign-changing unit roots $r_1<r_2<r_3$ are simple, and its remaining root is real and outside $(0,1)$, possibly on an endpoint. Reflect if necessary by
$$
 (q,u,a,h,z)\longmapsto (q(1-X),1-z,1-h,1-a,1-u).
$$
The substitution swaps the two sets of end/inner words and preserves the global words, with a degree-preserving test substitution. It preserves nonvanishing at the four nonorigin marks. If the original $q(1)=0$, the reflected $q(0)=0$ is allowed here: no step needs nonvanishing at the origin. In the chosen orientation the residual root is $-\lambda\le0$. After one more positive rescaling, the actual polynomial is
$$
 q=[s+(1-s)X]H_3,\qquad H_3=(X-r_1)(X-r_2)(X-r_3),
 \qquad s=\lambda/(1+\lambda)\in[0,1).
$$

Put $p(x)=\#\{r_i<x\}$. The local end moments require $p(u)\ge2$, $3-p(z)\ge2$: if the corresponding window had at most one root, a constant or affine sign fit of $q$ there would contradict its exact two moments with the positive weight $X$ or $1-X$. The inner and end moments also pay the true difference windows:
$$
 I_{u,a}(X(X-u)q)=0,\qquad I_{h,z}((1-X)(z-X)q)=0.
$$
If $a<u$, both $(0,a)$ and $(a,u)$ have a root, since the corresponding multiplier has fixed nonzero sign there; thus $1\le p(a)<p(u)$. If $u<a$, $p(u)<p(a)$. If $z<h$, similarly $p(z)<p(h)\le2$; if $h<z$, $p(h)<p(z)$. All strict sign arguments use a positive exact affine grid and a nonzero polynomial of degree at most six, so a finite set of zeros does not remove strictness.

**Fully paid erasures and actual atomic signs.** The signed law $\nu(P)=I_{0,1}(wqP)=\sum_x\eta_x P(x)$ for $\deg P\le9$ is obtained by division by $N$ and interpolation on the four marks $x\in\{u,a,h,z\}$. With $\ell_x$ their cardinal cubics,
$$
 \eta_x H_3(x)=I_{0,1}(w[s+(1-s)X] H_3^2\ell_x^2)>0 .
$$
The tested degree in the signed law is $3+6=9$, and the positive integrand has degree at most 15. Thus $\operatorname{sgn}\eta_x=\operatorname{sgn}q(x)=(-1)^{3-p(x)}$.

At stop $u$ erase any $e\in\{a,h,z\}$, replacing the signed profile by $P_e=(X-e)q$. At stop $a$ erase $e=u$. At stop $z$ erase any $e\in\{u,a,h\}$; at stop $h$ erase $e=z$. In each case the multiplied local word is paid: the end cases are affine combinations of their endpoint pair, and the inner cases are their original tests (up to a sign for the suffix). The modified signed law holds through degree 8 and has three atoms, with masses $(x-e)\eta_x$. On the prefix the pole is $1/(1-X)$, and on the suffix it is $1/X$; the suffix can be reflected to the prefix. The four unit simple roots of $P_e$ give four strict sign cuts away from the live stop. The stopped bracket costs $4+2(3-1)=8$ test degrees, total grid degree $2+5+8=15$, and deg $P_e$ plus the number of strictly stopped-side off-stop atoms is at most $5+2<19$. Thus its strict sign conclusion is fully paid:
$$
 \exists x\ne t,e \text{ strictly on the stopped side of }t,\qquad
 \operatorname{sgn}\bigl(\eta_x(x-e)\bigr)
 =-\operatorname{sgn}\bigl(\eta_t(t-e)\bigr).
$$
Indeed the stopped sum with its stop removed has the sign opposite to $P_e(t)$, by the two exact inequalities of `FiniteStoppedBracket.strict_bracket_of_pole_grid`; pole values are positive at every mark. For the sign fit use the actual four simple roots, split about $t$, so no approximation or additional variation premise is needed. This also implies that at least two marks strictly precede $u$ and at least two strictly follow $z$, since a single one could be erased, and that some $h$ or $z$ lies below $a$, and some $u$ or $a$ lies above $h$.

Interleave the three root labels `123` in increasing order with a permutation of the four marked labels. The window inequalities leave 29 of the 840 words; these count consequences leave 20; the opposite-sign requirement just proved leaves exactly the nine words in the table below. The pure finite enumeration `three_change_order_check` in the checker verifies the set directly, using only comparisons of positions. This step imposes no guessed order and does not claim that every survivor of the sign tests is feasible.

## 2. The actual positive seven-node rule and its compact pencil

For $0\le s\le1$, put $W_s=w[s+(1-s)X]$, strictly positive on the open unit interval. The global words say the monic degree-seven polynomial $T=H_3N$ is orthogonal through degree five for $W_s$. Its seven roots $\beta_1<\cdots<\beta_7$ are exactly the three unit roots and four marks of Section 1, with no collisions. Division by $T$ and interpolation on its nodes therefore give a seven-node law exact through degree **12** (not 13). Its weights are positive: apply the exact law to the square of each degree-six cardinal polynomial, then the positive 19-node rule to that integrand of degree at most $3+12=15$.

Scale this positive functional and weights by $D=12252240$; write $L_s(P)=D I_{0,1}(W_sP)$. Set $\mu_j=1/[(j+2)(j+3)]$, $b_j=D[\mu_{j+1}+s(\mu_j-\mu_{j+1})]$. In the monomial basis through degree six take $B_{ij}=b_{i+j}$, $A_{ij}=b_{i+j+1}$, and $E_{ij}=1$ only at $i=j=6$ (otherwise 0, indices starting at 0). Let $\delta$ be the rule's error on $X^{13}$, defined as rule minus $L_s$. For degree-at-most-six $P,Q$ the only potentially unpaid term of $XPQ$ is $[X^6]P[X^6]Q X^{13}$. Thus if $V$ is the square evaluation matrix at the seven actual nodes and $\omega_i>0$ are the scaled rule weights, exactly
$$
 B=V^\mathsf T\operatorname{diag}(\omega_i)V,\qquad
 A+\delta E=V^\mathsf T\operatorname{diag}(\omega_i\beta_i)V.
$$
In particular $A+\delta E$ and $B-A-\delta E$ are strictly positive definite, and
$$
 \det(A+\delta E-xB)=\det B\prod_{i=1}^7(\beta_i-x),\qquad \det B>0 .
$$

For any symmetric positive definite matrix $M$ of size seven, the minimum of its quadratic form on coefficient vectors whose last coordinate is 1 is $\det M/\det M_6$, where $M_6$ is its leading six block. This is algebraic over an ordered field: solve away the first six coordinates by completing the square using $M_6^{-1}$, and use the block determinant identity. Apply it to $A$ and $B-A$ using positivity of $XW_s$ and $(1-X)W_s$ on the positive grid. The preceding strict definiteness then implies
$$
 d_0(s):=-\det A/\det A_6 <\delta<
 d_1(s):=\det(B-A)/\det((B-A)_6).
$$
Since $W_s$ is pointwise nondecreasing in $s$, the two minima are nondecreasing (compare each quadratic form at the minimizing vector at the larger parameter). Thus $d_0<0$ is nonincreasing and $d_1>0$ is nondecreasing. Define $j=(\delta-d_0(s))/(d_1(s)-d_0(s))\in(0,1)$. For a closed rectangle $s_-\le s\le s_+,\ j_-\le j\le j_+$ the actual $\delta=(1-j)d_0(s)+jd_1(s)$ lies in the closed rational interval
$$
 (1-j_-)d_0(s_+)+j_-d_1(s_-)
 \ \le\ \delta\ \le\
 (1-j_+)d_0(s_-)+j_+d_1(s_+).
$$
Both bounding expressions use that the interpolation is increasing in $j$. The proof covers the entire parameter square, not a list of selected physical inputs.

## 3. Exact uniform root cages in every rectangle

Let $D_n(s,x)=\det(A_n-xB_n)$ for the leading block $n=6,7$. By expansion in the last diagonal entry the actual pencil determinant is $D_7(s,x)+\delta D_6(s,x)$. Each $D_n$ has degree at most $n$ separately in $s,x$, with integer coefficients, because $D$ clears every relevant monomial moment denominator. The two small coefficient templates in `determinants.json` are verified by exact integer determinant computation on the product grid $\{0,\ldots,n\}^2$; the stated degree bound and two applications of the polynomial zero bound prove the identities everywhere over any characteristic-zero field. There is no physical evaluation in this interpolation of a polynomial identity. The two endpoint formulas are $d_0(s)=-D_7(s,0)/D_6(s,0)$, $d_1(s)=-D_7(s,1)/D_6(s,1)$, accounting for the odd seven and even six signs at $x=1$.

The table `boxes.tsv` lists 1212 rectangles with dyadic coordinates. A row starts with $d_s,i_s,d_j,i_j$; the rectangle is
$$
 [i_s/2^{d_s},(i_s+1)/2^{d_s}]\ \times\
 [i_j/2^{d_j},(i_j+1)/2^{d_j}].
$$
Its next 14 entries are the integer endpoints of the seven ordered, disjoint closed root cages in denominator 8192. The checker sweeps successive endpoints of the integer $s$-partition in common dyadic scale; the $j$-intervals of every spanning set exactly tile their full integer range. Taking the closures of those slices proves coverage of the entire closed square over every ordered field, including all edges. The largest $d_s,d_j$ are simply table data, not mathematical restrictions.

At a rational cage endpoint $x\notin\{0,1\}$, change $s=(i_s+Y)/2^{d_s}$ and expand the two determinant templates into degree-seven Bernstein coefficients in $Y$. Explicitly, for power coefficients $a_k$ the $i$-th coefficient is $\sum_{k\le i} a_k\binom{i}{k}/\binom 7k$. Since each degree-seven Bernstein basis element is nonnegative on $0\le Y\le1$, and their sum is 1, strict same-sign coefficients certify strict sign on the whole interval. The checker verifies this at both rational bounds for $\delta$; the determinant is affine in $\delta$, so the sign holds on the entire rectangle. The signs at 0 and 1 if used as cage edges follow from the seven actual unit nodes directly. The left/right signs of the $i$-th cage (one-based) are respectively $(-1)^{i-1},(-1)^i$. The seven disjoint sign brackets thus identify, in order, cages for all seven actual roots. This verifies continuum bounds, not estimates at representative samples.

## 4. The exact actual port in each of the nine orders

| Name | Actual paid integral |
|---|---|
| L1 | $I_{0,u}(Xq)$ |
| L2 | $I_{0,u}(X^2q)$ |
| LA | $I_{0,a}(X(X-u)q)$ |
| R1 | $I_{z,1}((1-X)q)$ |
| R2 | $I_{z,1}((1-X)^2q)$ |
| RH | $I_{h,1}((1-X)(X-z)q)$ |

All are actual paid zeroes; RH is the negative of the original reverse inner word. A word below assigns its characters in order to $\beta_1,\ldots,\beta_7$. The indicated test is fixed for that word across **all** rectangles. The last column is a verified lower bound on the **signed normalized** test, with common denominator $10^8$.

| Word | Test | Sign | Numerator |
|---|---|---:|---:|
| `1z2ah3u` | L1 | − | 182350 |
| `1z2ha3u` | L1 | − | 182350 |
| `h1z2u3a` | L2 | − | 41813 |
| `h1z2a3u` | R2 | + | 58 |
| `z1a2h3u` | LA | − | 2806686 |
| `z1h2u3a` | L2 | − | 41813 |
| `z1h2a3u` | RH | − | 12 |
| `z1ah2u3` | R1 | + | 243304 |
| `z1ha2u3` | R1 | + | 243304 |

Here are all rescaling identities. For a left test use $x=d t$, $d=u$ for L1/L2 and $d=a$ for LA, and put
$$
 C=s+(1-s)d>0,\quad \gamma=(1-s)d/C,\quad f(t)=(1-\gamma)+\gamma t .
$$
The normalized test is $I_{0,1}(t^e f(t)\prod_i(t-r_i/d))$ with $e=1,2$ for L1/L2. For LA it is $I_{0,1}(t f(t)(t-u/d)\prod_i(t-r_i/d))$. The respective positive prefactors taking these normalized tests to the actual test are $C d^5,C d^6,C d^6$.
For a right test use $x=d+(1-d)t$, $d=z$ for R1/R2 and $d=h$ for RH, and put $\gamma=(1-s)(1-d)$ with the same $f(t)$. The normalized test is $I_{0,1}((1-t)^e f(t)\prod_i(t-(r_i-d)/(1-d)))$ with $e=1,2$ for R1/R2. For RH it has $e=1$ and an additional factor $t-(z-d)/(1-d)$. The positive prefactors are respectively $(1-d)^5,(1-d)^6,(1-d)^6$. All formulas follow by the indicated affine polynomial substitution and the factorization of $q$, not by stopping an unrelated integral.

In a box, each rescaled left root ratio is enclosed using lower numerator/upper denominator and vice versa. For the right root ratios use that $(r-d)/(1-d)$ increases in $r$ and decreases in $d$ for the site range $r\le1,d<1$; use the same distinction for the extra RH factor. The left $\gamma$ decreases in $s$ and increases in $d$, by clearing positive denominators, and the right $\gamma$ decreases in both. These give rigorous boxes for each test. Each normalized test is separately affine in $\gamma$ and every centered root or extra factor. Successive convex interpolation therefore reduces its signed minimum to the finite vertices. The checker evaluates the vertices by polynomial multiplication and the exact moments $I_{0,1}(t^m)=1/(m+1)$, $I_{0,1}(t^m(1-t))=1/[(m+1)(m+2)]$ and $I_{0,1}(t^m(1-t)^2)=2/[(m+1)(m+2)(m+3)]$. The strictly positive signed lower bound in every case contradicts the same actual zero.

## Reproduce and scope

Keep `PROOF.md`, `determinants.json`, `boxes.tsv`, and `check_three_changes.py` together. Run `python3 check_three_changes.py` without `-O`. The checker uses only integer arithmetic and Python's standard-library rational arithmetic; every acceptance condition is independently rechecked. The dyadic row data are just proposed brackets: the argument relies on no numerical root values, searches, approximations, or arithmetic associated with a special physical input. The polynomial determinants here encode a finite Rayleigh pencil; no elimination of physical variables is being used. No previous one-inner certificate was run for this work.

This proof covers only the strict interior three-change case of the actual weak-five quartic. It does not give a four-change exclusion, a weak-four exclusion, or an unconditional stage result.
