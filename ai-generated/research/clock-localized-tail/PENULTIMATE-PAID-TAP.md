# The penultimate paid tap of a late explicit direction is zero

Let \(A\) be strictly lower triangular in physical stage order, let \(\mathbf c\coloneqq A\mathbf1\), and define
\[
 C\coloneqq\operatorname{diag}(\mathbf c),\qquad Y\coloneqq I-C,\qquad D\coloneqq CA-AC-A^2=AY-YA-A^2.
\]
Suppose the tableau has order \(p\) over a field in which \(p!\ne0\). A vector belongs to \(E_g\) if it is a linear combination of actual Butcher weight vectors of trees having at most \(g+1\) vertices. A vector belongs to \(F_g\) if it comes from such a combination with zero exact polynomial profile. The exact profile associated with \(\boldsymbol\Phi_t(A)\) is \(|t|X^{|t|-1}/t!\); the profile of \(A\mathbf v\) is the primitive from zero of the profile of \(\mathbf v\), and multiplication by \(C\) multiplies a profile by \(X\). These statements are about formal combinations, so no model separation at degree \(g\) is required. In particular
\[
 AE_j+YE_j\subseteq E_{j+1},\qquad DE_j\subseteq F_{j+2}.
\]
For the last inclusion, the formal model of \(D\) is zero because \(XJ-JX=J^2\) for the primitive \(J\) from zero. The vanishing is an identity of polynomials under multiplication and integration.

Fix an integer \(m\ge0\) and a nonzero actual row \(\boldsymbol\beta\coloneqq\mathbf b A^m\), whose last nonzero coordinate is \(t\). Fix \(g\ge0\) and put
\[
 L\coloneqq p-1-m-g,\qquad
 K_g\coloneqq\{\mathbf v\in E_g : v_i=0 \text{ for }i<t-L\},\qquad
 \mu_j(\mathbf v)\coloneqq\boldsymbol\beta A^j\cdot\mathbf v .
\]
All physical coordinates and matrices in the proof may be restricted to the prefix through \(t\). If \(t-L\le0\), the loose suffix has fewer than \(L+1\) physical rows; it can equivalently be padded at its beginning by formal zero rows for the path count. In the intended use \(t-L\ge1\).

**Theorem.** If \(L\ge6\), then \(\mu_{L-1}\) is zero on \(K_g\). If \(\mu_L\) is not identically zero there, all the rows \(\mu_2,\ldots,\mu_{L-1}\) are zero on \(K_g\). For \(L\ge5\), on any \(\mathbf v\in K_g\) with \(\mu_L(\mathbf v)\ne0\), the numbers \(\mu_L,\ldots,\mu_3\) are geometric in reverse index. The last assertion means
\[
 \mu_{L-j}(\mathbf v)=a^j\mu_L(\mathbf v)\quad(0\le j\le L-3),
 \qquad a\coloneqq \mu_{L-1}(\mathbf v)/\mu_L(\mathbf v).
\]
The same conclusions hold if, at every grade throughout this argument, \(E_j\) is enlarged by the span of a final coordinate vector \(\mathbf e_s\) with \(A\mathbf e_s=Y\mathbf e_s=0\). This added direction makes no contribution to either side of any tested word with a positive power of \(A\) or \(Y\), or to the commutator.

## The paid word equations

For \(i,k,r\ge0\), \(i+k+r\le L\), and \(\mathbf v\in E_g\),
\[
 \boldsymbol\beta A^kY^r A^i\cdot\mathbf v
   =\frac{(m+k+r)!}{(m+k)!}\,\mu_{i+k+r}(\mathbf v).              \tag{1}
\]
Indeed exact order reads the model of \(\mathbf v\) against \((1-X)^m/m!\) after applying the corresponding word. An upper primitive sends \((1-X)^a\) to \((1-X)^{a+1}/(a+1)\) when using the ordinary integral. Moving the \(m+k\) outer copies of \(A\) to this adjoint side gives weight \((1-X)^{m+k}/(m+k)!\); multiplication by \(Y^r\) then changes the weight by the indicated factorial ratio. This is the same read as the right side. Likewise the paid rows \(\boldsymbol\beta A^kY^r\) kill \(D A^{i-1}\mathbf v\) if \(i\ge1\) and \(i+k+r+1\le L\), because its exact model is zero through that cost.

## The complete terminal path

Suppose \(\mathbf v\in K_g\) and abbreviate \(\mu_j\coloneqq\mu_j(\mathbf v)\). First assume \(\mu_L\ne0\). The \(L\)-edge path must use precisely all \(L+1\) terminal rows. In particular \(t-L\) is physical, \(v_{t-L}\ne0\), and every adjacent entry of \(A\) along this suffix is nonzero. Set
\[
 \boldsymbol\eta_i\coloneqq A^i\mathbf v,\qquad y_i\coloneqq 1-c_{t-L+i}
 \quad(0\le i\le L).
\]
The vectors are considered on the actual suffix: \(\boldsymbol\eta_i\) has its first nonzero coordinate at its row of ordinal \(i\), and they form a basis. They satisfy \(A\boldsymbol\eta_i=\boldsymbol\eta_{i+1}\) before the end and \(A\boldsymbol\eta_L=0\).

In this basis the component of \(Y\boldsymbol\eta_j\) at \(\boldsymbol\eta_j\) is \(y_j\), and its next coefficient \(z_j\) is determined by (1) at \(k=L-j-1,r=1,i=j\):
\[
 \begin{split}
 Y\boldsymbol\eta_j&=y_j\boldsymbol\eta_j+z_j\boldsymbol\eta_{j+1}
                  +\text{terms on later basis vectors},\\
 z_j&=m+L-j-y_j a,\qquad a\coloneqq\mu_{L-1}/\mu_L .
 \end{split}                                                     \tag{2}
\]
In the two-dimensional quotient of the suffix beginning at ordinal \(j\) by the suffix beginning at ordinal \(j+2\), these are consecutive matrix entries of a split diagonalizable operator. Thus if \(y_j=y_{j+1}\), that off-diagonal entry is zero. This excludes two adjacent endpoint clocks (\(y_j=y_{j+1}=0\)); it also excludes any three consecutive equal clocks, since their two required values of \(m+L-j\) differ by one.

Define the scalars \(r_h\) by the formal reciprocal, to degree \(L\),
\[
 \sum_{h=0}^L r_h Z^h
  \equiv\left(\sum_{h=0}^L\frac{\mu_{L-h}}{\mu_L} Z^h\right)^{-1}
  \pmod{Z^{L+1}},\qquad
 \mathbf u_i\coloneqq \sum_{j=0}^{L-i}r_j\boldsymbol\eta_{i+j}.
\]
Then \(r_0=1\), \(r_1=-a\), and \(\mathbf u_i=A^i\mathbf u_0\). Moreover \(\mathbf u_i\) has leading coefficient one at \(\boldsymbol\eta_i\) and its first \(L-i\) terminal taps \(\boldsymbol\beta A^k\) are zero, for \(0\le k<L-i\). This is the reciprocal identity at coefficient \(L-i-k\). These \(L-i\) linear tests are independent on the suffix starting at ordinal \(i\): apply them in descending \(k\) on the basis \(\boldsymbol\eta_i,\ldots,\boldsymbol\eta_L\); their successive terminal coefficients are \(\mu_L\). The common kernel is therefore exactly the line spanned by \(\mathbf u_i\).

The actual vector \(D\boldsymbol\eta_{i-1}\) lies in that suffix, since \(D\) is strictly lower triangular. Its first \(L-i\) taps are paid pure tests, so it belongs to that same line. Its leading coefficient follows from \(D=AY-YA-A^2\). Thus
\[
 D\boldsymbol\eta_{i-1}=(y_{i-1}-y_i)\mathbf u_i
 \quad(1\le i\le L).                                              \tag{3}
\]
This equality is a statement on numerical suffix rows, not just on their formal model.

## One or two clock factors on the genuine commutator direction

Set \(R\coloneqq L-i-k\). For \(R\ge2\), the word with one \(Y\) gives
\[
 \boldsymbol\beta A^kY\cdot\mathbf u_i=r_R y_{i+R}\mu_L .          \tag{4}
\]
Indeed the terms with \(j<R\) in \(\mathbf u_i\) are all paid by (1); their sum is \((m+k+1)\boldsymbol\beta A^{k+1}\cdot\mathbf u_i=0\). The term with \(j=R\) only sees the diagonal and later terms have already passed the terminal row.

For \(R\ge3\), the word with two \(Y\)'s similarly gives
\[
 \frac{\boldsymbol\beta A^kY^2\cdot\mathbf u_i}{\mu_L}
  =r_{R-1}\big((m+k+1)(u+w)-a u w\big)+r_R w^2,\qquad
 u\coloneqq y_{i+R-1},\quad w\coloneqq y_{i+R}.                    \tag{5}
\]
The terms with \(j\le R-2\) sum to
\((m+k+1)(m+k+2)\boldsymbol\beta A^{k+2}\cdot\mathbf u_i=0\). The \(j=R\) term sees just \(w^2\). For \(j=R-1\), the two remaining coordinates give \(u^2\mu_{L-1}+z_{i+R-1}(u+w)\mu_L\). Equation (2) changes this coefficient divided by \(\mu_L\) to the one in (5).

If \(y_{i-1}\ne y_i\), then (3) makes (4), also with \(k\) replaced by \(k+1\) when \(R\ge3\), and (5) zero by paid purity. In particular
\[
                 r_R w=0,\qquad r_{R-1}u=0 .
\]
If \(r_{R-1}\ne0\), first \(u=0\), then \((m+k+1)w=0\) by (5), so \(w=0\). This would give adjacent endpoint clocks, forbidden by (2). Consequently
\[
   r_j\ne0
   \ \Longrightarrow\
   y_{i-1}=y_i\quad\text{for all }1\le i\le L-j-1
   \qquad(2\le j\le L-2).                                       \tag{6}
\]
For \(2\le j\le L-3\), the first three clocks would then coincide. Hence all those \(r_j\) are zero. The reciprocal identity now gives precisely the stated reverse-geometric law down to \(\mu_3\).

## Comparing consecutive actual late spaces

Suppose \(L\ge6\) and the row \(\mu_L\) is nonzero on \(K_g\). At each grade with budget at least five and a nonzero top row, the last and penultimate rows on its whole late subspace are proportional. To see this, the geometric result gives the quadratic identity \(\mu_{L-1}^2=\mu_{L-2}\mu_L\) whenever \(\mu_L\ne0\). It also holds on its kernel: translate any vector there along a fixed vector with nonzero top read, and use more than two nonzero field scalars on the quadratic polynomial in the translation parameter. The field has sufficiently many elements because the relevant factorial is paid. Thus the kernel of the top row is contained in that of the penultimate row, as asserted.

Let \(\mu_L(\mathbf v)\ne0\). The vectors \(A\mathbf v\) and
\((Y-y_0 I)\mathbf v\) belong to \(K_{g+1}\), now with budget \(L-1\), since both vanish at the first allowed physical row of \(K_g\). At that next grade the top row is nonzero on \(A\mathbf v\) and the proportionality ratio is \(a=\mu_{L-1}(\mathbf v)/\mu_L(\mathbf v)\), fixed by this actual vector. Apply the same proportionality to \((Y-y_0 I)\mathbf v\). By (1), its two relevant taps are
\[
 \begin{split}
 \mu_{L-2}((Y-y_0 I)\mathbf v)&=(m+L-1)\mu_{L-1}(\mathbf v)-y_0\mu_{L-2}(\mathbf v),\\
 \mu_{L-1}((Y-y_0 I)\mathbf v)&=(m+L)\mu_L(\mathbf v)-y_0\mu_{L-1}(\mathbf v).
 \end{split}
\]
Their required ratio, and \(\mu_{L-2}=a^2\mu_L\) on the original vector, imply \(a\mu_L(\mathbf v)=0\), so \(a=0\). Equation (2) now forbids every equal adjacency. Taking \(i=1\) in (6) therefore also eliminates \(r_{L-2}\). The reciprocal shows that \(\mu_2,\ldots,\mu_{L-1}\) all vanish for this vector. Each is a linear row; vanishing on the complement of the proper linear kernel of \(\mu_L\) implies vanishing everywhere on \(K_g\).

## If there is no top path

It remains to prove the penultimate vanishing when \(\mu_L(\mathbf v)=0\) and the top row is unavailable. Suppose for contradiction \(\mu_{L-1}(\mathbf v)\ne0\). A contribution to this tap is a path of \(L-1\) edges spanning \(L\) of the possible \(L+1\) suffix positions. For each omitted ordinal \(h\), its contribution is the product of the starting \(v\)-coordinate, the actual entries of \(A\) along that path and the ending \(\beta\)-coordinate; there is only one chronological path on that chosen set of rows. If an initial position is not physical, regard it as a zero row with clock 1. At least one path contributes.

There are at most two nonzero contributions, and if there are two their omitted positions are adjacent. Indeed if the first possible coordinate is zero, only the path omitting that first position can contribute. Otherwise nonzero \(\beta_t\) and zero \(\mu_L(\mathbf v)\) force a missing adjacent edge. Every path with nonzero contribution must omit one of that edge's two endpoints.

Insert one factor \(Y\) at any ordinal along a path of \(L-1\) edges, testing (1) at total cost \(L\). Its expected response is zero because \(\mu_L(\mathbf v)=0\). Every position common to the contributing paths is at the same ordinal, since the two possible omitted positions are adjacent. The actual response there equals that position's \(Y\)-clock times the nonzero total contribution \(\mu_{L-1}(\mathbf v)\). Thus every common physical row is at the endpoint clock. There are at most two possibly nonendpoint physical rows, adjacent if there are two.

Now insert \(Y\) in a path with only \(L-2\) edges. A selected row of path ordinal \(a\) has physical ordinal between \(a\) and \(a+2\), since such a path omits two of the \(L+1\) positions. Among \(a=0,\ldots,L-2\), at most four insertion ordinals can meet either of two adjacent possibly nonendpoint physical rows. Since \(L\ge6\), there is an ordinal that cannot meet either. The corresponding actual response is zero. But (1) gives \((m+k+1)\mu_{L-1}(\mathbf v)\ne0\), where \(k\) is the number of remaining outer edges. This is the contradiction.

The argument uses only word equations from actual rooted order, the paid purity of \(D\), actual clock diagonalizability, and literal triangular support. No eigenvalue simplicity, sign, or absence of skipped edges is assumed. Over a nonzero commutative ring, the conclusions can be applied after selecting a paid residue field; the ranks and support descriptions are field statements, not assertions of freeness over the ring.
