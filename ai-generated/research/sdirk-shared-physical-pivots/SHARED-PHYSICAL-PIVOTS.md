# Shared physical rows for distinct clock groups

These are literal, source-only constructions for the ordinary rooted order conditions. They allow signed weights and use only real algebraic coefficients. A physical group with nonzero aggregate is a contributing clock; a group can have active individual weights even when its aggregate is zero. The co-site differences below have zero aggregate as corrections, not zero individual response after matrix multiplication. The regular quadrature clocks themselves all contribute.

## Setup

Let \(p=q+r+1\), \(q\ge1\), \(r\ge1\) and \(p\le 2q+2\). In particular, two children of size \(q+1\) never occur at a root of size at most \(p\). Write
\[
  g_t(X)\coloneqq |t|X^{|t|-1}/t!,\qquad
  I f\coloneqq\int_0^1f,\qquad
  (J f)(X)\coloneqq\int_0^Xf,\qquad
  (J^* f)(X)\coloneqq\int_X^1 f .
\]
The old strict common-diagonal matrix \(A_0\) has an actual linear decoder \(D_0\) taking stage vectors to polynomials of degree at most \(q-1\), with \(D_0\boldsymbol\Phi_t^0=g_t\) for \(|t|\le q\). Its output will be zero. The degree bound also applies when the decoder is evaluated on higher-order stage vectors. Define its actual first-excess error space
\[
  U\coloneqq\operatorname{span}\{g_t-D_0\boldsymbol\Phi_t^0:|t|=q+1\}.
\]
The old dense Laguerre preparation in the reviewed dense-donor result can have \(L(q)\coloneqq\lfloor(q+1)^2/4\rfloor\) rows and \(\dim U\le\lfloor q/2\rfloor+1\). Here and below the first-excess space is the one for the actual cached decoder; equality to an untruncated ideal chart is not assumed.

Take \(k\) distinct regular clock sites \(\xi_i\) with nonzero quadrature weights \(\beta_i\), exact through degree \(p-1\). Let \(S_X f=(f(\xi_i))_i\), \(C_X=\operatorname{diag}(\xi_i)\), and \(L_f=(\beta_i f(\xi_i))_i\) as a row. At \(g\) auxiliary physical stages, following the regular stages, use some of those same labels, with possible repetitions. Write \(C_Y\) for their clock diagonal and \(T\) for the selector assigning their regular representatives; \(S_Y=T S_X\) and \(T C_X=C_Y T\).

For row coordinates \(v,u\) on these two blocks, put
\[
  \Psi(v,u)\coloneqq(v-uT,u).
\]
Thus \(\Psi(0,u)\) is a shared collection of co-site differences. It does not read any polynomial sample vector \(S f=(S_X f;S_Y f)\), but it is generally nonzero on actual rooted stage columns. No assumption of identical rooted values is made.

Choose lower triangular \(G,D\) with common literal diagonal \(\gamma\ne0\), and any rectangular \(H\) of size \(g\) by \(k\). The physical new-stage block, the output row, and the old-to-new block are
\[
 B\coloneqq
  \begin{pmatrix}G&0\\ H+T G-D T&D\end{pmatrix},
 \qquad b_{\mathrm{new}}\coloneqq\Psi(\beta,\nu),\qquad
 O\coloneqq(SJ-BS)D_0.
\]
The full tableau is \(\left(\begin{smallmatrix}A_0&0\\O&B\end{smallmatrix}\right)\) with no old output. The feeds in \(O\) use earlier old stages, and the lower-left block of \(B\) uses earlier regular stages in the auxiliary rows. Every diagonal entry is \(\gamma\). Since \(D_0\mathbf1=1\), the new row sums equal the prescribed clocks. With \(C=\operatorname{diag}(C_X,C_Y)\), direct multiplication gives
\[
 \Psi(v,u)B=\Psi(vG+uH,uD),\qquad
 \Psi(v,u)C=\Psi(vC_X,uC_Y),\qquad
 \Psi(v,u)S f=v S_X f .
\]
At every clock the total weight is its regular \(\beta_i\), regardless of repeats or signs of individual weights. In particular no fresh noncontributing clock is forced. One regular representative can serve all auxiliary copies at its own clock. The last regular pivot rows to be chosen below serve the discrepancies of all clocks at once, not one set of pivots per group.

## One last word band can be paid by common taps

For a word \(W\) in the letters \(B,C\), let \(f_W\) be its polynomial density starting from \(1\), with a right \(B\) applying \(J^*\) and a right \(C\) multiplying by \(X\). Let \(u_W\) be the auxiliary row starting at \(\nu\) and using the letters \(D,C_Y\). Suppose there is an actual linear map \(\mathcal D\) on auxiliary rows satisfying
\[
  \mathcal D(u_W)=f_W\quad(|W|\le r-2),\qquad
  f_W-\mathcal D(u_W)\in V\quad(|W|=r-1)
\]
for some polynomial space \(V\) of dimension \(h\). Define \(H\) by the single linear rule
\[
                         uH=L_{J^*\mathcal D(u)}-L_{\mathcal D(u)}G .
\]
There is one requirement on the shared regular block:
\[
   (L_{J^*a}-L_aG) S_X F=0 \qquad(a\in V,\ F\in U).       \tag{1}
\]
Indeed, induction on word length gives \(v_W=L_{f_W}\) for \(|W|\le r-1\), in the transformed coordinates of \(b_{\mathrm{new}}W\). If the final letter for a word of length \(r\) is \(C\), the same equality holds. If it is \(B\) and its prefix is \(W\), then with \(\mathcal E\coloneqq f_W-\mathcal D(u_W)\) the discrepancy is
\[
              v_{WB}-L_{f_{WB}}=L_{\mathcal E}G-L_{J^*\mathcal E}.
\]
Thus at the longest length it is enough to use (1). Lower-length tests need no approximation.

Here is the physical solve for (1). Use \(h\) last regular rows as pivots and assume evaluation of \(V\) at their clocks is an isomorphism onto \(K^h\). Assume evaluation of \(U\) on the \(k-h\) other regular clocks is injective. Give every regular row the diagonal \(\gamma\) and set its other taps arbitrarily, except the taps from these last \(h\) rows into each earlier column. In an earlier column those \(h\) taps can vary the \(h\) discrepancy values for a basis of \(V\) freely: the coefficient matrix is the \(V\) evaluation matrix on the last \(h\) sites with its columns scaled by the nonzero \(\beta_i\). Contributions of the last \(h\) columns are already fixed. The injective map on \(U\) allows their contribution to be canceled by an earlier-coordinate linear functional, independently for each basis vector of \(V\). Solve those same \(h\) taps column by column. No diagonal or earlier row is altered. For \(h=0\) there is no requirement. This is an exact simultaneous solve, rather than a dimension heuristic about an unknown nonlinear tableau.

## Verification against every rooted tree

Put \(E_t=g_t-D_0\boldsymbol\Phi_t^0\), \(e_t=Sg_t-\boldsymbol\Phi_t^{\mathrm{new}}\), and \(\mathcal T=SJ-BS\). The literal primitive factor for a child \(t\) in a new row is
\[
  O\boldsymbol\Phi_t^0+B\boldsymbol\Phi_t^{\mathrm{new}}
                =SJg_t-\mathcal T E_t-Be_t .
\]
All new rows are exact through tree size \(q+1\) by induction. For a larger tree of size at most \(p\), at any root there is at most one child exceeding size \(q\). The other factors are nominal monomials in the clock, with their scalar tree factors. Induction down the unique large child therefore expresses the output error as a sum of terms of the form \(b_{\mathrm{new}} W\mathcal T E_t\), up to scalar factors, with \(|t|\ge q+1\) and \(|W|\le p-|t|-1\). A unary passage gives \(B\), and each unit of total small-sibling size gives a multiplication by \(C\).

For \(|W|<r-1\), both \(b_{\mathrm{new}}WSJE_t\) and \(b_{\mathrm{new}}WBS E_t\) reduce to their regular polynomial reads by the exact word identities. Their quadratures are within degree \(p-1\): \(\deg E_t\le|t|-1\), \(\deg f_W\le|W|\), and \(\deg f_{WB}\le|W|+1\). They coincide by \(I(f_W JE_t)=I((J^*f_W)E_t)\). When \(|W|=r-1\), its bound forces \(|t|=q+1\), so the one longest read \(WB\) uses (1) on \(E_t\in U\). The other read is still exact, and the same quadrature and adjoint identity apply. This proves all rooted conditions through \(p\). The next bushy tree fails if the scalar rule fails degree \(p\), since actual row sums and aggregate weights are the scalar data.

A stronger exact invariance assertion would preclude using the same co-site reference at distinct labels: an exact relation \(R C=C_Y R\) with diagonal \(C,C_Y\) places each row of \(R\) on its own physical clock fibre, by inspecting each coordinate. Thus a single coordinate cannot provide a nonzero entry in this exact difference for two unequal labels. This construction does not claim otherwise. It shares chronological physical correction pivots across labels, while retaining one already weighted reference per label.
