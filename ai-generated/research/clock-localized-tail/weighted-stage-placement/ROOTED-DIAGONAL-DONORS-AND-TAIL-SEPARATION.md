# Rooted diagonal donors debit the actual remaining reverse width

Use the paid field, rooted spaces and nonsingular triangular matrix of TWO-SIDED-SURPLUS-AND-PHYSICAL-OVERLAP.md. The tableau itself has ordinary order \(p\). There is no sparse or minimal quadrature assumption.

## A larger paid physical row family with the same scalar rank

Write \(d_t\coloneqq |t|-1\), and add the rooted diagonal operator
\[
 B_t\coloneqq\operatorname{diag}(\boldsymbol\Phi_t(A))
\]
as an available reverse letter of cost \(d_t\). The primitive \(A\) has cost one. The trivial rooted diagonal is the identity and can be omitted. The clock \(C\) is the rooted diagonal of \([\bullet]\). Define
\[
 \mathcal D_r\coloneqq
 \operatorname{span}\{\mathbf b^{\rm row} W:\ \operatorname{cost}W\le r\},
 \qquad \mathcal R_j\coloneqq\mathcal D_{p-1-j},
\]
with \(\mathcal D_r=0\) for negative \(r\). The ordinary algebra with only \(A,C\) is a subfamily. Rooted sum implies that \(B_t\) sends an actual \(u\)-tree vector to the \((t\#u)\)-tree vector and multiplies its scalar model by \(P_t(x)\), at degree cost \(d_t\). Extension gives the primitive rule for \(A\). Thus an actual row in \(\mathcal R_j\) is paid on all of \(E_j\), and its action is integration against a polynomial density of degree at most \(p-1-j\). Indeed a right \(B_t\) multiplies the density by \(P_t\), and a right \(A\) sends density \(f(x)\) to \(\int_x^1 f(y)\,dy\) by interchanging the polynomial primitives. All denominators involved are paid by \(p!\).

The scalar rank is still exactly
\[
 h_j=\min(j+1,p-j),
\]
because all densities up to degree \(p-1-j\) are already supplied by \(\mathbf b^{\rm row}C^\ell\); the pairing with degree-\(j\) polynomials has full smaller rank by the paid Cauchy matrix \(1/(\ell+m+1)\). The enlargement can increase the actual dimension, not this scalar rank. The degree-two commutator is among the paid words, so the two-sided ledger applies without changing its scalar parity floor.

## Measured tail separation at any split

Let \(r\coloneqq p-1-j\); split the literal indices into a leading prefix \(P\) and a suffix \(S\). Define
\[
 u^S_{r-2}\coloneqq\dim(\mathcal D_{r-2}|_S),\qquad
 D_{\rm old}\coloneqq
       \sum_{\substack{i\ge j+2,\ i\le p-1\\i\equiv j\ (2)}}h_i,\qquad
 Q_j\coloneqq\sum_{\substack{0\le i\le p-1\\i\equiv j\ (2)}}h_i .
\]
Suffix restrictions of diagonal letters are inherited original rooted values, not recalculated on the isolated suffix. Write \(M_S\) for the lower-right principal submatrix of \(M\); restricting \(\mathcal D_{r-2}M\) to the suffix gives \((\mathcal D_{r-2}|_S)M_S\), of dimension \(u^S_{r-2}\) since \(M_S\) is invertible. For **any** paid subspace \(Z_P\subseteq\mathcal R_j\cap\operatorname{Ann}(E_j)\) truly supported in \(P\),
\[
 \boxed{\qquad s-Q_j\ \ge\ \dim Z_P+u^S_{r-2}-D_{\rm old}.\qquad}       \tag{3}
\]
Proof: \(K_j\) contains \(Z_P+G_j\); its dimension is at least \(\dim Z_P+u^S_{r-2}\), because \(Z_P\) has zero suffix restriction. Combine with \(s\ge\dim E_j+\dim K_j\) and the forward sum through \(j\). Thus a suffix meeting the entire previous parity rank budget leaves no room at the scalar floor for even one extra leading cancelling donor. More generally, missing at most \(d\) of the earlier ranks leaves at most \(s-Q_j+d\) such independent leading rows. One may use any rigorously measured lower bound on \(u^S_{r-2}\), including a bound with only \(A,C\). Choosing the parity with \(Q_j=Q(p)\) gives the usual nonsingular quadratic floor as reference, but (3) also works on the other parity.

For example, in strict common-diagonal methods put \(N=A-\gamma I\). List distinct visible suffix labels in decreasing order of their last weighted indices \(i_\ell\), and let \(f_\ell(x)\coloneqq\prod_{m<\ell}(x-c_{i_m})\). The row \(\mathbf b^{\rm row}f_\ell(C)N^v\) has actual latest suffix pivot \(i_\ell-v\) whenever that index lies in \(S\), \(\ell-1+v\le r-2\), and all adjacent links on that path are nonzero. The coefficient is \(b_{i_\ell}f_\ell(c_{i_\ell})\) times the actual path product; earlier weighted occurrences of the same label cannot reach the pivot in \(v\) strict steps. The number of different resulting pivot indices is a valid lower bound on \(u^S_{r-2}\). No root property or pivot is assumed at an unmeasured label, and overlapping paths are counted only once.

## Leading kernels from repeated fibres

Let \(q\) be the number of distinct labels with at least one actual nonzero weight, and suppose the fibre-isolation payment is available, \(a\coloneqq p-q\ge j\). For any completed leading fibre at clock \(\theta\), let \(w_\theta\) be its actual raw fibre row and \(\bar b_\theta\) its aggregate. Fix a rooted tree \(t\) with \(d_t>0\), and write
\[
 \zeta_i\coloneqq \boldsymbol\Phi_t(A)_i,\quad
 \zeta_*\coloneqq P_t(\theta),\quad
 m_\theta\coloneqq\lfloor(a-j)/d_t\rfloor.
\]
The raw fibre is in \(\mathcal D_{q-1}\) by Lagrange isolation of the actual visible labels. On a true degree-\(j\) rooted profile the row \(w_\theta B_t^\ell\) has scalar read \(\bar b_\theta \zeta_*^\ell P(\theta)\) for \(0\le\ell\le m_\theta\). This is the original fibre exactness applied after the actual root product, not a stage purity assumption.

- If \(\bar b_\theta=0\), all these rows are in \(Z_P\). Their physical span has rank exactly \(\min(m_\theta+1,\#\{\zeta_i:b_i\ne0,\ c_i=\theta\})\): every column includes its actual nonzero \(b_i\), and the different \(\zeta_i\) give Vandermonde rank. Repeated values count once even when several nonzero weights have that value.
- If \(\bar b_\theta\ne0\), the rows \(w_\theta(B_t-\zeta_*I)B_t^\ell\), \(0\le\ell<m_\theta\), are all in \(Z_P\) and have exact rank \(\min(m_\theta,\#\{\zeta_i:b_i\ne0,\ c_i=\theta,\ \zeta_i\ne\zeta_*\})\). Here the nonzero column scaling is \(b_i(\zeta_i-\zeta_*)\); no individual stage is inferred exact from a signed weighted combination.

The ranks of these supplied subspaces add for different completed fibres, by disjoint support. Multiple trees on the same fibre instead require the rank of the joint actual evaluation matrix. One can also pool all raw and diagonal-multiplied paid fibre rows in \(W\) in (2); this counts any pure scalar dependencies *between* different fibres as well. A shifted cancelling row from a not-yet-completed fibre is another candidate for \(Z_P\) only if its actual full suffix restriction is zero and its cost is paid. It need not be independent of the completed rows.

Even when individual isolation is too expensive, (3) is applicable. To see a model-only way of producing eligible physical rows without \(q\le p\), let \(q_S\) be the number of visible suffix labels, let \(g_S(x)\) be the product of their linear factors, and consider \(\mathbf b^{\rm row}g_S(C)H(C)\) with \(\deg H\le r-q_S\) when \(r\ge q_S\). These are literal leading rows. If \(m\) distinct visible labels occur exclusively in \(P\), their ambient rank is \(\min(m,r-q_S+1)\) by Vandermonde evaluation. Their scalar rank is the actual paid matrix rank of
\(\int_0^1 x^i g_S(x)x^\ell\,dx\), \(0\le i\le j,\ 0\le \ell\le r-q_S\).
The difference is a valid leading \(Z_P\). No count of Gaussian quadrature nodes, unobserved donors, or unearned side rank is used in (3).

All these are conditional physical-width or equality constraints, not a new unrestricted numerical table entry.
