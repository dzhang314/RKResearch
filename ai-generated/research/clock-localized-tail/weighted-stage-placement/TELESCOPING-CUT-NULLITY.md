# A global cut bound with separate prefix and suffix kernels

Let \(A\) be a lower triangular RK tableau of ordinary order \(p\) over a field in which \(p!\) is a unit. Use \(E_j,F_j\) for its numerical rooted space and pure space through tree degree \(j\), meaning order \(j+1\). Write \(C\coloneqq\operatorname{diag}(A\mathbf1)\) and \(M\coloneqq CA-AC-A^2\). Fix a nonempty literal leading prefix \(P\) and an actual suffix \(S\) with \(L\ge1\) rows. Suffix matrices are \(T\coloneqq A_{S,S}\), \(C_S\coloneqq C_{S,S}\), and
\[
 M_S\coloneqq C_ST-TC_S-T^2,\qquad
 \boldsymbol\beta\coloneqq\mathbf b|_S.
\]
In this proof \(C_S\) is the inherited clock, not \(\operatorname{diag}(T\mathbf1)\). The leading matrix does retain its true clock, because its rows never use the suffix.

For \(r\ge0\) let \(U_r\) be the actual suffix row span of \(\boldsymbol\beta W(T,C_S)\) over words of length at most \(r\). Define
\[
 u_r\coloneqq\dim U_r,\quad
 \delta_r\coloneqq\dim\{\boldsymbol u\in U_r:\boldsymbol uM_S=0\},
 \qquad U_{-2}\coloneqq U_{-1}\coloneqq0 .
\]
Both negative-index dimensions are zero. In contrast write
\[
 \nu_j^P\coloneqq\dim\bigl(E_j(A_{P,P})\cap\ker M_{P,P}\bigr)
\]
for the **right** commutator nullity in the actual leading rooted space. In particular \(\nu_j^P\) and \(\delta_r\) are not a common nullity counted twice.

## The important improvement is to use the finite suffix word space, not its closure

For \(0\le j\le p-1\), define
\[
 r_j\coloneqq p-1-j,\quad a_j\coloneqq\min(j+1,r_j+1),\quad
 K_j\coloneqq E_j(A)\cap K^S .
\]
Identify \(K^S\) with vectors zero on the prefix. The actual paid rows \(\mathbf b A^m\), \(0\le m\le r_j\), have rank exactly \(a_j\) on \(E_j(A)\): they are the Beta functionals \(\ell_m\) on true rooted models, their rank on polynomial inputs follows from the factorial Vandermonde test, and the actual bushy columns supply every monomial. Let \(\lambda_j\) be their actual rank on \(K_j\). Thus \(a_j-\lambda_j\) independent exact scalar read combinations descend to the leading matrix and annihilate its pure space. The codimension here is relative to actual scalar functionals, not the number of formal weighted labels.

By ordinary order, the rows \(\mathbf b W(A,C) M\) for \(|W|\le r_j-2\) are genuine zero-model reads on \(E_j(A)\). Their suffix image is \(U_{r_j-2}M_S\), and this image lies in \(U_{r_j}\), since \(M_S\) has word length two in those same actual matrices. Hence the exact loss is bounded by
\[
       \lambda_j\le
        \min(a_j,\omega_{r_j}),\qquad
       \omega_r\coloneqq u_r-u_{r-2}+\delta_{r-2}.                 \tag{1}
\]
For \(r=0,1\) the zero-model correction space is empty, and the same inequality follows from the visible row space \(U_r\). Relative to the stationary bound using \(\dim U_\infty\), (1) uses the finite suffix progression required at the actual degree. Its loss term telescopes.

For \(\epsilon\in\{0,1\}\), let \(J_\epsilon\) be the largest \(j\le p-1\) of that parity, and define
\[
 B_\epsilon(p)\coloneqq
       \sum_{\substack{\epsilon\le j\le J_\epsilon\\j\equiv\epsilon\ ({\rm mod}\ 2)}}a_j,
 \qquad
 \mathcal R_\epsilon\coloneqq
       \sum_{\substack{\epsilon\le j\le J_\epsilon\\j\equiv\epsilon\ ({\rm mod}\ 2)}}
                       (\omega_{r_j}-\lambda_j).
\]
Only nonempty parities are used. The prefix pure inclusion
\(M_{P,P}E_{j-2}(A_{P,P})\subseteq F_j(A_{P,P})\)
and the descended scalar rows give
\[
 \boxed{\quad
 s\ge
 B_\epsilon(p)+L-u_{p-1-\epsilon}
  -\sum_{\substack{\epsilon+2\le j\le J_\epsilon\\j\equiv\epsilon\ ({\rm mod}\ 2)}}
                   \nu_{j-2}^P
  -\sum_{\substack{\epsilon\le j\le J_\epsilon\\j\equiv\epsilon\ ({\rm mod}\ 2)}}
                   \delta_{r_j-2}
  +\mathcal R_\epsilon .\quad}                                    \tag{2}
\]
Indeed the successive prefix rank increments are at least \(a_j-\lambda_j-\nu_{j-2}^P\), with initial bound \(a_\epsilon-\lambda_\epsilon\). Sum them and add the \(L\) disjoint actual rows. The two-step differences \(u_r-u_{r-2}\) sum to \(u_{p-1-\epsilon}\), since the last budget in the parity is zero or one. The refund \(\mathcal R_\epsilon\) is nonnegative; even without measuring \(\lambda_j\) one may refund at least \(\sum_j(\omega_{r_j}-a_j)_+\) from (1). A measured larger scalar prefix rank, or clipping a negative claimed rank increment to zero using nesting, only improves (2).

## What this changes relative to the quadratic bound

For a tableau with every diagonal nonzero both kernel penalties vanish. The larger of \(B_0(p),B_1(p)\) is the known
\[
           Q(p)\coloneqq\left\lceil
                          \frac{\lfloor(p+1)^2/4\rfloor}{2}\right\rceil ,
\]
of order \(p^2/8\); the parity ending at \(p-1\) attains it. This follows by summing the symmetric list \(a_j=\min(j+1,p-j)\), whose parity sums differ by at most one. Formula (2) now gives a genuine structural addition: a nonsingular method only \(g\) stages above \(Q(p)\) must, for **every literal cut**, have \(u_{p-1-\epsilon}\ge L-g\) in a maximizing parity, with an even higher demand if measured refunds are positive. It is not enough that each suffix site merely has a path to the output; these are dimensions of actual paid word reads. No ordinary order assumption says that a general suffix has a missing linear direction, so this is not an unconditional improvement.

For comparison, using only the earlier blind estimate \(\lambda_j\le\min(a_j,(L-r_j+1)_+)\) for a nonsingular suffix with \(1\le L\le p-1\) offers no gain on \(Q(p)\) by itself. For \(0\le r\le L\) its scalar debit is \(\min(r+1,L-r+1)\); it is zero afterwards. In either parity the sum of this list is at least \(L\): both endpoints have value one and every interior value at least two, with the parity counts giving the stated bound even when the endpoints have the same parity. Adding \(L\) back therefore cannot beat the old parity count on those nominal estimates. The improvement in (2) is exactly the **measured** tail dimension, actual read-rank refunds, or the additional coupling described in the companion note.

In mixed DIRK the two penalties in (2) may be substantial. The expression must be taken in maximum with already proved unrestricted floors and with the global (uncut) nullity bound, not added to either. This comparison does not change the unrestricted stage table.
