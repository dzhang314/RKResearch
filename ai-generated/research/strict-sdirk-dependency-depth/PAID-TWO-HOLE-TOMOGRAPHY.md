# Two-hole near-full path tests and exact multiplicative obstructions

Use \(s\ge 3\); terms with zero prefactor are omitted before reading any index. The result concerns unrestricted linear recovery of path weights, not necessity within the nonlinear RK-compatible subset.

A mathematical companion for order \(p=s\), a common diagonal
\(A=\gamma I+B\) over a characteristic-zero field, and nonzero longest
strict tall value \(L=b^TB^{s-1}e\). The companion shows \(L\ne0\)
unconditionally for \(s=p\ge7\); the calculation below itself
only assumes \(L\ne0\). No root assumption on \(\gamma\).
Write \(c=Ae\), \(C=\operatorname{diag}(c)\). All path weights are signed
finite sums of actual strict edge products and terminal output weight.

Let \(n=s-2\). Every strict path of length \(s-3=n-1\) retains exactly
\(n\) stages. Its two omitted indices \(1\le j<k\le s\) identify the
path uniquely (or give weight zero if an edge or output vanishes).
Write \(\Omega_{j,k}\) for its weight. Put thresholds \(r=j,\ u=k-1\);
then \(1\le r\le u\le n+1\). At position \(h=1,\ldots,n\) along the
retained stages the physical index is
\[
          h+1_{\{r\le h\}}+1_{\{u\le h\}} .
\]
This follows by counting which of the ordered holes have been passed.
Write \(Y_h\) for the actual clock at that position. Then, with
\(\alpha_h=c_{h+1}-c_h,\ \beta_h=c_{h+2}-c_{h+1}\),
\[
     Y_h=c_h+\alpha_h\,1_{\{r\le h\}}+\beta_h\,1_{\{u\le h\}}.
 \tag{1}
\]
Let brackets denote weighted path summation. Order \(s\) pays
\(\langle1\rangle\), \(\langle Y_h\rangle\), \(\langle Y_h^2\rangle\),
and \(\langle Y_h Y_\ell\rangle\) for every \(h<\ell\): these are
strict words with \(s-3\) factors \(B\) and at most two clocks.
All their exact model values depend only on \(\gamma\) and \(s\).

For specificity, put \(N=s-3\), \(a=h-1,\ b=\ell-1\), and retain
the formal operators \(J,T=J-\gamma I,X\) of the companion.
For \(a\le b\) the two-clock product has model
\[
 T^{N-b}X T^{b-a} X T^a 1
      =2 J^2T^N1+(b+3a)J^3T^{N-1}1
                         +a(b-1)J^4T^{N-2}1 .               \tag{2}
\]
Move the first \(X\) from the right through \(T^a\) using
\([X,T]=J^2\); the second uses \([X,J^2]=2J^3\).
The case \(a=b\) is the same-site square. Apply formal integral
at output. The one-clock model is \(JT^N1+aJ^2T^{N-1}1\).
These formulas agree with the companion's paid maximum order \(s\).

**Exact inversion under local triple distinctness.** Suppose for each
\(h\) the actual triple \(c_h,c_{h+1},c_{h+2}\) is pairwise distinct.
No global distinctness is needed. Degree-two Lagrange polynomials in
\(Y_h\) recover the local measures of states 0,1,2 in (1), hence recover
the marginals \(R_h=\langle1_{\{r\le h\}}\rangle\) and
\(U_h=\langle1_{\{u\le h\}}\rangle\). For \(h<\ell\), the mixed
centered product in (1) gives
\[
 \langle(Y_h-c_h)(Y_\ell-c_\ell)\rangle
     =\alpha_h\alpha_\ell R_h
         +\beta_h(\alpha_\ell+\beta_\ell)U_h
         +\alpha_h\beta_\ell\langle1_{\{r\le h,\ u\le\ell\}}\rangle .
 \tag{3}
\]
This is just the monotonicity \(r\le u\) and \(h<\ell\);
the two cross indicators with \(u\le h\) both reduce to that event.
Divide by \(\alpha_h\beta_\ell\ne0\) to get the joint lower-rectangle
sum for \(h<\ell\); for \(h\ge\ell\) it is already \(U_\ell\).
At the boundaries 0 and \(n+1\), the margins or the total give the
same sums. Finite differences then give every signed
\(\Omega_{j,k}\) uniquely. This is a literal linear inverse from the
paid degree-two moments on the one clock coordinate per position,
and does not assume nonzero individual path weights. Without the
triple-distinct condition keep the paid linear equations, but no
unique inversion is claimed.

**New nonlinear tests in the actual support.** Let \(\omega_j\) be
the signed one-hole weights from the companion. They are themselves
determined by the one-clock words under this same local distinctness
(and more weakly whenever the relevant adjacent gaps do not vanish).
For separated omissions, their actual products factor:
\[
                  L\Omega_{j,k}=\omega_j\omega_k
                     \qquad(k-j\ge2).                       \tag{4}
\]
Indeed a single interior omission \(j\) replaces the two adjacent
edges around \(j\) by the actual skip-one edge \(B_{j+1,j-1}\).
Separated omissions make these replacements independently (when
\(k=j+2\) they share a retained vertex, not an edge).
Omitting the first stage drops the first edge, and omitting the
last drops the last edge and replaces \(b_s\) by \(b_{s-1}\);
these endpoint modifications are also independent of any separated
second hole. Dividing the one-hole and two-hole weights by the
nonzero longest path weight \(L\) proves (4), even when the new
edge or output weights involved are zero. This argument uses
neither an unconstrained abstract path measure nor positivity.

Adjacent double omissions instead expose a single skip-two edge:
with \(a_i=B_{i,i-1}\),
\[
      \Omega_{j,j+1}/L=
             B_{j+2,j-1}/(a_j a_{j+1}a_{j+2})
                     \qquad(2\le j\le s-2).
\]
The two endpoint double omissions are respectively
\(1/(a_2a_3)\) and \(b_{s-2}/(b_s a_{s-1}a_s)\).
Thus the paid data also recover the normalized third-subdiagonal
coefficients and this new endpoint ratio where local inverses
exist. Evaluating the linear inverse in (3), the separated equations
(4) are explicit necessary equations purely in the actual clocks,
\(s\), and \(\gamma\). They involve the two-hole composability of
one physical triangular matrix; a freely chosen measure on paths
need not satisfy them. Neither solvability nor a prohibition with
all nonzero gaps is claimed. In particular they are not by
themselves a stronger numeric \(s\) bound.
