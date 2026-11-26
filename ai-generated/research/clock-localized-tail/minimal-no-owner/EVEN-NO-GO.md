# With a negative preceding prefix, the even-reverse gate requires an interior clock

This sharpens the [finite lower-word test](LOWER-CUT.md) for a leading block at distinct negative abscissae. It does not exclude arbitrary clock choices at minimum width.

## 1. Exact finite identities

Let \(r=2n\), \(n\ge2\), \(m=r+1\), and \(p=2r+1\). Use the repaired early bank with two distinct negative genuine anchors, the same notation \(D(X)=(X-\alpha)(X-a)\), \(J=I_0-\gamma I\), \(J^*=I_1-\gamma I\), and \(\ell=\int_0^1\), with \(\gamma<0\). At minimum width \(L(r)\), take the physical prefix of length \(j=n+1\) from LOWER-CUT.md. Assume its first \(j-1\) sites are distinct negative numbers avoiding the anchors. Set
\[
 G(X)\coloneqq D(X)\prod_{i<j}(X-x_i),\qquad z\coloneqq x_j.
\]
The monic polynomial \(G\) has \(j+1=n+2\) simple negative roots. The actual necessary condition for the exceptional \(z\) is
\[
 \ell(PG(X-z)Q)=\ell(PJ(GQ))=0
    \quad(\deg Q\le n-1),\qquad 0\ne P\in\mathbb P_{\le2n-2}.
 \tag{1}
\]
The finite argument below does not use any contact at length \(r\).

Put \(R\coloneqq I_1 P\), \(u\coloneqq\ell(GR')\) and \(\Theta\coloneqq G'/G\). Thus \(R(1)=0,\ R'=-P\), and \(\deg R\le2n-1\). From the first part of (1), factoring a polynomial minus its value at \(z\), and from the second via the exact adjoint, one obtains
\[
 \ell(GQ R')=uQ(z)\quad(\deg Q\le n),\qquad
 \ell(GA R)=-\gamma u A(z)\quad(\deg A\le n-1).
 \tag{2}
\]
For \(A,B\in\mathbb P_{\le n-1}\), integrate the first identity with \(Q=B\) by parts to obtain
\[
 \ell\bigl(GR(A+\Theta B)\bigr)
  =u[-\gamma A(z)-B(z)+\gamma B'(z)]
                         -G(0)R(0)B(0).                     \tag{3}
\]
With \(Q=(X-z)B\), the same integration and (2) give, for \(C\in\mathbb P_{\le n-2}\),
\[
 \ell\bigl(G(X-z)R(C+(\Theta+t/(X-z))B)\bigr)
   =\gamma u(1-t)B(z)+zG(0)R(0)B(0)                         \tag{4}
\]
for any scalar \(t\). Here the apparent pole at \(z\) is cancelled by the outside factor, so (4) remains an exact polynomial identity.

## 2. Sign-matching rational functions

We use two elementary positive-residue spaces. For a sum \(S(X)=\sum_\xi c_\xi/(X-\xi)\) with \(c_\xi>0\) on at least \(n\) distinct nonpositive poles, the first space is
\[
       C+S B,\qquad C\in\mathbb P_{\le n-2},\quad
                         B\in\mathbb P_{\le n-1}.
\]
It has dimension \(2n-1\) and a nonzero member has at most \(2n-2\) zeros with multiplicity on the positive ray. If poles are all negative, the same includes zero. For the second space \(A+SB\) with both degrees at most \(n-1\), the dimension and maximum zeros are \(2n\) and \(2n-1\). In both cases independence follows by residues and the number of poles. To prove the zero count, divide a hypothetical function by the nodal hull \(H\) of one more zero than the stated maximum. Its residues are \(c_\xi B(\xi)/H(\xi)\), and the resulting rational function is \(O(X^{-n-1})\) at infinity. The first \(n\) coefficients at infinity vanish and give \(\sum_\xi c_\xi B(\xi)^2/H(\xi)=0\). Since \(H\) has fixed nonzero sign at the poles, \(B=0\) and then the polynomial numerator is zero.

At exactly the maximum number of zero constraints the same argument gives the first \(n-1\) coefficients at infinity zero. Thus \(B\) is the degree-\((n-1)\) polynomial orthogonal through degree \(n-2\) for the positive masses \(c_\xi/|H(\xi)|\); \(B\ne0\) because the polynomial part alone has too small a degree. For strictly negative poles, \(B\) has only simple negative roots. For \(t\ge0\), its sign in the partial-fraction evaluation follows also from the exact identity
\[
 B(t)\sum_\xi\frac{c_\xi B(\xi)}
                   {|H(\xi)|(t-\xi)}
   =\sum_\xi\frac{c_\xi B(\xi)^2}
                   {|H(\xi)|(t-\xi)}>0 .                     \tag{5}
\]
It uses orthogonality against \((B(t)-B(X))/(t-X)\). These facts do not require the roots prescribed for \(H\) to be simple: zeros with even multiplicity can be used without changing a function's sign on the interval.

The nonzero \(R\) in (1) has at most \(2n-2\) interior sign changes because it already has the endpoint zero at \(1\). In either space choose functions vanishing at those changes and fill any extra zero constraints as indicated below. Such a nonzero function exists by dimension, has exactly the specified multiplicities by the zero count, and can be oriented to have the same sign as \(R\) immediately to the right of zero and throughout each sign interval in \((0,1)\).

## 3. No nonpositive or right-exterior next clock

If \(z\le0\), use (4) with \(t=1\) and \(S=\Theta+1/(X-z)\). Its positive residues are on nonpositive poles (a coincident pole just adds the two positive residues). In the first space place \(2n-2\) positive zeros, including the sign changes of \(R\) and completing them beyond \(1\). Orient the function \(f=C+S B\) so that \(fR\ge0\) on \((0,1)\). The left side of (4) is then strictly positive. If \(z=0\), the right side is zero. If \(z<0\), the selected nodal hull \(H\) is even degree, so \(H(0)>0\) and the residue formula and (5) show that \(f(0)\) has the sign of \(B(0)\), both nonzero. Thus \(R(0)B(0)\ge0\) and the right side \(zG(0)R(0)B(0)\) is nonpositive. Both cases contradict (4).

If \(z\ge1\), first use (4) with \(t=0\) and the first space \(h=C+\Theta B_1\). Place the maximum \(2n-2\) zeros as before, including all sign changes of \(R\) and filling beyond \(1\). Orient \(hR\ge0\). Its value at zero has the sign of \(B_1(0)\) by the even degree argument; \(B_1(z)\) has the same sign since all its roots are negative. Now \(\ell(G(X-z)Rh)<0\) whereas \(zG(0)R(0)B_1(0)\ge0\). Because \(\gamma<0\), (4) implies \(uB_1(z)>0\).

Use (3) with the second space \(f=A+\Theta B_2\). Place \(2n-1\) zeros, including every sign change of \(R\), and add the remaining multiplicities in pairs at unused interior sites, with one unpaired zero at \(z\) if needed. This allows \(z=1\) and preserves sign matching in the entire open interval. With \(H_2\) the monic hull of these zeros, \(H_2(0)<0\), \(H_2(z)\ge0\). By the odd degree residue formula and (5), \(f(0)\) has the sign of \(B_2(0)\), and \(f(z)/B_2(z)\le0\). At \(H_2(z)=0\) the latter follows directly from \(f(z)=0\). Also \(B_2(z)\) has the same sign as \(B_2(0)\), and \(B'_2(z)/B_2(z)\ge0\) since the roots are negative. Therefore the coefficient of \(u\) in (3), divided by \(B_2(z)\), is
\[
 -\gamma f(z)/B_2(z)+\gamma\Theta(z)-1+
                       \gamma B'_2(z)/B_2(z)<0.
\]
With \(fR\ge0\), the integral in (3) is positive and its boundary term is nonpositive. Thus \(uB_2(z)<0\). This contradicts \(uB_1(z)>0\): both \(B_1(z)\) and \(B_2(z)\) have the sign of \(R\) just right of zero by construction, whether or not \(R(0)\) is itself zero.

It follows that any actual exception after the stated negative prefix must have \(0<z<1\); this is not merely exclusion outside a generic set. If the prefix includes earlier nonnegative sites or \(\deg R=2n\), the sign argument above is not asserted.

## 4. At most \(n-1\) remaining interior candidates

For a fixed negative preceding prefix, the \(n\) second-block functionals in (1) are already independent on \(\mathbb P_{\le n-1}\). Indeed, for a nonzero \(P\) in that space put \(F=I_0(GP)\). Then
\[
 \ell(PJ(GP))=\left[\frac{F^2}{2G}\right]_0^1+
           \frac12\ell(F^2G'/G^2)-\gamma\ell(GP^2)>0 .
\]
The first two terms are nonnegative because \(G>0,G'>0\) on \([0,1]\) and \(F(0)=0\); the last is strictly positive. Thus the square test map is injective and the second group is independent. The fixed-prefix limiting argument in LOWER-CUT.md gives full combined rank \(2n-1\) as \(z\to+\infty\), after dividing the first group by \(-z\). Hence some minor can include all \(n\) constant second rows and \(n-1\) first rows, with nonzero leading coefficient. Its degree in \(z\) is at most \(n-1\). Every exception must be a root of it, so at most \(n-1\) interior sites survive, and they are real algebraic when the prefix is.

For the balanced odd targets through \(20\) with even reverse \(r\), this applies to \(p=9,13,17\). They may have separate scalar-grid or architecture constraints; this proof requires only the actual double-factor contacts and strict chronology, and does not exclude an interior next stage, a mixed preceding prefix, or a wider bank.
