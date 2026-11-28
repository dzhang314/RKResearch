# The nonzero-mass mixed calibration overlap cannot have two crossing pairs

**Scope.** Continue the characteristic-zero
[eight-clock n13 finite atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md).
At a *mixed* overlap \(a=e\) or \(h=d\) between the two front
calibrations, at most one ordinary pair can occur on both fronts.
This excludes two crossing pairs in those overlap charts,
not one cross, the half-half overlap, four distinct calibrations,
the six-pair branch, or 17-stage order eleven in general.
No ordered-field inequality or reverse order eleven is used.

## 1. Literal two-cross pattern and its two equalities

Write \(a=2c_3\), \(b=1-c_{14}\), \(d=1-b\), \(h=a/2\),
and \(e=1-b/2\) in the earlier physical orientation. At \(a=e\)
the right half-plateau joins the left plateau's two actual
occurrences, so the unique active triple is at \(a\).
The opposite plateau \(d\) is occupied twice at the right.
Both fronts must select their two extra active labels from
the same three uncalibrated roots. If two ordinary pairs
cross, both fronts select the **same** two roots \(t,u\),
with remaining root \(w\). We do not order sixth versus
seventh: the row-7/row-11 contact is symmetric in the two extras.

Let \(Q(X)=X^3+q_2X^2+q_1X+q_0\) be the monic cubic cofactor of
\(H_6=(X-a)(X-a/2)(X-d)Q(X)\). The overlap fixes
\(b=2-2a,\ d=2a-1\). The finite-atlas pivot theorem makes the
cubic moment determinant nonzero. Since \(w,t,u\) are the
three distinct remaining roots,
\[
 s=t+u=-q_2-w,\qquad p=tu=q_1+w(q_2+w).
\]
Use these in the inverse-Gram contact \(\Psi\) with
\[
 \ell_0=a^2-as+p,\quad \ell_1=-p,\qquad
 r_0=d^2-ds+p,\quad r_1=-(1-s+p).
\]
The actual off-diagonal row pairing gives \(\Psi=0\) at \(w\).

There is a second clock equation. At a crossing pair \(x\),
the local product of the two physical responses in scale \(F\)
is \(-\mu_x/B_x\), and their calibrated forward and reverse
observations are \(x^2(a-x)/a\) and \((1-x)^2(x-d)/b\). Hence
\[
 k\kappa=-B_x H'_6(x)\frac{x^2(1-x)^2(a-x)(x-d)}{ab}.
\]
Here \(\mu_x=k/H'_6(x)\) by the actual paid square moments,
and the two response scales are \(G=\kappa F\). The pair weight
\(B_x\) is its ordinary scalar pool. The eight scalar clocks
are distinct, so degree-seven scalar Lagrange testing gives
\[
 B_x H'_6(x)=\frac{\mathcal J(x)}{x(x-1)},\qquad
 \mathcal J(y)= \int_0^1 X(X-1)
              \frac{H_6(X)-H_6(y)}{X-y}\,dX .
\]
The quotient in \(\mathcal J\) is the formal polynomial divided
difference, requiring no specialization denominator. Therefore
\[
 \Xi(y)=\mathcal J(y)y(1-y)(a-y)(y-d),\qquad \Xi(t)=\Xi(u).
\]
The pair sites are distinct nonendpoints, neither is a plateau,
and all ordinary masses and response scales just used are live.
Reduce \(\Xi(Y)\) modulo \(Y^2-sY+p\); its linear coefficient
\(\gamma(w)\) must be zero since \(t\ne u\). There is no
division by \(\gamma\) or a projected pure volume.

## 2. Exact cleared coefficient norm and coprimality

The cubic moment matrix has determinant \(-D/21337344000\), where
\[
 D=14112a^9-95256a^8+278124a^7-462126a^6+482244a^5
      -328125a^4+145804a^3-40926a^2+6624a-476 .
\]
The receipt derives this from the rational weight moments of
\((X-a)(X-a/2)(X-d)\). Put \(M=66D\ne0\).
The integer numerators \(r_j\) in the receipt satisfy
\(q_j=r_j/M\) by the unique moment solve; its three equations
are checked after clearing denominators.

Use the monic quotient for \(W=Mw\):
\[
 W^3+r_2W^2+M r_1 W+M^2r_0=0.
\]
The sum and product of the other two **scaled** roots are
\(S=-r_2-W,\ P=M r_1+W(r_2+W)\).
The four contact factors times \(M^2\) are integral:
the first and third are \((aM)^2-(aM)S+P\) and the same
with \(d\), the others are \(-P\) and \(-(M^2-MS+P)\).
Thus the element `contact` equals \(M^4\Psi\).

For the crossover form
\[
 \widehat H=2M H_6=(X-a)(2X-a)(X-d)
                    (MX^3+r_2X^2+r_1X+r_0).
\]
The coefficients of \(\widehat{\mathcal J}=1680M\mathcal J\)
are obtained by multiplying the coefficient at \(X^i\) in
\(\widehat H\) by \(-840/[(i-j+1)(i-j+2)]\) for
\(0\le j<i\) and summing at \(y^j\). All are integers.
Compute \(1680M^{10}\Xi(Y/M)\) and reduce modulo \(Y^2-SY+P\).
The linear coefficient is precisely the element `cross`,
equal to \(1680M^9\gamma(w)\). A Horner step by coefficient
\(c\) changes \(\beta+\gamma Y\) to
\((c-P\gamma)+(\beta+S\gamma)Y\).

An element's norm in the monic cubic quotient is the
3-by-3 multiplication determinant in the basis \(1,W,W^2\).
If the element vanishes at the actual root \(W\), evaluation
gives a nonzero left kernel, so its norm vanishes without
requiring this specialized quotient to be a field. The two
cleared identities are
\[
 \begin{aligned}
 1185921\operatorname{Norm}(\texttt{contact})
     &=66^{12}D^8 N_1(a),\\
 511200087552000\operatorname{Norm}(\texttt{cross})
     &=1680^3\,66^{27}D^{26}N_2(a).
 \end{aligned}
\]
The integer-grid checks use degree bounds 132 for the first identity
and 258 for the second. Assign both \(W\) and \(Y\) degree weight nine,
the degree of \(M\); the monic reductions preserve that weighted
degree. The scaled contact factors have degrees at most \(20,18,20,18\)
and the Gram factors degrees at most \(0,4,4,8\), giving weighted
degree at most 44 for the contact. In the crossover, \(\widehat H\)
has coefficient degree at most 12 in \(a\); \(\widehat{\mathcal J}\)
has the same bound, and multiplication by the four clock factors
increases it by at most two. Multiplying its coefficient at \(Y^j\)
by \(M^{9-j}\) gives weighted degree at most 95; the linear remainder
coefficient has weighted degree at most 86. For an element of
weighted degree \(r\), its multiplication norm has degree at most
\(3r\): the weights of basis powers cancel in each determinant term.
The right sides satisfy the same bounds. Thus the exact grids
\(0,\ldots,132\) and \(0,\ldots,258\) prove both identities.
The residual numerators \(N_1,N_2\) have degrees 60 and 23;
their integer arrays are in the companion. The factors
discarded are only rational nonzero scalars and the
proved-live \(D\). Modulo 103 the numerators retain their
degrees, with leading residues 51 and 62, and a Bézout
combination equals 1. Degree-preserving reduction makes
them coprime over \(\mathbf Q\). The field of the tableau
is not specialized. In any characteristic-zero extension
these numerators cannot share a root, contradicting the
two paid equalities.

At \(h=d\), reflect just this polynomial system: swap \(a,b\),
send \(X\) to \(1-X\), and exchange the fronts. The scalar
quadrature functional is invariant. In the crossover equation,
\(\mathcal J\) and hence \(\Xi\) change sign after reflecting
the active monic even-degree hull, preserving the equality.
The contact Gram equation is symmetric under exchanging the
anchored bases and row roles. The reflected clocks would
therefore solve the excluded \(a=e\) system. This needs no
ordinary reverse order-eleven tableau.

The [Lean companion](../lean/RKCert/ReviewedNative/ERK11MixedOverlapTwoCrossGate.lean) checks the cleared
polynomial arithmetic and modular Bézout identities in the kernel.
An [exact Python replay](erk11-mixed-overlap-two-cross-exit/replay_cleared_standalone.py) checks the same polynomial arithmetic.
The actual order and physical chronology transfers are above.
