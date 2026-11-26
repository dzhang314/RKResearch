# The first mixed equations force an active tail

The literal seed with reserved trailing abscissae cannot be completed at minimum width. The minimum is also impossible for arbitrary strict feedback on the specified canonical reflected Laguerre abscissae when the reverse budget is even and the stated scalar is nonzero, in particular for negative diagonal. This does not exclude a different choice of abscissae, extra stages, nonzero early output weights, or unrestricted strict SDIRK.

## 1. The numerical kernel at minimum width is exhausted

Let \(p=m+r\), \(r\le m\), with \(r\ge3\). Keep a closed canonical minimum forward SDIRK cache of cap \(m-1\), with common diagonal \(\gamma\ne0\), zero output weights, and actual paid numerical columns spanning that bank. Use distinct true late clocks \(x_i\) and no other pure scalar rows, with strict late matrix \(T\), row output weights \(b\), and true late local order through order \(m\), as in the direct no-owner construction. Set \(y_i=1-x_i\), \(M=\operatorname{diag}(y_i)\), and \(B=T+\gamma I\). For a row functional, let letter \(Y\) multiply the row by \(M\), and \(J\) multiply it by \(T\). Their formal counterparts on polynomials in \(Y\) are multiplication by \(Y\) and \(L=I_0^Y-\gamma I\). Thus the ordinary primitive letter \(B\) has formal counterpart \(I_0^Y\). The actual word rows start from \(b\). Write \(V_k\) for their span through word length \(k\).

If rooted order \(p\) holds, the actual numerical word rows through length \(r-1\) admit their exact formal polynomial profile, with no ambiguity. To see it, let \(K_n\) be the exact model image of order-\(\le n\) rooted combinations whose actual early numerical data vanish. Then \(K_n=\mathbb P_{\le n-1}\) for \(n\ge m+1\): the ordinary early commutator \([C_F,A_F]-A_F^2\) is invertible with diagonal \(-\gamma^2\) and sends every model to zero. Its application to the full actual paid span through \(m-1\) therefore supplies numerical corrections, with zero exact model, through \(m+1\). Subtract such a correction from any desired polynomial representative. Now test any numerical-null row combination of words of length at most \(k\le r-1\) against true rooted heads in \(K_{p-k}\). Unary extensions and marks keep the early numerical zero, so these are actual summed order equations. The model polynomial of the combination pairs to zero against all \(\mathbb P_{\le p-k-1}\). The rational Hilbert pairing on \(\mathbb P_{\le k}\) is nonsingular, and \(p-k-1\ge k\). Thus the model polynomial is zero. This argument uses actual early-null heads even if their high late values are not pure point evaluations.

Consequently the numerical model-null subspace \(N_k\subset V_k\) has codimension \(k+1\). Let
\[
                    \Omega=BM-MB-B^2 .
\]
As a right row operator its model is \(YI_0^Y-I_0^Y Y-(I_0^Y)^2=0\). Its literal diagonal is \(-\gamma^2\), so \(V_{k-2}\Omega\) is an injective subspace of \(N_k\). Thus \(\dim V_k\ge\dim V_{k-2}+k+1\), with bases \(1,2\) as lower bounds at lengths zero and one. If the physical late width is exactly \(d=L(r)=\lfloor(r+1)^2/4\rfloor\), the ordinary lower bound at \(r-1\) is saturated. Every inequality of that parity must be equality, so
\[
 N_k=V_{k-2}\Omega\quad(2\le k\le r-1,\ k\equiv r-1\bmod2),
 \qquad \dim V_k=L(k+1)\quad(k\equiv r-1\bmod2).
 \tag{1}
\]
This proves exhaustion of the **actual** numerical kernel, not just a formal independence count. All computations below use this exact consequence of full rooted order.

## 2. A common dead tail rents a linear number of rows

Allow arbitrary clocks, and suppose a physical trailing cohort of sites is zero in every first-primitive response \(bM^aT\), \(0\le a\le r-1\). Let \(t\ge1\) be the number of distinct clocks in that cohort with nonzero \(b_i\). On the cohort every word containing \(T\) vanishes, because the first such word already does and strict \(T\) moves support only earlier. Thus the restriction of \(V_k\) has rank \(t_k=\min(t,k+1)\) and is spanned by the restricted pure marks. On that cohort \(v\Omega=-\gamma^2v\) for \(v\in V_{k-2}\): in \(\Omega=TM-MT-T^2-2\gamma T-\gamma^2I\) every strict part still vanishes there. Hence \(V_{k-2}\Omega\) has restricted rank \(t_{k-2}\).

For \(k\ge2\), the two genuine model-zero types
\[
              bM^aB-\frac{bM^{a+1}}{a+1},\qquad a=k-2,k-1,
\]
have on the cohort polynomial leading degrees \(k-1,k\) with nonzero leading coefficients, since their strict term vanishes. Together with the earlier degree-\(\le k-2\) tail they give exactly \(t_k-t_{k-2}\) new independent restrictions, and hence at least that many new full numerical kernel directions. Therefore
\[
  \dim V_k\ge \dim V_{k-2}+k+1+t_k-t_{k-2}.
\]
The \(k=0\) base is \(1\); the \(k=1\) base satisfies \(\dim V_1\ge2+t_1-1\), because \(bB-bM\) is a nonzero zero-model row on two distinct active trailing clocks. Telescoping either parity gives
\[
                      d\ge L(r)+\min(t,r)-1 .
 \tag{2}
\]
No sign or location of the clocks was used. Thus the previous literal seed and shared pivot construction, with all first-primitive responses supported before its last \(r\) nonzero-weight sites, cannot be completed by paying more mixed contacts at width \(L(r)\). It would require at least \(r-1\) additional late rows. Merely changing those allotted sites from exterior to interior does not fix the dead-tail rent. This does not invalidate the partial projection, which did not claim full rooted order and did not have the decoder of §1.

## 3. The first clock is forced even without the dead-tail ansatz

At exact minimum even \(r\), (1) gives \(\dim V_1=2\); since the mark and ordinary primitive have the same degree-one model,
\[
                      q_0:=bT=b(M-\gamma I).
 \tag{3}
\]
The final physical weight \(b_d\ne0\): if zero, that row has neither downstream taps nor output and can be removed, contradicting the \(L(r)\) bound. Thus \(y_d=\gamma\). The penultimate weight is nonzero as well: otherwise (3) forces \(T_{d,d-1}=0\), making that row removable. In particular \(T_{d,d-1}\ne0\) for distinct clocks.

Equation (3) is also forced at minimum odd \(r\) with distinct clocks. Here (1) gives \(N_2=\operatorname{span}\{b\Omega\}\), so \(b(B-M)=\lambda b\Omega\). Write \(z=y_d\), and evaluate on the final coordinate, where only the diagonal of every triangular operator contributes. The scalar is \(\lambda=(z-\gamma)/\gamma^2\). The zero-model rows \(bMB-\frac12 bM^2\) and \(bB^2-\frac12 bM^2\) have coefficients \((z^2/2-\gamma z)/\gamma^2\) and \((z^2/2-\gamma^2)/\gamma^2\) of \(b\Omega\). Their difference is \(b(B-M)B=\gamma\lambda b\Omega\). If \(\lambda\ne0\), it follows that \(b\Omega T=0\). The penultimate coordinate then forces \(T_{d,d-1}=0\), since \((b\Omega)_d=-\gamma^2b_d\ne0\). This penultimate row has nonzero weight, again because it would otherwise be removable. At that coordinate \(b(B-M)=\lambda b\Omega\) now forces \(y_{d-1}=z\), contradicting distinct clocks. So \(\lambda=0\), proving (3) and \(y_d=\gamma\) also for odd \(r\).

In either parity, when \(\gamma<0\) a purely interior late grid cannot meet minimum width: at least the final clock \(x_d=1-\gamma>1\) is forced. Mixed grids are not thereby excluded.

## 4. Even-rigidity and the canonical clock-set exclusion

Assume \(r\ge4\) is even. By (1), \(N_3=\operatorname{span}\{b\Omega,bM\Omega\}\). Restriction to the last two coordinates is injective on this space: \(\Omega\)'s last two square triangular block is invertible, the two weights are nonzero, and the two clocks are distinct. A word containing two strict primitives is zero on the last two coordinates; a word containing one is zero on the last one. Consider the following zero-model combinations, with the output-to-source word convention:
\[
 \begin{aligned}
 \tau&=JJY-2JYJ+YJJ,\\
 \rho&=JYY-4YJY+3YYJ,\\
 \sigma&=JYY-2YJY-2\gamma(JY-YJ).
 \end{aligned}
 \tag{4}
\]
The formal identities follow by \(LY^a=Y^{a+1}/(a+1)-\gamma Y^a\). Explicitly the three two-primitive polynomials in \(\tau\) are \(Y^3/2-2\gamma Y^2+\gamma^2Y\), \(Y^3/3-3\gamma Y^2/2+\gamma^2Y\), \(Y^3/6-\gamma Y^2+\gamma^2Y\); for the one-primitive relations the three length-three polynomials have the same \(-\gamma Y^2\) term, and \(P_{JY}-P_{YJ}=Y^2/2\). Exhaustion of \(N_3\) now gives
\[
       a_\tau=0,\qquad a_\rho,\ a_\sigma\ \in\ \operatorname{span}\{q_0\Omega\}.
 \tag{5}
\]
Indeed the last-coordinate cancellation for the latter forces the polynomial \(bM-\gamma b=q_0\) before \(\Omega\).

Set \(z=y_{d-1}\), \(x=y_{d-2}\). The coefficient of \(a_\tau\) at \(d-2\) is
\[
                  b_d T_{d,d-1}T_{d-1,d-2}(x-2z+\gamma).
\]
Hence \(T_{d-1,d-2}\ne0\) forces the arithmetic relation \(x=2z-\gamma\). If instead \(T_{d-1,d-2}=0\), both penultimate and antepenultimate columns receive their strict input only from \(d\). The antepenultimate weight is nonzero, since (3) would otherwise also force its tap to \(d\) zero and the row would be removable. At either of these two sites \(i\), \(q_j(i)=\gamma^j q_0(i)\) for \(q_j=bM^j T\), and \((q_0\Omega)_i=-\gamma^2q_0(i)\) (the potential other last-coordinate tap in that block is zero). The actual \(\rho\) coefficient divided by \(q_0(i)\) is \((y_i-\gamma)(y_i-3\gamma)\). Equality of the proportionality constants in (5) forces \(x+z=4\gamma\), since \(x,z\) are distinct.

Now suppose the late clock multiset is exactly the reflection of an actual canonical minimum reverse Laguerre cache of cap \(r\): its forward labels \(y\) consist of \(\min(j,r+1-j)\) selected actual roots of \(W_j(Y)=j!(I_0^Y-\gamma I)^j1\) at each level \(1\le j\le r\). In particular the selected level-one root is \(\gamma\), and **both** level-two roots are present. The \(y/\gamma\) are distinct ordinary Laguerre roots. We use only the following standard arithmetic property of the canonical clock data: the ordinary Laguerre polynomial of each degree \(j\) is irreducible over \(\mathbb Q\) (Schur), and the mean of its roots is \(j\), by its next-to-leading coefficient. These facts suffice; no assumption on the full Galois group is made. A nonconstant rational affine relation between two roots gives the same degree for both and maps their full conjugate root set to itself. The arithmetic branch \(x/\gamma=2(z/\gamma)-1\) would force \(j=2j-1\), hence \(j=1\) and identical labels, impossible. The mirror branch \(x/\gamma=4-z/\gamma\) forces \(j=2\). Therefore the two labels are exactly the degree-two siblings and their literal adjacent tap is zero. This argument does not assume the whole reverse matrix was initially the old Laguerre one.

At site \(d-1\), direct evaluation of (4) gives
\[
 \begin{aligned}
 (a_\rho)_{d-1}&=q_0(d-1)(z^2-4\gamma z+3\gamma^2),\\
 (a_\sigma)_{d-1}&=q_0(d-1)(z^2-4\gamma z+2\gamma^2).
 \end{aligned}
\]
Here \(W_2(z)=z^2-4\gamma z+2\gamma^2=0\), and \((q_0\Omega)_{d-1}=-\gamma^2q_0(d-1)\ne0\). Thus (5) forces \(a_\rho=-q_0\Omega\) and \(a_\sigma=0\) **globally**. On every clock \(y_i\ne\gamma\), the literal identity
\[
                   a_\sigma=q_0(M^2-2\gamma M)-2q_1(M-\gamma I)
\]
and (3) now give \(q_1(i)=b_i(y_i^2/2-\gamma y_i)\). The unique remaining coordinate \(d\) has \(q_1(d)=0\) by strictness, whereas the formal factor \(LY\) there is \(-\gamma^2/2\). Hence the entire actual error is the nonzero singleton
\[
               q_1-b\, (M^2/2-\gamma M)
                   =\frac{b_d\gamma^2}{2}\,e_d^{\mathsf T}.
 \tag{6}
\]
This deduction allowed signed weights and even zero weights away from the first active slots.

### One true detecting rooted equation

Use the shifted tall tree of order \(m\). Its canonical early numerical column is zero since the strict early cache has depth at most \(m-1\), while its exact model at physical clock \(X\) is \(P(X)=W_{m-1}(X)/(m-1)!\). The late bank is locally exact through order \(m\), so its actual column is \(EP\). Adjoin one unary root, followed by the single root mark \(Y=1-X\); in shifted rooted notation the \(X\) mark on \(t\) is \(t\#[\bullet]+\gamma t\). This is a combination of trees through total size **\(m+2\)**. It stays early-null and tests precisely \(bMT\,EP=q_1 EP\). Its exact target is \(\ell(YJP)=\ell((LY)P)\). Because ordinary root-bush order supplies the scalar rule through degree \(p-1\), the direct sampled polynomial \(bE((LY)P)\) gives the same target (its degree is \(m+1\le p-1\)). Equation (6) contradicts this rooted equation whenever
\[
                          W_{m-1}(1-\gamma)\ne0.
\]
In particular every prescribed negative real-algebraic \(\gamma\) satisfies the condition, as the roots of \(W_{m-1}\) are negative and \(1-\gamma>1\). No special norm calculation for any order is required.

For balanced \(m=\lceil p/2\rceil,\ r=\lfloor p/2\rfloor\), the even-\(r\) claim through \(p=20\) applies individually to \(p=8,9,12,13,16,17,20\). The additional canonical-shape exclusion beyond the earlier minimum-bank scalar/parity screens is at \(12,16,20\). The other four were already excluded in this geometry by exterior scalar support and/or parity. It does not settle arbitrary feedback on canonical sites at the compatible odd-\(r\) orders \(14,15,18,19\). It makes no unrestricted stage-table change.

## 5. A concrete finite gate for genuinely mixed clocks

Even for an arbitrary mixed/distinct grid, retain \(y_d=\gamma\) and set \(z=y_{d-1}\). If \(W_2(z)=0\), (5) makes \(a_\sigma=0\) globally just as above, so the singleton contradiction already follows when \(W_{m-1}(1-\gamma)\ne0\). Thus a viable negative-diagonal minimum design with even \(r\) needs
\[
          \kappa\coloneqq -W_2(z)/\gamma^2\ne0 .
\]
Its first three slots must satisfy the arithmetic or mirror branch of §4. If there is only one exterior clock and the next two lie in \([0,1]\), the mirror relation \(x+z=4\gamma<0\) is unavailable; use an adjacent-tap arithmetic triple if trying that mixed geometry. These are literal necessary constraints, not a proof that such a grid works.

One can now avoid treating the first missing mixed equations as unrelated interpolation problems. Let \(u_j\) be the actual proposed \(bT^j\), with \(u_1=q_0=b(M-\gamma I)\). Propose \(u_2,u_3,q_1\) satisfying their true measured moment gates. Define
\[
 \begin{aligned}
 S&=u_1(M^2-2\gamma M)-2q_1(M-\gamma I),\qquad K=S/\kappa,\\
 v_1&=u_2 M-u_3-2\gamma u_2-\gamma^2u_1-K,\\
 v_2&=2v_1-u_2 M,\\
 q_2&=((\kappa-1)K-u_1M^2+4q_1 M)/3 .
 \end{aligned}
 \tag{7}
\]
The first unpaid two-primitive mixed responses must be \(v_1=a_{JYJ}\), \(v_2=a_{YJJ}\); \(a_{JJY}=u_2 M\). Indeed \(K=q_0\Omega\) follows from \(a_\sigma=\kappa q_0\Omega\); \(a_\tau=0\) gives \(v_2=2v_1-u_2M\); and the actual coefficients at \(d-1\) show \(a_\rho=(\kappa-1)q_0\Omega\). These determine (7). Conversely use the following seven input rows and requested primitive outputs:
\[
  (b,\ bM,\ bM^2,\ u_1,\ u_1M,\ q_1,\ u_2)
       \longmapsto
  (u_1,\ q_1,\ q_2,\ u_2,\ v_1,\ v_2,\ u_3).
 \tag{8}
\]
For each physical column restrict the seven inputs to strictly later sites. The requested output column has a literal strict realization exactly when it kills every relation on that actual restriction. This is the existing causal kernel check, now a seven-row test for **all** word responses up to length three. If this test passes, the matrix really realizes the equations (7) and the complete length-three dictionary with true clocks; it does not merely realize a model-zero projection.

In this gate, measured source validation of \(v_1,v_2,q_2\) introduces no additional scalar conditions if \(u_1,u_2,u_3,q_1\) were already paid on the indicated actual graded bands (with the affordable marked versions). The formal combinations \(S,K\) are identically zero on the order-\(\le p-3\) source tests under those assumptions. The nonzero part of \(v_1\) has model
\[
                   YL^2 1 - L^3 1-2\gamma L^2 1-\gamma^2 L1
                       = L(YL1),
\]
and \(2P_{v_1}-YL^2 1=L^2Y\), the model for \(v_2\). The formula for \(q_2\) is the corresponding formal \(\rho\) identity. Thus the remaining difficulty at this first mixed shelf is genuinely the common physical column realization (8), not recovering the scalar word formula. Higher mixed shelves and exact next-order construction are not established by the length-three gate.
