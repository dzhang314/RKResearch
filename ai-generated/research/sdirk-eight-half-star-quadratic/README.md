# No coprime quadratic profile with a star end in the half-diagonal SDIRK8 chart

Use the [all-active half-diagonal endpoint pair](../sdirk-eight-half-equal/README.md): a ten-stage strict SDIRK tableau over a characteristic-zero field, common diagonal \(\gamma=1/2\), \(g_1=g_{10}=1/8\), \(g_i=0\) on the eight other physical rows, \(c_1=c_{10}=1/2\), \(b_1=-b_{10}\). Let \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). The earlier [finite quadratic profile theorem](../sdirk-eight-half-quadratic/README.md) reduced its coprime profiles to finitely many clocks and denominator choices. This packet excludes **all** such profiles when either chronological end is in the star phase. The arithmetic–arithmetic case and actual common-root discrepancies remain open. The unrestricted order-eight stage interval is still **10–11**.

The result includes repeated roots of the quadratic denominator and repeated physical clocks permitted by the earlier chart. No positivity, ordering, or real closure is used.

## 1. Explicit regular projection to one clock

Assume the front phase is star. Let \(a,b,s,y,c,d\) be the six literal zero-row clocks of the [finite quadratic reduction](../sdirk-eight-half-quadratic/README.md), so \(s=c_4,y=c_5\). Work over \(K_0=\mathbb Q(t)\), \(t^2=1/2\), with front sign fixed. The literal fifth-clock equation gives \(y=3s/2-1/4\) or \(y=103/72-s\). Check both branches, and the rear star and two rear arithmetic signs. With the generic pivots, recover \(h_y\) from the first affine rank read; the three values at \(a,b,s\) interpolate \(p\in\langle L_3,L_4,L_5\rangle\) as a linear function of the coefficients of monic \(q=X^2+\alpha X+\beta\). The fourth value solves \(\alpha\) as an affine function of \(\beta\). The rear ratio is quadratic in \(\beta\), giving a monic binary quotient
\[
                         B=K_0(s)[\beta]/(\beta^2+r_1\beta+r_0).
\]
These generic operations are used only away from the scalar numerator and denominator supports of the exact chart pivots. The replay returns those univariate factors automatically.

Write \(R_\rho=\det m_p\) in \(B[X]/(q)\), i.e. the norm of the residue of \(p\) in that monic degree-two quotient. It detects coprimality in each scalar fiber. For this *generic* computation we also avoid the scalar numerator and denominator supports of \(\mathrm N_{B/K_0(s)}R_\rho\), so \(p\) can be inverted modulo \(q\). A zero of that auxiliary norm does **not** imply that \(p,q\) share a root at the actual \(\beta\). All such scalar fibers are handled separately below.

Let \(P_6(X)=\prod_{x\in(a,b,s,y,c,d)}(X-x)\), including multiplicities. Compute \(T_j=\ell(P_6X^j/q^2)\) for \(0\le j\le5\), with the \(\ell\) of the preceding profiles. The [exact projection code](star_projection.py) avoids a large residue Cramer determinant as follows. For \(f=P_6X^j\), first divide by \(q^2\), giving quotient \(V\) and remainder \(W\). Put
\[
      r=\operatorname{rem}_{q}(W p^{-2}),\qquad
      u=\operatorname{rem}_{q}\bigl((W-rp^2)/q \;\cdot p^{-1}\bigr)
\]
where the inverse powers are taken modulo \(q\). Both \(r,u\) are linear and
\[
                       W\equiv r p^2+u q p\pmod{q^2}.
\]
The first division in the second formula is exact. Paid pure moments give \(\ell(rp^2/q^2)=\ell(uqp/q^2)=0\). Thus
\[
 T_j=I(V)-I\bigl(\operatorname{quo}_{q^2}(r p^2+u q p)\bigr),\qquad I(X^j)=1/(j+1).
\]
Every quotient integrated here has degree at most seven. The exact code checks the four coefficient identities in the remainder basis before applying \(I\).

Only the two still-unpegged physical zero rows contribute to the \(T_j\). Thus the three rank-three Hankel minors
\[
 G_0 = \det[T_{i+j}]_{i,j=0}^2,\quad
 G_1 = \det[T_{i+j+1}]_{i,j=0}^2,\quad
 G_2 = \det[T_{i+j}]_{i\in\{0,1,2\},\,j\in\{0,1,3\}}
\]
all vanish at every actual profile. This uses no positivity or clock distinctness. Take the three binary norms \(\mathrm N_B(G_j)\) and the cross determinant of the two affine coefficient lists of \(G_0,G_1\) in \(\{1,\beta\}\). An actual regular \(s\) is a root of their numerator gcd (one may enlarge it by taking norms over the two signs of \(t\)). In every phase, the exact gcd has all its factors among the guarded scalar factors: the replay verifies each denominator support, makes the gcd squarefree, and removes only factors of the recorded guard support. The leftover is constant. This leaves an explicit finite product of scalar exception polynomials, not an omitted generic case.

## 2. Saturated good reduction in finite quotients

Let \(M\) be a monic irreducible \(\mathbb Q\)-factor of the recorded scalar support of degree \(n\). In the finite quotient \(K_0[s]/(M)\), where the generic reconstruction coefficients are defined, take the monic rear quadratic again. This is a free algebra \(D\) of dimension \(2n\) over \(K_0\). Recompute the *scaled* \(T_j\) by Cramer's rule (with no inversion of \(R_\rho\)), and the corresponding Hankel minors. On every coprime root they vanish as before.

At a geometric point where \(q,p\) have a shared root \(r\), all four residue inputs \(q p,Xq p,p^2,Xp^2\) belong, even after reduction modulo \(q^2\), to the dimension-two space of multiples of \((X-r)^2\) of degree at most three. The determinant and all three-by-three cofactors of this residue matrix vanish. Hence the Cramer-scaled \(T_j\) and every Hankel minor vanish at this geometric point as well. The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8SharedRootResidues.lean) proves the shared-root divisibility and the degree-one quotient bound, including repeated roots of \(q\).

We count a lower bound on the number of these **known bad geometric points**, not roots in a finite residue field. Write \(\mathrm N_B(R_\rho)=(u+t v)/w\) with \(u,v,w\in\mathbb Q[s]\); all denominators in this test must be units in the monic scalar quotient.

* If \(M\nmid u^2-v^2/2\), take the lower bound zero.
* If \(M\mid u,v\), all \(n\) geometric \(s\) values have at least one bad \(\beta\). Take lower bound \(n\).
* Otherwise, if \(M\mid u^2-v^2/2\), the irreducible \(\mathbb Q\)-factor splits over \(K_0\) into two conjugate factors of degree \(n/2\), one dividing \(u+t v\). To see this, in \(\mathbb Q[s]/M\) the ratio \(u/v\) gives a square root of \(1/2\); the two embeddings of that quadratic extension partition the \(n\) conjugates equally. Exactly this half of the geometric \(s\) values have a bad \(\beta\). Take lower bound \(n/2\).

At least one independent evaluation functional for each of these bad geometric points annihilates any multiplication map by a combination of the scaled Hankel minors. Therefore the characteristic-zero multiplication kernel has dimension at least the given bound. A genuine coprime candidate is a **different** geometric point and would increase it by at least one. This reasoning needs no semisimplicity of the rear quadratic.

For an upper bound on the kernel, reduce the fixed monic quotient bases at a good prime (the replays use \(1009,t=285\)). Check all rational denominators and pivot units, keep the mod-prime scalar polynomial squarefree of degree \(n\), and compute the multiplication rank. For \(A=a+b\beta\) in the reduced algebra the kernel dimension is exactly
\[
 \deg\gcd(M,\mathrm N_B(A))+\deg\gcd(M,a,b).
\]
Indeed over each field factor of the squarefree scalar base, its \(2\times2\) multiplication matrix has rank two if its norm is nonzero, rank zero if both coefficients vanish, and rank one otherwise. When the resulting dimension matches the exact lower bound, good reduction only **raises** kernel dimension. Thus there is no additional characteristic-zero point with \(A=0\) and \(p,q\) coprime. For example, a degree-60 scalar factor requires and has kernel dimension 30, not an invertible full multiplication matrix.

If the generic coefficient pivots are not valid on a scalar factor, the [finite fiber replay](check_star_family.py) recomputes the actual \(H\)-read, the Legendre interpolation at either third front point, and the affine denominator pencil over the exact finite quotient. A nonunit splits that quotient by an exact gcd; it is never treated as invertible or discarded solely by mod-prime behavior. The rear polynomial may drop degree. If its quadratic has a shared-root fiber but \(R_\rho\) is not identically zero there, its unique possibly coprime \(\beta\) is the other root of the rear quadratic, computed from the trace and the linear zero of \(R_\rho\). On the remaining monic fibers the replay verifies a scaled Hankel unit by reduction, preserving the finite bases and all divisors. These paths also exclude scalar fibers with literal twins, the forbidden early rank singularity, or no monic interpolant. Any possible fallthrough fails an assertion rather than certifying a case.

## 3. Reflection and reproducibility

The full weighted reflection in the all-active endpoint chart has the same constant diagonal. It swaps the two endpoint phases and sends \(c\) to \(1-c\), and the normalized reverse cubic defect is a nonzero scalar multiple of the forward one. A coprime quadratic relation transfers by \(X\mapsto1-X\), since each shifted Legendre \(L_j\) changes by \((-1)^j\) and the reflected quadratic stays monic. Therefore the six front-star replays also exclude a rear star with an arithmetic front, without a second computation.

From this folder within the repository run `python3 check_star_family.py`. It imports the [preceding literal-front checker](../sdirk-eight-half-quadratic/literal_front.py) and uses Python 3 with `sympy==1.14.0` and `python-flint==0.9.0`. Dependencies can be installed into an isolated virtual environment; no network is used during replay. A single orientation can be requested by three positional arguments: rear star (1 or 0), rear sign (1 or -1), fifth-clock branch (0 or 1). The run first computes the exact univariate support and then its finite checks; allow several minutes for all orientations. The Lean receipt checks the common-root residue step, not the full nonexistence argument or the exact polynomial computations.
