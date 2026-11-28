# High/high disjoint \((1,1)\): the odd quartic pivot cannot vanish

This is a second independent boundary of the [off-diagonal A2/A2 chart](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hh-rankzero/README.md) over arbitrary characteristic-zero fields. In the same seven-clock setting, assume the actual \(R\)-scale line has \(M\ne0\), and the two same-law later singleton offsets \(a,b\) differ. We exclude the vanishing of an additional odd singleton-quartic pivot. The complementary regular nonzero pivot is not asserted empty by this packet.

## Mirror-folded physical graph

Use centered \(x=y-h,\ h=H/2\), and \(m=1+h\). Write \(D_a=D(a/2),N_a=N(a/2)\), \(J_a=(N_a-D_a)/a\), similarly at \(b\), and set
\[
 \begin{split}
 n_a&=(a+b-2H)D_a-HJ_a(H-b),\\
 n_b&=(a+b-2H)D_b-HJ_b(H-a),\\
 U&=n_aD_b,\quad V=n_b D_a,\quad \lambda=U/V.
 \end{split}
\]
The actual \(\widehat R=VR=r_0+r_1x+r_2x^2\) has the polynomial coefficients
\[
 r_2=(J_aD_b+J_bD_a+H J_aJ_b)/2,\quad
 r_1=(J_b(H-a)D_a-J_a(H-b)D_b)/2,\quad
 r_0=(U+V)/4-h^2r_2 .
\]
These satisfy all four actual singleton reads, and \(r_2\ne0\). Under the true mirror \(a\leftrightarrow b\), \(r_0,r_2\) are invariant and \(r_1\) changes sign. Denote \(\delta=a-b\ne0\). Dividing an odd coefficient identity by \(\delta\) is only used on this branch; we make no assertion about equal offsets. For each symmetric row the exact elementary-symmetric change \(s=a+b,z=ab\) is checked by polynomial substitution back.

At the observed doubled centers \(p=(a-H)/2,\ q=(H-b)/2\), put
\[
 L_3=x^3-\ell x,\quad L_4=x^4-\alpha x^2+\beta,\qquad
 (\ell,\alpha,\beta)=(3m^2/5,6m^2/7,3m^4/35).
\]
The affine \(F_*\) is recovered from the actual two ratios \(L_3/L_4\), with \(L_4(p)L_4(q)\ne0\). The replay forms \(x^2-Sx+T=(x-p)(x-q)\), \(S=\delta/2\), and works modulo it. If the remainders of \(L_3,L_4\) are \(c_0+c_1x,d_0+d_1x\), the two-by-two multiplication determinant is
\[
 D_{\rm ax}=d_0(d_0+S d_1)+T d_1^2=L_4(p)L_4(q).
\]
Thus \(D_{\rm ax}F_*\) is the exact affine fit even when none of its individual coefficients is a unit. After exact monic division,
\[
 M_3=\frac{D_{\rm ax}(L_3-F_*L_4)}{(x-p)(x-q)}
        =m_0+m_1x+m_2x^2+m_3x^3 .
\]
The true seven-clock decomposition requires \(\widehat R\mid M_3\). Here \(m_0,m_2\) are odd under the mirror and \(m_1,m_3\) even. The checked folded rows include the two actual polynomial remainder coefficients of \(M_3\) modulo \(\widehat R\), the genuine folded scale determinant, and the sum and the odd divided difference of the two mirror common-\(B\lambda\) equations. No evenness of the tableau or equality of its reflected coefficients is assumed.

## Lost odd rank reduces to one linear equation in \(H\)

Set \(L_0=L_4(h)\), \(C^\#=U(A_2+B R)=c_0'+c_1'x+c_2'x^2\). Its actual endpoint values \(2U L_0,2V L_0\) give \(c_1'=-4L_0r_1\). The quartic
\[
 UV L_4-\widehat R C^\#
 =\Theta(x^2-h^2)(x-a+h)(x-h+b)
\]
has degree four and its four distinct roots are the actual singleton nodes. Equating the cubic coefficient to \(-\delta\) times the leading coefficient gives
\[
 r_1(c_2'-4L_0r_2)=\delta(UV-r_2c_2').
\]
For the pivot \(J=r_1/\delta+r_2\), the case \(J=0\) therefore requires
\[
 W=UV-4L_0r_2^2=0.
\]
Also \(\widehat R(a-h)=\widehat R(h-b)\), since the sum of those two distinct coordinates is \(\delta\). Their paid reads imply \(V\phi=U\psi\), \(\phi=N_a/D_a,\ \psi=N_b/D_b\). The previous [off-diagonal scale guard](../sdirk-eight-all-dirty-seven-quadratic-both-s-both-two-s-disjoint-hh-rankzero/README.md#useful-off-diagonal-scale-guard) proves \(\lambda\ne1\), hence \(\phi\ne\psi\) on this boundary. The exact folded \(J\) is affine in \(H\), and its constant coefficient before nonzero rational clearing is
\[
 J|_{H=0}=(N_aD_b-N_bD_a)/(2\delta)\ne0 .
\]
Therefore its \(H\) coefficient is also nonzero at every candidate on \(J=0\), and \(H\) is uniquely recoverable. No rank-loss root of that implicit linear formula is discarded.

For smaller extra graph rows, on \(J=0\) write \(A=m_2+\delta m_3\) and \(T'=m_1+\delta A\). The quotient by \(r_2(x^2-\delta x+r_0/r_2)\) gives the necessary rows
\[
 m_0m_3-A T'=0,\qquad m_3r_0-T' r_2=0 .
\]
The first is odd and is divided by the nonzero \(\delta\).

## Full univariate elimination in \(s\)

Project \(W\), those graph rows, and the general folded rows along the linear \(J\) in \(H\). True projected guards are obtained by the same nominal linear resultants from each guard times its mirror, and from the leading \(H\) coefficient of \(J\) itself. At the actual recovered \(H\) they are nonzero. Cancel only their factors. Take the recorded pair resultants in \(z\), all in the single remaining coordinate \(s\). The exact degrees are \(592,576,464,448,1024\). Their common irreducible factors have degrees/multiplicities \((3,8),(3,10),(3,24),(6,24),(1,28)\). In each corresponding exact \(s\)-field the joint \(z\)-gcd has degree \(2,2,4,4,4\) respectively and is supported entirely on the already impossible leading-coefficient loss of \(J\). No finite reductions or real sign assumptions enter this classification.

## Replay and scope

Run `SYMPY_GROUND_TYPES=flint python check_odd_rank.py`, with SymPy 1.14 and python-flint 0.8. No cached coefficients or compiled kernel. The [Lean scalar gates](../../lean/RKCert/Research/SDIRKEightDirtySevenBothSingletonBothTwoSDisjointHHOddPivot.lean) certify the cubic coefficient and graph shape identities, not the full order reduction or exact fibre census. This proves that the odd pivot is nonzero in the regular high/high chart; it does not close the regular nonzero-pivot chart or change the stage interval.
