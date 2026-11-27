# Exact fourteen-stage order nine with six openings and two reverse pairs

The literal [tableau](positive.json) is an **explicit fourteen-stage Runge–Kutta method of exact order nine** over \(\mathbb Q(\sqrt{15})\), with seven positive contributing scalar clocks and scalar precision nine. It uses a genuinely different cut from the previous [nine-opening seven-site control](../erk14-order9-seven-clock/README.md). It changes no unrestricted stage interval. The tenth tall cleared defect is exactly \(-1221/445\).

Each coefficient in the fixture is \([a,b]\) for \(a+b\sqrt{15}\) with rational coordinates. The replay checks every coefficient in this field, all 486 rooted equations through nine, corresponding scalar quadrature, row sums, pairwise row distinction, and exact next-order failure. No floating-point threshold is used.

    sha256sum -c sources.sha256
    python3 -B splice.py
    python3 -B splice.py --emit /tmp/erk149-two-pair.json
    cmp positive.json /tmp/erk149-two-pair.json

## Cut and genuine free directions

The first six chronological clocks are \(0,e,2p/3,p,q,r\). The last three opening rows are actually pure through derivative size four. Their coefficients are chosen by exact moments through \(X^2\) on the origin, the rough stage at \(2p/3\), and available earlier clean donors, with one free tap \(f\) from the third donor row onto the preceding \(q\) donor. All high rows and outputs see the opening only through the degree-three decoder \(\Pi\) interpolating its literal rows at \(0,p,q,r\). It recovers ideal derivative models at every size up to four. For a tree \(t\), use \(\rho_t=g_t-\Pi\boldsymbol\Phi_t^{\rm old}\), where \(g_t(X)=|t|X^{|t|-1}/t!\).

On the three clean opening donors the pure size-five errors are spanned by
\[
  \mathbf Q=(A\mathbf c^3-\mathbf c^4/4)|_{p,q,r},\qquad
  \mathbf V=(A_{i,\,2p/3})_{i=p,q,r}.
\]
Indeed a non-unary size-five root has only children of size at most three, and any exceptional size-four child profile differs from its ideal polynomial in the two rough supports. The clean donors cannot read the support of the first quadratic error, so its one unary descendant accounts for the second displayed axis. These axes are independent on \(p,q\), with nonzero determinant proportional to \(p q^2(p-q)^2\). Thus, with \(\ell\) their common annihilating row, all \(\rho_5\) lie in
\[
                  H=\ker\bigl(f\mapsto\ell\cdot(f(p),f(q),f(r))\bigr)
                    \subset X\mathcal P_3 .
\]
This is the exact three-dimensional source space: the two pure donor errors give separate cubic interpolation directions and a size-five bush pays a nonzero degree-four direction. Both \(\mathbf Q,\mathbf V\) vary affinely in their **last** coordinate with the genuine tap \(f\).

## Seven clocks, two reverse groups

The contributing clocks are \(0,1,1/3,2/3,1/2,(5-\sqrt{15})/10,(5+\sqrt{15})/10\). The weights are interpolatory \(\int_0^1\ell_i(X)\,dX\). Symmetry gives every odd centered moment. The seven-node hull times \(X-1/2\) has zero integral as well: with centered squared interior radii \(1/9,3/5\), the even condition is \(9(\alpha+\beta)-21\alpha\beta=5\). This supplies precision nine. Each of the masses at \(1/3\) and \(2/3\) is split equally into two nonzero shares, all calibrated values are positive, and only the origin has nonzero opening weight.

Use reverse physical chronology \(1,A,B,A',B',C,D,E\), where \(A=1/3,\ B=2/3,\ C=1/2,\ D=(5-\sqrt{15})/10,\ E=(5+\sqrt{15})/10\); primed stages repeat their named clock but are distinct physical rows. Let \(y=1-x\), \(a=1-A\), \(b=1-B\). The strict reverse matrix \(L\) is constructed with
\[
  L\mathbf1=\mathbf y,\quad
  \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\quad
  \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
  \mathbf h=L\mathbf u .
\]
The first interior row at \(A\) has \(u=-a^2/2\). The \(B\) row reads it with tap \(b(a-b)/a\). At \(A'\), use the two available interior inputs to make the pair-mean \(Ly\) and \(Ly^2\) exact; the stated \(B\) tap is exactly what makes the third grouped read \(\mathbf h\) zero at \(A\). At \(B'\), its three prior interior donors solve those three target actions directly. Their matrix is invertible because the two \(A\) stages have differing \(u\) values at the same clock. Fill each row sum using the first endpoint donor. Consequently \(\mathbf u,\mathbf g,\mathbf h\) are opposed differences on the two pairs, extended by their zero values at the singletons \(C,D,E\).

At \(C,D,E\) solve the three lower moments and \(L\mathbf u=0\), together with the additional response \(L\mathbf v\) for a second opposed pair direction \(\mathbf v\) (here supported on the \(B\) pair). These are five independent donor inputs: \(1,y,y^2\) interpolate the three earlier scalar sites, and the two oppositions separate their individual pair occurrences. At \(D,E\) the already available singleton \(C\) adds an independent \(y^3\) input. Thus their remaining cubic defects \(k_i=(L y^3)_i-y_i^4/4\) can be assigned independently. At \(A,B,C\) the fixed aggregate of this cubic defect is \(w_i G(y_i)\) where
\[
                G(s)=(a+b)s^3/3-ab s^2/2-s^4/4;
\]
all earlier tap clocks there are in \(\{0,a,b\}\) in reverse units.

To make \(\mathbf k\) kill \(EH\), the two freely adjustable final responses pay two scalar conditions. The third condition is precisely its test on the line of \(H\) vanishing at \(D,E\). Pick the monic pressure polynomial
\[
          P(X)=X(X-D)(X-E)(X-\tau).
\]
The fixed part of the \(\mathbf k\) payment on \(P\) is linear in \(\tau\); its unique zero here is \(\tau=7/11\). The single opening tap \(f\) then solves \(\ell(P)=0\), affine in \(f\). For \(p=3/10,\ q=3/4,\ r=4/5,\ e=1/10\), this gives \(f=14432/180225\). Both adjustments are actual scalar equalities, and the remaining two cubic responses and the three \(L\mathbf v\) responses are solved by the literal stage equations. Three independent opening clocks can vary locally with \(f\) repaired; these are not merely reweighting identical rows.

## Proof of exact ordinary order

The forward high block \(B_\mathrm{high}\) is the weighted transpose of \(L\) in reversed order, and the cross lower-left part is \((EJ-B_\mathrm{high}E)\Pi\); the scalar output at 0 uses the old origin directly. There are precisely six opening and eight actual new rows.

For a high primitive, the actual discrepancy is the propagated high derivative error under \(B_\mathrm{high}\) plus \((B_\mathrm{high}E-EJ)\rho_t\). Every first nontrivial source has size at least five; two first errors could only meet at order at least eleven. Thus each error through nine is a sum of single-seed words with at most three exterior clock/primitive letters. Under the weighted transpose, after the first three reverse letters the error from the ideal scalar word lies in the two opposed pair directions, because multiplying by the clock preserves these directions and the two-primitive errors have the displayed names \(\mathbf u,\mathbf g,\mathbf h\). Empty and up-to-two-letter words are paid exactly by their grouped reverses. For length three, only actual size-five sources occur, and the new discrepancy is a linear combination of the already grouped errors, \(\mathbf k\), and the array \(L\) applied to an opposed pair direction. Now \(L\mathbf u=\mathbf h\) is already grouped and \(L\mathbf v\) is paid on \(EH\), while \(\mathbf k\) was paid there by the pressure and the two final corrections. The adjoint scalar comparison is formal integration by parts with total polynomial degree at most eight, paid by the quoted clock rule. Consequently all ordinary rooted conditions through nine follow. The independent exact field replay gives a direct check even without this symbolic reduction.

This packet does not assert a new order-ten construction. The proof of an exact positive control here is redundant with the field arithmetic replay. Standalone Lean field specializations are tracked separately from this packet until independently built.
