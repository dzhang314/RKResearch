# What blocks order ten in the seven-clock, fourteen-stage splice

The [changed-mesh control](../../upper-bounds/real-algebraic/erk14-order9-seven-clock/README.md) remains an exact order-nine witness. This follow-up excludes order ten throughout the stipulated fixed-prefix/cross-feed architecture, not just near its displayed scalar solution. It also measures the three remaining contextual residual generators and identifies the actual moving scalar direction when one relaxes degree-nine quadrature. The unrestricted interval remains **14–15**.

## Exact theorem and scope

Use the scaled nine-row prefix \(A_0\) and decoder \(\Pi_\xi\) of the control, and the same literal deletion of the three virtual high rows \(0,\xi_{\rm old},\xi/2\) into old physical rows \(1,8,9\). The five new physical stages, chronologically, are \(z,w,v,\xi_{\rm donor},1\), with \(\xi_{\rm donor}=\xi_{\rm old}=\xi\) as a clock. The seven scalar sites \(0,1,\xi,\xi/2,v,w,z\) are distinct, with \(\xi\ne0\); they are contributing after grouping. Output is supported on the three earlier designated stages and the five new stages. Individual real weights are arbitrary with either sign; in particular the old \(\xi\) output may vanish. The high strict block \(B\) may vary freely; its cross part is the actual decoder feed \((EJ-BE)\Pi_\xi\). No reverse co-order, compatibility equation, Lobatto nodes, or selected order-nine parameters are imposed.

Suppose true order ten holds. Use the [fourteen-stage equality result](../ERK10-FOURTEEN-STAGE-EQUALITY.md) and its paid lower bound for literal \(\mathbf b A=\mathbf b(I-C)\) on the physical tableau. If the new \(\xi\) stage had zero output weight, this equality in its penultimate column would force its only later edge, into the final stage at 1, to be zero. It could then be deleted, contradicting the fourteen-stage floor. Thus all five new weights are nonzero: the other four are the only contributing rows at their respective clocks.

Read the virtual high labels in reverse chronology \(1,\xi_{\rm donor},v,w,z,\xi/2,\xi_{\rm old},0\). The three old labels never serve as reverse columns. Changing the forward \(B\)-column reading one of these three old labels is an exact gauge: its added row tap on the old coordinate subtracts the same coordinate in the decoder feed, by \(E_{\rm old}\Pi_\xi\) equal to the literal old evaluation. The full incoming row is unchanged after merging. Define the weighted adjoint \(L\) using the five nonzero **new** weights; for an old reverse row \(i\) prescribe \(L_{ij}\) on the new columns using the gauge \(B_{ji}=w_iL_{ij}/w_j\). No old weight is inverted, even if \(w_i=0\). The weighted adjoint identity is then exact on all virtual labels. In a new reverse row the physical equality \(\mathbf b A=\mathbf b(I-C)\) forces \(L\mathbf1=\mathbf y\) with \(y=1-x\), since the corresponding physical column only reads new rows later in forward chronology. In each old reverse row impose that same sum using its gauge, e.g. the first reverse column alone. No other simplifying assumption is needed.

Put
\[
 \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\qquad
 \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad
 \mathbf h=L\mathbf u,\qquad D=X(X-\xi)(X-\xi/2).
\]
The first reverse row has clock 1 and no tap, so \(u(1)=g(1)=h(1)=0\).

## Three exact model directions from actual direct trees

A source is called direct here if all its root children have size at most five. Its actual high derivative is the ideal scalar polynomial: the decoder is paid through size five and each of its child primitives is therefore exact, by rooted induction. This applies to every size-six source and to the specified size-seven trees below. The four rational identities checked in the native Lean module use the normalized unscaled prefix (\(\xi=1\)); scaling gives their stated spans for every nonzero \(\xi\).

The two size-six sources are the size-six bush and the tree with two leaf children and a size-three bush child. Their residual polynomials have combinations with coefficients \((-9,27)\) and \((3,-6)\), giving respectively \(D\) and \(DX(X-\xi)\) after scaling and rescaling by a power of \(\xi\). The three direct size-seven sources are the size-seven bush, the tree with three leaf children and a size-three bush child, and the tree with two leaf children and a size-four bush child. Their residuals combine as \((-9,27/2,18)\) and \((9/2,27/4,-27)\), giving \(D\) and \(DX\) at scale 1, with the analogous scaled spans. The union of the direct sources therefore contains the three-dimensional model \(D\mathcal P_2\).

For any such direct \(t\), the [exact primitive identity](../../upper-bounds/real-algebraic/erk14-order9-seven-clock/EXACT-PROOF.md) gives the first error \((BE-EJ)\rho_t\). A true outer primitive with one leaf mark on \(t\) gives precisely \(-\langle\mathbf u,E\rho_t\rangle_{\mathbf w}=0\); after moving the clock, \(L E X-EJ^*X=-\mathbf u\). Scalar integrations here follow from true degree-nine bush moments. Every direction of \(D\mathcal P_2\) is therefore killed by \(\mathbf u\). Each such source polynomial vanishes at the three old clocks \(0,\xi,\xi/2\), and \(u(1)=0\) from chronology. The remaining three coefficients are distinguished by the Vandermonde on \(v,w,z\) with nonzero factors \(D(v),D(w),D(z)\), so \(u(v)=u(w)=u(z)=0\). This is a **true rooted consequence**, not an imposed second reverse condition.

## The final primitive obstruction

The actual outer parent of a direct \(t\) with two leaf marks pays \(\langle\mathbf g-2\mathbf u,E\rho_t\rangle_{\mathbf w}=0\), so \(\mathbf g\) also kills the same direct sources. Now take the literal three-unary extension \([[[t]]]\) of a direct size-six or size-seven source. Its propagated first error consists of the two-letter term on \(\rho_t\), the one-letter term on \(\rho_{[t]}\), and the empty term on \(\rho_{[[t]]}\). The empty term vanishes because \(L\mathbf1=\mathbf y\). The other two sum to
\[
 \left\langle \frac{\mathbf g}{2}+\mathbf h,E\rho_t\right\rangle_{\mathbf w}
 +\left\langle\mathbf u,E(\rho_{[t]}-J\rho_t)\right\rangle_{\mathbf w}=0 .
\]
The last term is exactly zero. The actual support of \(\mathbf u\) is now only at old clocks \(0,\xi,\xi/2\), including the new copy at \(\xi\). At any of these clocks, the identity \(J_x\Pi_\xi=A_{\rm old,x}\) of whole incoming rows says \(\rho_{[t]}(x)=J_x\rho_t\). Thus the old-output cancellation does not require both \(\xi\) weights to be nonzero, or their \(\mathbf u\) contributions to oppose. We conclude \(\mathbf h\) annihilates all of \(D\mathcal P_2\).

On the other hand, the second reverse row at \(\xi\) sees only 1. Its row sum is \(r=1-\xi\), so \(u(\xi_{\rm donor})=-r^2/2\). Since \(u(v)=0\) and the earlier donor clocks are \(1,\xi\), the tap at \(v\) on \(\xi_{\rm donor}\) must be \((1-v)^2/(2r)\). Hence
\[
                h(v)=-(1-\xi)(1-v)^2/4\ne0 .
\]
But the same three-node \(D\mathcal P_2\) Vandermonde forces \(h(v)=0\) (all other possible contributions are at roots of \(D\) or at the first reverse row 1). This is the contradiction. It uses no particular root of the scalar compatibility equation, no assumed reverse co-order, and no sign on weights inside the chart.

With all five new weights nonzero, the same obstruction allows **any** ordering of the four interior new stages. The first reverse row is still the final stage at 1. The one-mark argument uses no other chronology and first proves that each distinct new clock \(v,w,z\) has \(u=0\). If the next reverse row were one of those clocks, it would have only the zero-\(y\) endpoint donor and hence \(u=-y^2/2\ne0\). The second reverse row is therefore forced to be the live copy at \(\xi\), after which the first remaining new interior plays the same role as \(v\) above. A zero-weight new copy of \(\xi\) at an earlier forward slot (not penultimate) is outside this proof.

## Residual rank and truly moving parameters at the positive control

In the displayed degree-nine scalar instance the opposed \(\mathbf u\) pays all length-zero and length-one sources to order ten. At size seven the four length-two reverse tests are multiples of one functional, since \(\mathbf g=\gamma\mathbf h\) at \(v,w,z\) and the size-seven discrepancy vanishes at \(\xi\). This is nonzero even on a direct size-seven bush. Its actual two-leaf marked parent has size ten and factorial 70, with raw residual in a strict interval around \(-2.15244\times10^{-6}\); it cannot be explained by a lower source inside the bush. At size six the eight length-three words restrict to a two-dimensional source space. The two exterior words CCC and CCT (C is a clock, T is the transpose transport) have a nonzero determinant approximately \(-1.7866\times10^{-11}\) on the two exact basis polynomials. Thus the contextual functionals, as rows on the direct sum of their two source grades, span dimension three. This is not a claim that the unrestricted tableau Jacobian has rank three.

For the fixed degree-nine quadrature shape the scalar compatibility root is simple and isolated, and the active reverse taps of the positive construction are uniquely calibrated at each such mesh. The movable split \(s\) at \(\xi_{\rm donor}\) is a true tableau change but a gauge on all rooted outputs through size twelve: the new \(\xi\) primitive differs from the old one by \(R_t/s\), with \(R_t=0\) through source size five. Up to size twelve no root can have two children with such a defect. Multiplying the one possible difference by the new weight \(s\) cancels it; the final stage's tap to this coordinate is itself proportional to \(s\), and all its lower inputs therefore have the same cancellation. Changing a tap in a fully merged column cancels **identically in the matrix**, not only in the weighted equations.

There is one genuine shape direction if one drops only the degree-nine scalar moment while preserving exact ordinary order nine. Perturb the monic cubic \(R_\xi\) by \(\varepsilon H_2\), where \(H_2\) is the monic quadratic orthogonal to the first two anchored moments for the weight \((X-1)D(X)\). A nonzero two-by-two scalar determinant gives \(H_2\). The same reverse compatibility equation still has a simple root \(\xi(\varepsilon)\) near the control, and the entire ordinary order-nine proof needs only precision eight. This is a genuinely moving analytic family, real algebraic for nearby real-algebraic parameter choices. The directed implicit differentiation gives \(d\xi/d\varepsilon\approx0.358175\); the actual factorial-70 raw residual moves at slope about \(-1.58438\times10^{-5}\). But the mandatory raw tenth bush moment is exactly
\[
 -\varepsilon\int_0^1 X^2(X-1)D(X)H_2(X)\,dX .
\]
Its slope near \(+2.96910\times10^{-5}\) is nonzero, since the full three-by-three anchored moment matrix is invertible. Thus the shape direction literally moves the nonlinear defect but loses an independent required clock moment. No nearby member restores order ten.

## Replay and verification scope

    sha256sum -c sources.sha256
    python3 -B continuation.py

The replay uses the neighboring positive witness's exact parameter box. It checks the four rational direct-source linear combinations, the complete contextual rank test, the isolated actual failed tree, and the two genuinely moving literal derivatives. The Lean native module checks the four concrete source identities, first receiver Vandermonde cancellation, and split algebra in Mathlib/Lean 4.36.0. The full rooted exclusion and local implicit continuation above are mathematical, not asserted as one closed native all-tableau theorem.
