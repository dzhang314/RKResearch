# Anchored contrast excludes the point collision in the literal two-pair chronology

This supplies the missing point-source branch for the **specific** reverse order \(1,A,B,A',B',C,D,E\) of the [six-opening positive order-nine control](../../upper-bounds/real-algebraic/erk14-order9-six-opening-two-pair/README.md). Here every high individual weight and aggregate is nonzero. The low annihilator \(\ell=E_r\) is evaluation at the third clean donor, and \(r\) equals one high interior. The exact proof does not impose reverse co-order at the collided site. Other point-collided chronologies and zero-share branches are not covered. The unrestricted ERK10 interval remains **14–15**.

More precisely, use characteristic zero and all the fixed-interface assumptions from the [separate generic two-pair result](../erk149-six-opening-two-pair-order10/README.md): the literal strict six-row prefix \(0,e,2p/3,p,q,r\), cubic \(\Pi\) on \(0,p,q,r\), exactly eight strict new rows, the origin as the only scored opening row, two distinct paired sites and three distinct singleton interior sites, one terminal at 1, and high cross block \((EJ-BE)\Pi\). All seven scalar sites are distinct; no positivity of the individual shares is assumed. This proof assumes the literal full \(\mathbf b A=\mathbf b(I-C)\) consequence of actual fourteen-stage order ten from the linked equality ledger.

## Point source, literal boundary, and a different residual

Use the standard cubic interpolation cut \(0,p,q,r\) of the six canonical opening rows and the exact cross matrix \((EJ-BE)\Pi\), as in the positive control. If \(\ell=E_r\), both pure size-five donor defects vanish at \(r\). Its literal physical row is locally pure through size five and reads only \(0,p,q\) (the coefficient on the rough donor is zero). Exactness there on \(1,X,X^2,X^3\) implies **whole-row equality** \(J_r\Pi=A_r^{\rm old}\), including a zero tap to \(r\) itself. Also \(E_r\Pi\) is exactly the old physical evaluation at \(r\) on arbitrary prefix data.

Write
\[
 \rho_t=g_t-\Pi\boldsymbol\Phi_t^{\rm old},\qquad
 \boldsymbol\Delta_t=\boldsymbol\Phi_t^{\rm high}
                        -E\Pi\boldsymbol\Phi_t^{\rm old}.
\]
This actual contrast is different from the high derivative error relative to \(E g_t\). If all root children of \(t\) have size at most four (a direct source), the high derivative is ideal and \(\boldsymbol\Delta_t=E\rho_t\). Both the origin and the old \(r\) have the ideal direct value, so this scalar drive vanishes at those clocks. Nonzero contrasts start at size five.

Otherwise, through size ten there can be only one child \(u\) with size at least five. Let \(G(X)\) be the product of the ideal factors of its smaller siblings. The literal primitive/cross construction gives
\[
 \boldsymbol\Delta_t
   = (EG)\odot B\boldsymbol\Delta_u
           + E\bigl(\rho_t-GJ\rho_u\bigr).
\]
Both \(J_r\Pi=A_r^{\rm old}\) and the fact that those smaller siblings are locally ideal at the old \(r\) imply \(\rho_t(r)=G(r)J_r\rho_u\). Thus **every fresh contrast drive** on this recurrence vanishes at \(0,r\), even when an individual larger \(\rho_t\) does not. Adding one leaf to a root gives the analogous identity \(\boldsymbol\Delta_{t\#\bullet}=C\boldsymbol\Delta_t+E(\rho_{t\#\bullet}-X\rho_t)\), again with a drive vanishing at \(r\). This is the reusable anchored contrast.

The genuine size-five and direct size-six \(\rho\) spans are respectively \(X(X-r)\mathcal P_2\) and together \(X(X-r)\mathcal P_3\). This follows from the point case of the [direct source rank calculation](../erk149-six-opening-two-pair-order10/README.md): the two independent cubic donor directions and the degree-four bush give the first; the added monic degree-five bush gives the latter. Direct sources through seven also span \(X(X-r)\mathcal P_4\). On the four noncollided interiors both enlarged spaces separate the four values. The terminal 1 is treated separately by strictness.

## True reverse words and the projected gates

Suppose actual order ten. The [fourteen-stage equality ledger](../ERK10-FOURTEEN-STAGE-EQUALITY.md) gives literal \(\mathbf b A=\mathbf b(I-C)\). For the weighted high transpose \(L\) this is \(L\mathbf1=y\), \(y=1-x\). Define the actual reverse defects
\[
 \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\quad
 \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
 \mathbf h=L\mathbf u,\quad
 \mathbf k=L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4.
\]
At the empty endpoint row 1 all vanish. The **grouped** statement below is at the other four interior clocks, not at \(r\).

For a contrast drive, move its exterior reverse word through the weighted transpose. Compare the resulting row with the scalar word on \(\mathbf1\) using clock multiplication and \(J^* f(x)=\int_x^1 f\). If the actual error is pooled only at \(r\), it kills that drive. Moreover summing the ideal scalar comparisons telescopes to the ordinary desired output: the one-step model recurrences for \(\rho_t\) and the contrast use the same \(GJ\) and clock operations, and exact scalar degree-nine quadrature gives each required integration by parts. At a direct initial source the first drive is \(E\rho_t\). A prescribed word of length \(\ell\) is realized by attaching \(\ell\) actual unary parents or root leaves, in the appropriate order; all subsequent drives then see strictly shorter exterior words. This argument isolates the input to a desired word without assuming the upper source remains direct.

Lengths 0 and 1 have no error. True length-two words on direct sources through seven force the grouped \(\mathbf u\) row zero off \(r\), since \(L x=J^*X-\mathbf u\). True length-three words then force \(\mathbf g,\mathbf h\) grouped zero off \(r\), for the same direct sources: the two-clock/one-primitive row has error \(\mathbf g-2\mathbf u\), while the three-primitive row has error \(\mathbf g/2+\mathbf h\). All errors of lengths up through three are now pooled only at \(r\), hence annihilate all later fresh drives. Use true length-four words on size-five/direct size-six sources to isolate the following at each noncollided interior:
\[
                     \mathbf k,\qquad L C\mathbf u,\qquad
                     L\mathbf g,\qquad L\mathbf h                 \tag{1}
\]
all have zero aggregate. For clarity, in pullback order take the words CCC T, C T C T, T C T T, T T T T, respectively. The first gives \(\mathbf k\) modulo the lower paid rows. The second subtracts \(LC\mathbf u\) from the degree-three scalar comparison. The third gives \(L(\mathbf u-\mathbf g)\) modulo lower payments. The fourth gives \(\mathbf k/6+L(\mathbf g/2+\mathbf h)\). This uses \(L\mathbf u=\mathbf h\) and the earlier grouped equalities. No uncorrected \(\rho_{[t]}\) contributions are discarded; their anchored contrast drives were killed at shorter lengths.

## Exact contradiction in the stipulated literal chronology

Use reverse \(y\) coordinates \(a=1-A,\ b=1-B\). The high strict order is exactly \(1,A,B,A',B',C,D,E\). Any completed pair group at a noncollided clock has exact pooled \(Ly,Ly^2,Ly^3\) of the appropriate grade. Its earlier scalar donor \(y\)'s for these first two pairs are only \(0,a,b\). Since \(y^3=(a+b)y^2-ab y\) on that set, the normalized cubic defect at \(a\) or \(b\), respectively, is
\[
       G(a)=a^3(a-2b)/12,\qquad G(b)=b^3(b-2a)/12.
\]
If \(r\) is either nonpaired singleton \(C,D,E\), both quantities must vanish by (1), impossible.

If \(r=B\), the noncollided \(A\) pair forces \(a=2b\). The \(A\)-group pooled taps on the first \(A,B\) rows are fixed by its exact \(Ly,Ly^2\) reads. Its normalized tap on the first \(A\) is
\[
                     \frac{a(3b-2a)}{6(b-a)}\ne0 ,
\]
since \(a=2b\). But \(L\mathbf u\) and \(LC\mathbf u\) at \(A\) both have zero aggregate. They separate those two donor values by their distinct scalar clocks, so the first \(A\) pooled tap times \(u(A_1)=-a^2/2\) must be zero, contradiction.

If \(r=A\), the noncollided \(B\) pair forces \(b=2a\). Its two tests \(L\mathbf u,LC\mathbf u\) separate the contribution of the first \(B\) donor from the (possibly two) \(A\) donors. Its exact pooled moments \(Ly,Ly^2\) give a nonzero normalized tap \(\lambda=a/3\) on \(B_1\), and total normalized tap \(\nu_1+\nu_2=4a/3\) on \(A_1,A'\). Thus \(u(B_1)=0\). The actual first \(B\) row, which can read only endpoint 1 and \(A_1\), then has tap \(2a\) on \(A_1\); it follows that \(g(B_1)=-2a^3/3,\ h(B_1)=-a^3\).

Let \(\alpha,\beta\) be the actual \(A'\) row taps on \(A_1,B_1\). In the pooled \(B\) row denote \(X=\nu_2\alpha,\ Y=\nu_2\beta\). Its \(L\mathbf h=0\) requires \(-a^2X/2-a^4/3=0\), so \(X=-2a^2/3\). Its \(L\mathbf u=0\) then gives \(-2a^3/3+aX+2aY=0\), so \(Y=2a^2/3\). The required grouped \(L\mathbf g\) on that same noncollided \(B\) site is consequently
\[
   -(4a/3)a^3/3 + a^2X+(2a)^2Y +(a/3)(-2a^3/3)
                          =4a^4/3\ne0 .
\]
This final contradiction uses no choice of the unavailable grouped conditions at \(A=r\). All cases of the stated point collision within the one literal order have been covered.

The native scalar lemmata verify the two-donor separation, both first-pair cubic formulas, and the last \(4a^4/3\) obstruction over characteristic-zero fields in Lean/Mathlib 4.36.0. The anchor geometry, actual direct-source spans, and rooted contrast lifting are the mathematical proof above.


For the independently reproducible scalar calculations, run the following from ai-generated:

    python3 -B research/erk149-two-pair-point-collision/replay.py
    sha256sum -c research/erk149-two-pair-point-collision/sources.sha256

The Python replay uses SymPy exact rational functions. From ai-generated/lean the corresponding commands are:

    lake build +RKCert.ReviewedNative.ERK149TwoPairAnchored
    lake env lean AuditERK149TwoPairAnchored.lean

The typed transcript identifies all four native statements and their standard axioms.
