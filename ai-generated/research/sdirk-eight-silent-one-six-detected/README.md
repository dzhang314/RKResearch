# Closing the detected six-active branch with one invisible donor

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, consider exactly one physical nonzero quadratic residual, at the individually weight-zero stage one, and six active stages. The [undetected branch](../sdirk-eight-silent-one-six/README.md) was already excluded. This packet excludes the detected branch \(B\boldsymbol h\ne0\) for \(\boldsymbol h=(A-\gamma I)\boldsymbol g\). Thus **six active stages are impossible** in the single-invisible family. Four/five active (undetected) and seven/eight/nine active (detected) are not excluded here. The unrestricted interval remains **10–11**.

## Active cubic Gram and reverse support

The cubic scalar span on the six active coordinates has a nonsingular four-dimensional Hilbert Gram. Its complementary nondegenerate form has dimension two. The nonzero \(\boldsymbol h\) there is isotropic, and every pure degree-four vector lies in its orthogonal complement there by paid pairings of total degree seven. This complement is the line spanned by \(\boldsymbol h\). Consequently \(C\boldsymbol h,L_4(\boldsymbol c)\), and every pure-four read are proportional to active \(\boldsymbol h\). Call \(r\) the single physical clock of all its nonzero entries. Every other active clock is Gauss. If \(r\) is Gauss, all actual active clocks are Gauss. Otherwise at least two active rows at \(r\) are necessary by the paid first moment of \(h\). Three would leave at most four distinct sites including the non-Gauss clock \(r\), which would either violate ordinary rank or the four-site Gauss rule. Thus there are exactly two at \(r\); their \(h\)'s agree and their weights cancel by the paid \(h,h^2\), leaving the four distinct singleton Gaussian sites. This uses signed weights.

Write \(x=c_{10}=1-\gamma\), \(c=c_9\ne x\), \(u=(x-c)/\gamma\ne0\), \(k=1+2u-u^2\), \(N=A-\gamma I\), and \(\boldsymbol w=\boldsymbol b^{\mathsf T}M\). The actual reverse basis \(\boldsymbol w,\boldsymbol wN\) spans \(Z_3\), with \(w_{10}=-\gamma^2b_{10}\ne0\), \(w_9=-\gamma^2b_9k\), and \(\boldsymbol w(C-xI)=-k\boldsymbol wN\). The row \(\boldsymbol h^{\mathsf T}B\) belongs to \(Z_3\). For \(k\ne0\), it is thus \(\boldsymbol wP(C)\) for a nonzero affine \(P\). At \(k=0\), \(\boldsymbol w\) is physically supported at \(x\), and one can use its basis \(\boldsymbol w,\boldsymbol wN\) directly. A silent physical eighth has \(w_8\ne0\) from the two actual weighted strict successor taps, and \(2(c_8-x)=\gamma k(u-2)\).

## Gaussian terminal clocks

First, if \(r\) is Gauss, all active clocks are Gauss. A nonzero eighth weight then contradicts the literal reflected three-clock incidence. For silent eight, \(k=0\) is impossible at a Gauss terminal/penultimate pair. If \(k\ne0\), the two terminal \(w\)'s are nonzero, so one of \(x,c_9\) equals \(r\) and the other is the unique root of \(P\). The silent \(w_8\ne0\) forces its clock to be that root. The two possibilities give \(u=2\) or \(2u+k(u-2)=0\), both impossible for two Gauss terminal clocks.

Next suppose \(r\) is not Gauss and \(x\) is Gauss (hence \(\gamma\) is Gauss). If \(k\ne0\), \(h_{10}=0\) gives the unique root \(P(x)=0\). The penultimate therefore has \(h_9\ne0\) and \(c_9=r\). For \(k=0\) the same conclusion follows: the terminal zero \(h_{10}\) kills the \(\boldsymbol w\) coefficient of \(\boldsymbol h^{\mathsf T}B\) in the \(Z_3\) basis, while \((\boldsymbol wN)_9=w_{10}A_{10,9}\ne0\).

If physical eight is active, its clock is Gauss, distinct from the other two tail clocks. At \(k=0\) neither fixed actual reverse-third clock can be Gauss when \(\gamma\) is Gauss. At \(k\ne0\) the support relation makes \(w_8=0\), so the actual normalized reverse third defect is zero. In star it equals \(k\), impossible. In arithmetic the degree-five cleared expression
\[
 (1+4u-4u^2)(-2+u+4u^2-u^3)+4u^2(3u-2)
\]
must vanish at \(u=(x-c_8)/(2\gamma)\); it never does on the stated ordered Gauss pair. Thus eight is silent, at \(x\) (either from \(k=0\) or from the unique root \(P\)), and the literal gap is \(u=1\pm\sqrt2\) or \(u=2\).

The non-Gauss clock \(r=x-\gamma u\) differs from both literal front clocks \(a,b\) in all those fields, hence both nonzero-\(h\) front stages are silent. Together with physical eight these exhaust the silent quadratic-zero rows. Thus rows four and five are active. If row four is Gauss, it has \(h=0\), no actual strict feed from stage one, and only two available strict clocks \(a,b\). Its three clean scalar moments give the impossible two-clock nodal integral. Otherwise row four is \(r\) (the second physical copy), and row five is Gauss. The latter is clean through degree four and has only strict scalar feeds at \(a,b,r\), which gives the impossible three-clock nodal integral. The [exact split Gauss replay](six_gauss_terminal.py) checks all 192 front, Gauss and gap orientations of these two integrals.

## Non-Gaussian terminal with the canceled repeat

If \(x\) is not Gauss, then \(x=r\), \(c_9\) is Gauss, and a physically active eighth must be Gauss and distinct from \(c_9\). At \(k=0\) the two fixed nonterminal tail clocks cannot both be Gauss. At \(k\ne0\), the penultimate is the unique root of \(P\); an active eighth has \(w_8=0\) and thus reverse third defect zero. Star again fails, and arithmetic gives \(x=2c_9-c_8\), \(\gamma=1-x\), and \(u=(x-c_9)/\gamma\); the cleared degree-five expression is nonzero on every pair of these Gauss clocks.

Thus physical eight is silent. At \(k=0\) it is at \(x\), with \(u=1\pm\sqrt2\). At \(k\ne0\) it is at \(c_9\), and the literal clock equation gives \(2u+k(u-2)=0\). The strict diagonal in both cases is \(\gamma=(1-c_9)/(1+u)\) with \(c_9\) Gauss. In these fixed monic Gauss/gap quotients \(x\) differs from both literal front clocks. Thus again exactly rows \(2,3,8\) are silent quadratic-zero rows, and actual row four or five gives the same clean two- or three-clock scalar obstruction, now with \(r=x\). The [exact quotient replay](six_terminal_defect.py) checks all 128 front/Gauss site choices with both gap polynomials and all their roots.

In either tail case, for strict predecessor set \(S\) and candidate clean current clock \(y\), the tested obstruction is
\[
 I_0^y\!\left(\prod_{s\in S}(X-s)\right)
   -\gamma\prod_{s\in S}(y-s)\ne0.
\]
It uses only the physical predecessor clock set and the equal diagonal, not an extrapolated stage order at silent rows.

## Replay

Run `python3 check_detected.py` with `sympy==1.14.0` and `python-flint==0.9.0` against the earlier sibling chart files. The reduction at \(1129\) splits all four simple Gauss roots and both front orientations; the two exact gap polynomials are kept in fixed monic bases and their scalar divisors checked. The units lift over characteristic zero in these finite bases rather than assuming the proposed tableau itself can be reduced. The [Lean receipt](../../lean/RKCert/ReviewedNative/SDIRK8SilentSixReverseSupport.lean) verifies the guarded affine root support and silent terminal gap identities, compiled on Lean/Mathlib 4.36.0. The physical Gram and finite chart analysis are source-level.

With seven active stages, the [small-multiplicity follow-up](../sdirk-eight-silent-one-seven-small/README.md) excludes up to five distinct active clocks in the same detected branch.
