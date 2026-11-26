# Two additional formation consequences

This note is independent of the mixed-word tail proof. Use the setting of the prefix-rank seal 3c699221… and its paid Hilbert pairing.

If \(L\ge d+2\), every clock-local summand of \(E_d\) is actually **pure**, not merely invisible to \(\mathbf b\). The formation obstruction forces its output to be zero. Its exact profile then has zero pairing with all polynomials through degree \(d\), by the same localized identity, and Hilbert separation forces that profile to be zero. Consequently \(V\subseteq F_d\). For \(j\le d\) one also has \(F_d\cap E_j=F_j\): a chosen grade-\(j\) profile of a vector in the intersection has zero moments from its grade-\(d\) pure representative, and the pairing through degree \(j\) determines it. Thus \(\zeta_j\ge j+1\) throughout this early range. Inequality (8) consequently cannot buy an early scalar rent by assuming low-grade localization alone.

At the even midpoint \(p=2d+2\), the monic Gaussian polynomial \(\Pi_{d+1}\) has simple roots in a splitting field over every paid field. Here is an algebraic proof so that the word “cardinal” has its literal meaning. Put \(r\coloneqq d+1\) and
\[
 U\coloneqq (X(1-X)\Pi_r')'+r(r+1)\Pi_r .
\]
Its leading coefficient cancels. For any polynomial \(S\) of degree at most \(r-1\), two formal integrations by parts move the differential term onto \(S\), producing \((X(1-X)S')'\) of degree at most \(r-1\). The endpoints vanish because of the factor \(X(1-X)\); orthogonality and Hilbert separation imply \(U=0\). If an interior algebraic root \(\theta\) had multiplicity \(j\ge2\), the leading term at power \((X-\theta)^{j-2}\) in this identity would be its nonzero initial coefficient times \(\theta(1-\theta)j(j-1)\), while the other terms have higher vanishing order. This is impossible over a paid field. The endpoints were separately excluded by the shifted Hilbert pairing.

Let \(r_{\rm vis}\) be the number of clock labels for which \(\mathbf b\) is nonzero on the actual space \(E_d(\theta)\). The profile map is well-defined at the even midpoint via tests through degree \(d\). For each local summand its image is zero if the summand is invisible; otherwise it is the one-dimensional cardinal line of its Gaussian node. These lines are independent, since each vanishes at every different Gaussian node and not at its own. Therefore
\[
 \dim(V/(V\cap F_d))=r_{\rm vis},\qquad
 \dim(E_d/(F_d+V))=d+1-r_{\rm vis}.
\]
In particular the weighted rank deficit should not be estimated by counting all existing clocks or all localized pure directions. If \(F_d\) itself is clock-invariant, then \(F_d\subseteq V\) and \(\zeta_d=d+1-r_{\rm vis}\) exactly, even without invariance of all \(E_d\). If \(E_d\) is clock-invariant, \(F_d\) automatically is here: the exact moments through degree \(d\) of \(C\mathbf f\in E_d\) remain zero for \(\mathbf f\in F_d\), since the extra clock costs one and \(p=2d+2\), so its profile vanishes.
