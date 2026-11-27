# Exact rational pressure obstruction for one fixed fifteen-stage point-triple chart

This scout targets rational ERK10 in 15 stages, not a new lower bound on arbitrary rational methods. In the specified chart it rules out order ten over \(\mathbb Q\), even after moving four other scalar sites and reoptimizing all high taps and live triple splits. In particular a simple rational precision-nine scalar mesh does **not** complete to order ten by this path.

The scope is six canonical opening rows with an actual clean old point \(r\), literal \(A_r=J_r\Pi\) and \(H_5=X(X-r)\mathcal P_2\), plus nine strict high rows. Only the old origin is scored. The high cross matrix is literally \((EJ-BE)\Pi\). The reverse high chronology is \(1,A_1,A_2,C,A_3,D,E,F,G\), where \(A_1,A_2,A_3\) share forward clock \(A=3/5\), \(C=2/5\), and the remaining four scalar clocks \(D,E,F,G\) are arbitrary distinct rational sites, distinct from \(0,1,A,C,r\). The point \(r\ne0\) is off all six high interiors. All high physical weights and group masses are nonzero, with arbitrary signs. In the actual weighted high transpose \(L\), assume \(L\mathbf1=\mathbf y\) and the weighted grouped vanishing of
\[
 \mathbf U=L\mathbf y-\mathbf y^{\odot2}/2,\quad
 \mathbf G=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\quad
 \mathbf H=L\mathbf U,\qquad y=1-x .
\]
These are explicit shape hypotheses, not claimed universal for width fifteen.

## The remaining rooted pressure budgets

Put \(\mathbf V=\mathbf G/2+\mathbf H,\ \mathbf W=L\mathbf V\), and \(\mathbf K=L\mathbf y^{\odot3}-\mathbf y^{\odot4}/4\), \(\mathbf K_4=L\mathbf y^{\odot4}-\mathbf y^{\odot5}/5\). The [actual anchored contrast](../erk149-two-pair-point-collision/README.md) has fresh scalar drives vanishing at \(0,r\). The target order-ten tests through reverse word length four force \(\mathbf K,\mathbf W\) to kill \(I_5=X(X-r)\mathcal P_3\), and length five forces \(\mathbf K_4,L\mathbf K,L\mathbf W\) to kill \(I_4=X(X-r)\mathcal P_2\). Indeed the direct source spaces are exactly \(I_4\) through size five and \(I_5\) through size six. The shorter words' errors are grouped zero; the first two nonzero \(\mathbf U,\mathbf V\) entries on the triple span the two-dimensional opposed plane. Therefore all length-four errors are combinations of the indicated \(\mathbf K,\mathbf W\) and lower paid rows. To isolate the length-five conditions, first pull \(TY^4\), then \(T^2Y^3\) and \(T^4Y\), where \(T\) denotes the reverse primitive and \(Y\) multiplication by \(y\). Their respective errors are \(\mathbf K_4\), \(\mathbf K_4/4+L\mathbf K\), and \(\mathbf K_4/24+L\mathbf K/6+L\mathbf W\). The exact degree-nine scalar rule pays the comparisons by integration by parts.

Under the stated chronology a complete group with two earlier scalar sites of reverse clocks \(a=1-A=2/5\), \(t=1-C=3/5=3a/2\) has normalized cubic defect
\[
             k(y)=(a+t)y^3/3-at y^2/2-y^4/4 .
\]
This fixes the first three group values at \(A,C,D\). Normalizing the count on actual groups means summing the three physical rows with their weights at \(A\), then dividing by the nonzero group mass. The chronological scalar read at \(C\) uses the first two actual \(A\) rows; here \(L\mathbf U=0\) requires their profiles genuinely distinct.

If \(P_6\) is the monic hull of the six high interiors, a weighted grouped defect annihilates \(I_5\) exactly when its values, after multiplication by \(x_i(x_i-r)P_6'(x_i)\) and group weight, lie on an affine polynomial. Interpolating the fixed \(\mathbf K\) at \(A,C,D\) determines \(r\) by a linear equation when its coefficient is nonzero. The known two first group responses of \(\mathbf W\) at \(A,C\) similarly determine its full required affine direction. No split variable can affect those two responses: on the first two triple rows \(\mathbf V=-a^3/6\). Thus \(\mathbf W\) there is \(-a^3/6\) times the actual total scalar tap at the triple site.

At each of the first four completed groups \(C,A,D,E\), the values of \(\mathbf K_4,L\mathbf K,L\mathbf W\) are now fixed by the scalar geometry, not the remaining internal high taps. For the two transfer columns this follows because on the triple
\[
\begin{aligned}
 \mathbf K&=\bar K_A\mathbf1+a^2\mathbf U+
                  6(\bar K_A-a^4/4)\mathbf V/a^3,\\
 \mathbf W&=\bar W_A\mathbf1-a^2\mathbf U/6+
                  6(\bar W_A+a^4/12)\mathbf V/a^3 .
\end{aligned}
\]
Check the first two physical entries (their differences are \(a^2\) and \(-a^2/6\) times the first \(\mathbf U\) difference), then use the nonzero aggregate weight and zero grouped \(\mathbf U,\mathbf V\) to get the third. The singleton \(D\)'s total taps to \(a,t\) are fixed by the first two scalar moments. The singleton \(E\)'s three scalar tap totals to \(a,t,d=1-D\) are fixed by the exact first two moments and the calibrated third one. Those formulas also fix the first four \(\mathbf K_4\) values by interpolating \(y^4\) on the actual earlier scalar donors.

Testing each top column on \(X(X-r)(X-F)(X-G)\) then uses only those first four group values. These are three necessary scalar pressures, independent of the free tail taps.

## Exact elimination, including singular rational pivots

The scalar rule has eight distinct sites including \(0,1\). Its weights are uniquely interpolatory. Orthogonality of its monic nodal hull against \(1,X\) gives two linear equations for \(F+G,FG\) in terms of \(D,E\). With the nonsingular moment pivot and the nonsingular anchor pivot, the exact three pressure equations reduce to polynomials in \(D,E\) of bidegrees \((5,5),(5,5),(8,11)\), up to nonzero convention factors as computed by the script. The gcd of eliminating \(E\) from the first pressure with each of the other two is, up to scalar,
\[
         (2D-1)^8(102 D^2-102D+11)^8(5271D^2-4864D+193)^3 .
\]
Both quadratics have nonsquare discriminant over \(\mathbb Q\), so a rational solution would have \(D=1/2\). Whenever the scalar moment pivot is nonsingular this gives zero scalar weight at \(E\), contrary to the live-mass premise: its scaled weight numerator is proportional to \((2D-1)(102D^2-102D+11)/(E-1)\).

For the singular scalar moment pivot, compatibility requires the pivot determinant and both sums/products numerators to vanish. Their projected resultant gcd in \(D\) has radicals \(2D-1,\ 102D^2-102D+11\), leaving just \(D=1/2\) rationally. At that value the simultaneous gcd in \(E\) is \(E^2-E+11/102\), with no rational root. For a singular anchor pivot, both its numerator and denominator must vanish. Their projected resultant has the same three radicals as the top pressure gcd, so again the only rational option is \(D=1/2\), which was already excluded. Thus no rational point in the stated fixed-\((A,C)\) architecture survives. The same does not claim closure at other \(a\), at zero shares, or at algebraic singular pivots.

As a separate explicit ingredient, the eight rational scalar sites \(0,1,1/9,8/9,4/13,9/13,2/5,3/5\) support a positive exact degree-nine rule. It is a usable scalar part, not a rooted upper certificate.

## Reproduce

From this directory:

    python3 -B top_scaled.py
    sha256sum -c sources.sha256

This verifies exact polynomial resultants, all rational singular-pivot tests, and quadratic nonsquare discriminants via SymPy; no numeric root threshold and no end-to-end Lean proof is used. The count and rooted reduction are the mathematical arguments above.
