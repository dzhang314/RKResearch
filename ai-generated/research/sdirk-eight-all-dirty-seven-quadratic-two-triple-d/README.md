# Quadratic seven-clock data cannot put all six doubled rows in the two opening triples

Assume a strict ten-stage SDIRK tableau of ordinary order at least eight over a characteristic-zero field, with every physical quadratic residual nonzero, exactly seven distinct clocks, and a genuinely quadratic graph of singleton residuals \(R\). Use D for a doubled clock label. This packet excludes **D,D,D in both genuine orientations**, so in particular the six doubled physical rows cannot be exactly the first three and the last three. This is a chronology restriction, not a full quadratic-graph or ten-stage exclusion. No sign conditions on weights are used. It is separate from the [two singleton-pair prefix exclusions](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md).

## Literal phase census and small scalar contradictions

Scale to common diagonal one and use dimensionless centered clock \(v=(2x-\ell)/\ell\), with interval length \(\ell=1/\gamma\). Both endpoint labels are D at \(\pm e\), \(e=(\ell-2)/\ell\). The [odd projection](../sdirk-eight-all-dirty-seven-quadratic-end-stars/README.md) applies also when the endpoints share their label \(e=0\). In particular if \(a,b\) are different squared-root labels of the nonconstant bracket of \(Q(v)\), then \(35ab-21(a+b)+15=0\).

For \(e\ne0\), the three D labels are \(\{-e,e,d\}\). A forward arithmetic opener with later D clocks in either order gives \(d=0\) (midpoint first) or \(d=3e\) (other endpoint first). Forward star gives \(d=2-5e\) from the sum of the two later clocks. The reverse possibilities in original coordinates are \(d=0\) or \(d=-3e\) for arithmetic and \(d=5e-2\) for star. Thus:
- Forward arithmetic and reverse star require either \(d=0,e=2/5\) or \(e=1\). The latter is not an interval coordinate; the former gives actual forward arithmetic gap \(u=e/(1-e)=2/3\), forbidden by nonzero third tap. The opposite mixed orientation is its mirror.
- Two stars force \(d=0,e=2/5\). In centered unnormalized \(t=x-\ell/2\), \(m=\ell/2=5/3\), \(h=m-1=2/3\), the D labels are \(0,\pm h\). The known later residuals at each end equal \(\kappa/2\), \(\kappa=17/9\), independently of which later clock was second. Their conversion is \(\lambda\ne0\) from reverse to original. Products of the two D residuals are \(\lambda\kappa/4\) at either endpoint and \(\lambda\kappa^2/4\) at zero. The common quartic coefficient \(B\) and Vieta give \(L_4(0)=\kappa L_4(h)\), with actual discrepancy \(5296/5103\ne0\).
- Two arithmetic phases force both midpoint first, \(d=0\); the other combinations would force \(e=0\). This is the sole distinct-endpoint case remaining for the next section.

For \(e=0\) the two endpoint rows share the label \(v=0\), but are distinct physical pairs. Two stars force the sum of the other D labels to be both \(2\) and \(-2\). In the mixed phase, orient arithmetic forward. The other D labels are \(u,2u\), with their sum \(-2\) from reverse star, hence \(u=-2/3\). The squared-root relation at \(4/9,16/9\) gives the nonzero value \(-325/81\). Two arithmetic phases require the same original ordering of those later labels; swapping would force \(u=0\). Then the two noncentral D squared labels \(u^2,4u^2\) give \(28u^4-21u^2+3=0\). Here \(v=t=x-1\), and the exact second-row forward and reverse residuals at the same clock are \(\kappa(u)/2,\lambda\kappa(-u)/2\). Products at zero and \(u\) give \(L_4(u)=L_4(0)\kappa(u)\kappa(-u)\). The difference reduces modulo the squared-root quartic to \(12u^2/35-24/245\), whose gcd with it is one. This does not presume the graph is even at a shared endpoint.

## Both distinct midpoint arithmetic triples

Put \(m=\ell/2,h=m-1\), and use \(t=x-m\). The two actual forward and reverse first-three clocks are \(1,m,2m-1\) in their respective normalized coordinates. The normalized forward residuals are \((1,\kappa,q)/2\) where \(u=h\),
\[
 \kappa=1+2h-h^2,\quad D=-2+h+4h^2-h^3,\quad
 q=(1+4h-4h^2)+4h^2(3h-2)/D .
\]
The two residual-product equations at \(0,h\) require \(qL_4(0)=\kappa^2 L_4(h)\). Its exact numerator factors as
\[
 \frac4{35}h^2(h^2-2h-1)
       (2h^7-24h^6+84h^5-32h^4-153h^3-10h^2+48h+12).
\]
The first two factors contradict distinct endpoints and \(\kappa\ne0\). The surviving degree-seven factor is irreducible. The shared coefficient \(B\) is fixed up to \(\lambda\) by \(B\lambda=\beta_0=-4L_4(h)/q\ne0\).

Here \(P\) is proportional to \(t(t^2-h^2)\), so \(R=r W\) for \(W=t^2-S\) even, with nonzero scale \(r\). Let
\[
 Q_0:=Q/B=L_3(t)-\mu\,t L_4(t),\qquad
 \mu=L_3(h)/(hL_4(h)).
\]
Dividing \(Q_0\) by \(-\mu\,t(t^2-h^2)\) gives exactly \(W\). The replay checks \(S\ne0,h^2\) and \(L_4(\sqrt S)\ne0\) in the forced degree-seven field. Thus there is no hidden repeated graph root in **this** subcase. Let \(T(t)\) be the quadratic interpolating the genuine first-three residuals at \(-h,0,h\). Denote its even/odd parts by \(T_e,T_o\). The sums of the two literal residuals on each double fix the entire quadratic
\[
 A_2(t)=-B[T(t)+\lambda T(-t)]
       =-\beta_0\left[\frac{1+\lambda}{\lambda} T_e(t)
                           +\frac{1-\lambda}{\lambda} T_o(t)\right].
\]

## Normalized quadratic trace and literal fourth reads

Use the [normalized nilpotent trace](../sdirk-eight-all-dirty-seven-constant/README.md#the-trace-gate-and-its-normalization),
\(
 2\sum_i1/g_i=\ell\sum_i b_i/g_i
\).
The factor \(\ell\) is necessary for the integral of the normalized primitive with weight sum one.

For the singleton sum, the logarithmic derivative of \(H=L_4-R(A_2+B R)\) gives, over the splitting field of \(W\),
\[
 \sum_{\text{singleton } i}\frac1{g_i}
   =-\frac1r\sum_{W(\epsilon)=0}
                 \frac{L_4'(\epsilon)}{W'(\epsilon)L_4(\epsilon)}
     +\sum_{W(\epsilon)=0}\frac{A_2(\epsilon)}{L_4(\epsilon)} .
\]
This follows from partial fractions of \(1/W\), \(H(\epsilon)=L_4(\epsilon)\), and \(H'(\epsilon)=L_4'(\epsilon)-rW'(\epsilon)A_2(\epsilon)\). Add \(\sum_{d=0,\pm h}A_2(d)/L_4(d)\) for the three paired contributions to \(\sum1/g_i\).

For \(\sum b_i/g_i\), the [signed Cauchy/residue computation](../sdirk-eight-all-dirty-seven-affine-two-singletons/AFFINE-TRACE.md) applies with the same derivation for this \(R\): the rational function
\[
 \frac{B H_3[A_2(A_2+B R)+B L_4]}{P H L_4^2}
 =\frac{BH_3}{P H R^2}
      -\frac{H_3(L_4/R+A_2)}{Q_0L_4^2}
\]
has the grouped physical residues plus the extraneous residues from the second term at roots of \(L_4\). At any common \(H,L_4\) root the first term still contributes the correct physical singleton residue. The first expression has no residue at infinity. Thus \(\sum b_i/g_i\) is exactly the coefficient of \(t^7\) in the degree-less-than-eight remainder of \(H_3(L_4/R+A_2)/Q_0\) modulo \(L_4^2\), where \(H_3=4m^6/175\). The inverses of \(W,Q_0\) in this quotient are legitimate because \(Q_0L_4\) have no common root and \(W\) divides \(Q_0\). This is a computation in the exact field, not a numerical quadrature.

Consequently the normalized trace is \(c/r+\mathcal T(A_2)=0\), for a field scalar \(c\) and a linear functional \(\mathcal T\) computed as above. By parity \(\mathcal T(T_o)=0\): the unweighted sums cancel at opposite labels, and \(T_o/Q_0\) is even so its remainder has no odd \(t^7\) coefficient. The replay checks \(c,\mathcal T(T_e)\ne0\), hence \(\lambda\ne-1\) and
\[
 r=\rho\frac{\lambda}{1+\lambda},\qquad
 \rho=\frac{c}{\beta_0\mathcal T(T_e)}.
\]
Put \(\theta=(1-\lambda)/(1+\lambda)\). The complete singleton quartic in original coordinates now is
\[
 H(t,\theta)
   =L_4+\beta_0\rho W(T_e+\theta T_o)
                      -\frac{\beta_0\rho^2}{4}(1-\theta^2)W^2.
\]
The reversed quartic is \(H(t,-\theta)\) in its own centered coordinate; the original quartic reflection follows from the displayed parity.

Every D row is already consumed in the two disjoint triples, so each literal fourth row in its own orientation must be S. Use the [actual fourth read](../sdirk-eight-all-dirty-clock-census/README.md#3-exact-two-ended-fourth-read-exclusion-on-every-mesh). If \(T_f(x)=T(x-m)=a_0+b_0 x+c_0 x^2\), with \(J\) the zero-based primitive, its equation is
\[
 g_4[1-\Lambda(x_4)+b_0+c_0\Delta(x_4)]
    =T_f(x_4)-JT_f(x_4),\qquad
 \Lambda=1+(x-1)/\kappa,\quad
 \Delta=\tfrac43+\tfrac{2(\kappa+1)(x-1)}{3\kappa}.
\]
For the forward fourth use \(g_4=\rho(1-\theta)W(t_4)/2\) and \(x_4=t_4+m\). Let \(F(t,\theta)\) be the resulting cubic polynomial equation. It is checked without dividing by the affine coefficient of \(g_4\), so possible zero coefficients are retained. For the reverse fourth the genuine normalized opening data \(T_f,\kappa\) are exactly the same, and \(r_{\rm r}=r/\lambda=\rho(1+\theta)/2\), so use \(F(t,-\theta)\). Necessarily the exact resultant \(J(\theta)=\operatorname{Res}_t(H,F)\) vanishes at both \(\theta,-\theta\). It has degree six and its gcd with \(J(-\theta)\) is already one in the degree-seven field. This closes the distinct-midpoint branch without an assumed rank pivot or a finite-field reduction.

## Replay and Lean scope

Run `python check_small_phases.py` and `python check_midpoint_two_ddd.py` with SymPy 1.14 and python-flint 0.8. The [Lean companion](../../lean/RKCert/Research/SDIRKEightDirtySevenQuadraticTwoTripleD.lean) checks two scalar shared-end Vieta reductions on Lean/Mathlib 4.36.0. The full trace and chronological exclusions are audited mathematical arguments with exact scripts, not an end-to-end native theorem. No finite-characteristic assertion is made.
