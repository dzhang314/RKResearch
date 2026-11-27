# First exact closures for seven distinct active stages

At the ten-stage strict SDIRK8 floor over a characteristic-zero field, suppose stage one is the only nonzero quadratic-residual stage, with zero weight. There are seven active physical stages, now at **seven distinct** clocks, and the active cubic defect \(\boldsymbol h=(A-\gamma I)\boldsymbol g\) is nonzero. This note excludes all cases with both literal front stages active and \(k=0\), and all cases with both fronts active, \(k\ne0\), and constant affine multiplier \(Q\) below. It also gives a zero-\(k\) ruling out of a Gauss \(h\)-hole at any active trailing clock, independently of the front weights.

The [six-clock census](../sdirk-eight-silent-one-seven-six-dependent/README.md) is separate and closed. Fewer active literal fronts or nonconstant \(Q\) at nonzero \(k\) are not all excluded here. The unconditional **10–11** interval is unchanged.

## Classification of every active scalar \(h\)-profile

The active vectors \(\boldsymbol h,C\boldsymbol h\) are independent: otherwise nonzero \(h\) would occupy a single active clock, and its zero signed first moment would contradict the nonzero weight there. As in the earlier signed cubic Gram argument, the active pure-four space has dimension at most two, so each of its actual vectors is an affine clock multiple of \(h\). In particular
\[
 L_4(c_i)=Q(c_i)h_i
\]
for a nonzero affine \(Q\) on the active nodes. With their monic nodal polynomial \(D\), let \(R_b,S_b\) interpolate \(D'(c_i)b_i h_i\) and \(D'(c_i)b_i h_i^2\). The five and two paid scalar moments put these in degrees at most one and four. They satisfy \(Q S_b=L_4 R_b\) as polynomials (seven nodes, degree at most five), and \(R_b\ne0\).

* If \(Q\) is constant, \(R_b\) is a nonzero constant by degree, and all \(h_i=L_4(c_i)/Q\ne0\).
* If \(Q\) is linear and coprime to \(L_4\), \(R_b\) is a nonzero multiple of \(Q\). Its root is not an active clock (it would force \(L_4=0\) there). Thus each active \(h\) is the same coprime rational profile, without zeros.
* If \(Q\) shares its root \(r\) with \(L_4\), write \(P=L_4/Q\), a cubic. There must be an active clock \(r\) whose actual \(h_r\ne P(r)\): otherwise all active \(h_i=P(c_i)\), and the paid first moments against the first four scalar powers and the nonsingular cubic Hilbert Gram would force \(P=0\). For \(\nu=\int_0^1P(X)\,dX/P(r)\), the identity that \(P^2-P(r)P\) is \(L_4\) times a degree-two polynomial gives \(\int P^2=P(r)\int P\). Comparing the ordinary integral with the paid first and second defect sums gives, at this one physical exception,
  \[
  b_r h_r=(b_r-\nu)P(r),\qquad b_r h_r^2=(b_r-\nu)P(r)^2.
  \]
  Since \(b_r\ne0,P(r)\ne0,h_r\ne P(r)\), it follows that \(h_r=0\) and \(b_r=\nu\). Thus the shared-root profile has exactly one **Gauss hole**, with its actual Gaussian weight. In this case too, \(R_b\) is a nonzero multiple of \(Q\).

A useful scalar identity for subsequent charts follows without any ordering. Write \(W_F(X)=\int_0^1(F(X)-F(Y))/(X-Y)\,dY\). For the above \(D\),
\[
 L_4W_D-DW_{L_4}=\kappa Q^2
\]
for a nonzero scalar \(\kappa\). Indeed this left side has degree at most two: expand as the integral of the divided difference of \(D\) against \(L_4\) minus that of \(L_4\) against \(D\), use \(\int X^jL_4=0\) through \(j=3\), and use \(\int D=0\) by ordinary degree-seven precision. Its values at the seven nodes are \(L_4(c_i)b_iD'(c_i)=Q(c_i)R_b(c_i)\), so the quadratic identity follows.

## Zero reverse factor, independent of the silent multiplicity

Write \(x=c_{10}=1-\gamma,\ c=c_9=x-\gamma u,\ k=1+2u-u^2,\ N=A-\gamma I,\ M=CA-AC-A^2,\ \boldsymbol w=\boldsymbol b^{\mathsf T}M\). The actual reverse identities of the earlier packets give \(\boldsymbol h^{\mathsf T}B=\alpha\boldsymbol w+\beta\boldsymbol wN\), \(w_{10}=-\gamma^2b_{10}\ne0,\ w_9=-\gamma^2b_9 k\), and \(\boldsymbol w(C-xI)=-k\boldsymbol wN\). At \(k=0\), the reverse row is supported at physical clock \(x\); the two possible silent occupants need not have the same individual defect.

* **Eighth active.** In \((\boldsymbol wN)_8,(\boldsymbol wN)_9\) the only trailing nonzero entry is \(w_{10}\), because \(w_9=0\). The two actual reflected tail taps are \(\gamma u,\gamma(B'-1-m')\), using the normalized reflected third clock \(B'\) and middle tap \(m'\). Therefore \(u h_8=(B'-1-m')h_9\), even if both silent zero stages balance \(x\). Both scalar factors are nonzero in both fixed rear orientations.
* **Eighth silent.** Its actual \(w_8\ne0\) gives
  \(w_8=2\gamma u b_{10}A_{10,8}\).
  Thus \(A_{10,8}\ne0\). The actual eighth coordinate of \(\boldsymbol h^{\mathsf T}B\) is zero, so \(0=\alpha w_8+\beta w_{10}A_{10,8}\) and \(\gamma\beta=2u\alpha\). The actual ninth and terminal entries then give \(h_9=2u^2h_{10}\). This derivation never supposes \(w_8=-w_{10}\) or takes a normalized weight at the silent eighth.

Hence with a Gauss hole no active penultimate or eighth can be that unique zero; and with a silent eighth it cannot be the terminal either. If the terminal is the hole with an active eighth, \(\gamma=1-r\) is Gauss and the two other tail defects use the cubic \(p_0=L_4/(X-r)\). Their required ratio has a unit residual in all four exact reflected gap orientations at the verified split Gauss reduction. Thus the Gauss hole in zero \(k\) cannot be any active tail clock. [Replay](seven_k0_anchors.py).

## Both literal front anchors, zero factor

Normalize clock \(Y=c_i/\gamma\) and \(h\) by \(\gamma^3\). The two literal front \(H_a,H_b\ne0\) at normalized \(A_0,B_0\) determine
\[
 Q(Y)=q_0+q_1Y,\qquad
 Q(A_0)=L_4(\gamma A_0)/H_a,\qquad Q(B_0)=L_4(\gamma B_0)/H_b .
\]
At the active tail clocks use the preceding ratios and \(h=L_4/Q\); no hole occurs there, so the denominators and singleton defects are nonzero. With the known reflected gaps this gives the exact guarded degree-nine polynomial for \(\gamma\). Its gcd with the homogeneous Gauss-common-root polynomial \(\sum_j [X^j]L_4(-\gamma q_0)^j q_1^{4-j}\) is one, including at the midpoint. The constant \(Q\) locus has a degree-four gcd with that diagonal in three literal phases, and is handled separately. [Replay](seven_k0_anchors.py).

For the coprime linear locus normalize the physical denominator as \(X-\xi\). From the paid integrals of \(h\) and \(h^2\), polynomial division of \(L_4/(X-\xi)\) gives both signed sums \(\sum b_i/(c_i-\xi)\) and \(\sum b_i/(c_i-\xi)^2\). For the first, the nonzero remainder \(L_4(\xi)\) isolates the simple fraction after the cubic scalar integral. For the second, the same nonzero remainder squared isolates the double fraction after reducing the cross term with the cubic numerator. Consequently the weighted functional \(\Lambda(f)=\sum b_i f(c_i)/(c_i-\xi)^2\) is exactly known through polynomial degree nine by division with remainder and the ordinary precision-seven integral of the quotient.

For constant \(Q\), the paid \(h^2\) and \(C h^2\) moments mean \(\sum b_iL_4(c_i)^2=\sum b_i c_iL_4(c_i)^2=0\). Together with ordinary degree-seven precision these determine both signed scalar moments of degrees eight and nine. Use them exactly, rather than substituting continuous degree-eight or degree-nine precision.

With active eight, the five known pegs \(a,b,x,c_9,c_8\) leave two ordinary nodes once the known sites are masked out. Either weighted functional yields a signed \(3\times3\) Hankel that must vanish; all checks are units. With silent eight there are four ordinary pegs \(a,b,x,c_9\). The signed \(3\times3\) pivot reconstructs the three missing singleton nodes from six masked moments. Both literal fronts active forces physical four silent by the [literal first-four rank test](../sdirk-eight-silent-one-seven-six-anchored/README.md); physical eight is the other silent zero, so row five is active at one of those three missing roots. The same literal row-five affine elimination in its actual cubic defect as in the anchored chart, now cleared against the actual denominator \(Q\), fails at all three. This elimination does not assign any virtual defect to physical four.

## Both literal fronts active, nonzero factor, constant \(Q\)

The literal anchor equation \(q_1=0\) gives an exact irreducible degree-four diagonal condition in either front phase. All active \(h\)'s are nonzero. In \(\boldsymbol h^{\mathsf T}B=\boldsymbol wP_1(C)\), at most one distinct inactive clock \(z\) can have nonzero aggregate \(w\). There are seven or eight aggregate sites.

If only the seven active sites occur, the six scalar moments make \(D'(c_i)w_i\) constant, as is \(R_b(c_i)=D'(c_i)b_i h_i\). Thus \(P_1\) is constant on the active nodes, hence everywhere; both silent \(w\)'s then vanish individually. In particular eight is active. Its actual penultimate single comparison is \(L_4(c)=kL_4(x)\), giving a guarded cubic gap projection, and the five-peg signed moment gate with the extra degree-eight/nine moments closes the branch.

If there is a separate inactive aggregate at \(z\), it is the root of \(P_1\). The actual active tail comparisons are \((x-z)L_4(c)=k(c-z)L_4(x)\) and, when eight is active, the analogous third ratio. Eliminate \(z\) by cross multiplication. Star gives the polynomial
\[
 (2-u)L_4(c)-uL_4(c_8)+k(2u-2)L_4(x)=0.
\]
Arithmetic gives \(H L_4(c_8)+2T L_4(c)-kT L_4(x)=0\), with the usual cleared \(H,T\). Cancel only the literal forbidden factors (including the zero penultimate gap, zero \(k\), or possible tail collisions). These finite gap quotients and the signed five-peg Hankel exclude active eight. If eight is silent, its own \(w_8\ne0\) forces \(z=c_8=x+\gamma k(u-2)/2\). Substitution into the actual ninth relation gives the guarded quartic gap
\[
 (u-2)L_4(c)-(2u+k(u-2))L_4(x)=0
\]
after discarding the exact forbidden gap factor. The four ordinary pegs reconstruct the three remaining nodes using the same paid scalar moments and literal row-five cut. No equality of the two actual silent defects was assumed. [Replay](constant_q_nonzero.py).

## Verification

Run `python3 check_seven_anchors.py` in its sibling repository proof tree with `sympy==1.14.0` and `python-flint==0.9.0`. It verifies four universal zero-factor terminal-hole phase checks at \((1129,203)\), twelve both-front zero-factor phases and ten constant-\(Q\) nonzero-factor phases at \((1103,161)\). Exact characteristic-zero projections and their guarded components precede every unit test. The [native supporting lemmas](../../lean/RKCert/ReviewedNative/SDIRK8SevenDistinctAnchors.lean) check the Gauss-hole discrepancy and the physical silent-eighth ratio without the sole-balance assumption in Lean/Mathlib 4.36.0. The chart and finite arithmetic are source-level.
