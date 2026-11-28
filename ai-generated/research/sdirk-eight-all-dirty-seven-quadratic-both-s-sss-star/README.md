# Both singleton endpoints: no actual three-singleton star

Let a strict ten-stage SDIRK tableau over a characteristic-zero field have ordinary order at least eight, all ten literal quadratic defects nonzero, and exactly seven distinct clock labels. Suppose both physical endpoint clocks are singletons. Then neither true orientation can open with an **S,S,S star**, meaning the two actual later rows each use the first stage only. This proof does not exclude an arithmetic S,S,S prefix or other both-singleton shapes.

The [seven-clock decomposition](../sdirk-eight-all-dirty-seven-clock/README.md) has four S and three D clock labels. [Earlier constant and affine exclusions](../sdirk-eight-all-dirty-seven-affine-final/README.md) make the singleton residual graph truly quadratic. All physical weights are nonzero, so the actual opposite prefix is the reflected weighted one. If its other end is singleton and one prefix uses three S, the opposite actual three-row prefix must have shape **S,D,D**: the two prefixes are disjoint rows; all four S are already consumed including the actual terminal singleton. The allowed genuine arithmetic and star maps of this opposite prefix are kept separately below.

## A forced graph and an exact nodal remainder

Normalize the common diagonal to one, and use \(y=x-1\), with ordinary first clock \(0\) and terminal \(H\); the reflected clock is \(y'=H-y\). Write \(w=y-1,\ h=H/2-1,\ m=h+2=1/(2\gamma)\). A true S,S,S star has later \(y\) clocks \(u,2-u\), \(u\ne0,1,2\), and both their true defects equal \((1+2u-u^2)/2\). The first-row defect is \(1/2\). These three distinct paid evaluations force the entire singleton graph
\[
 R(y)=\tfrac12(1+2y-y^2)=\tfrac12(2-w^2).
\]
No fourth read is involved. Write \(p=u-1\); since the two other forward S have nonzero defect, \(p^2\ne2\). The four S labels are then \(w=-1,p,-p,2h+1\). Their nodal quartic is
\[
 N_S(w)=(w^2-p^2)(w+1)(w-2h-1).
\]
With true \(C=A_2+B R\), the scalar \(\mathcal H=L_4-R C\) from the paired-fibre identities is a nonzero multiple of \(N_S\); it has degree four and exactly those roots. Reduce modulo \(W=w^2-2\). The remainder of \(N_S\) is \((2-p^2)(1-2h-2h w)\), so if \(L_4\bmod W=\alpha+\beta w\) then necessarily
\[
 -2h\,\alpha-(1-2h)\beta
    =-\frac{16}{35}h(h^4-2h^3+4h^2+2h-9)=0.
\]
Here \(L_4\) is the centered monic Legendre mode in \(w-h\) on half-width \(m\). This remainder comparison is valid without any split assumption or division by \(\alpha,\beta,h\).

## True rear phases

The actual \(F_*\) is determined uniquely modulo \(W\) by \(F_* L_4=L_3\). Consecutive Legendre coprimality forces \(L_4\) coprime to \(W\) on every candidate (otherwise both consecutive modes would have the same root). Its inverse is also explicitly checked in each exact field. The cubic
\[
 P=(L_3-F_* L_4)/W
\]
has the three D labels as its actual roots. In original \(w\) coordinates the two D readings from the true rear arithmetic phase have map \(T(w)=2w-(2h+1)\); the true rear star has \(T(w)=4h-w\). Both maps send the actual first later D clock to the actual second; in each phase the two actual D labels are distinct. Thus \(P\) and the exact polynomial divided difference \((P(T)-P)/(T-w)\) must share a root. The denominator here is exact polynomial division; no evaluation at a candidate with coincident clocks is involved.

For the irreducible quartic \(h^4-2h^3+4h^2+2h-9\), the replay constructs its abstract rational field, solves the inverse, and verifies unit gcd for **both** rear maps. This covers all embeddings and extensions. For \(h=0\), the exact cubic is \(P=-w(7w^2-36)/26\); arithmetic again has unit gcd. Rear star at \(h=0\) instead uses both endpoints \(w=\pm1\), where both original endpoint defects are \(1/2\). Its actual normalized reverse/original scale is therefore one. At either rear D read its reflected offset is \(1-w\), and its actual star residual is \((1+2(1-w)-(1-w)^2)/2=R(w)\). This contradicts the all-dirty fibre condition that neither physical copy at a D is on the singleton graph. This argument retains both physical star orders.

## Replay and scope

Run `python check_sss_star.py` with SymPy 1.14. The modular polynomial calculation and all fibre gcds are exact characteristic-zero arithmetic. The native Lean companion verifies the doubled quadratic interpolation and reflected residual scalar identities. The rooted-order ingress and the resultant/gcd reasoning are not formalized end to end here. This is a separate both-singleton subchart, and it does not change the 10–11 stage interval.

The publication audit independently replayed the corresponding exact arithmetic; the new Lean companions here are draft scalar lemmas, not claimed kernel-checked in this release.
