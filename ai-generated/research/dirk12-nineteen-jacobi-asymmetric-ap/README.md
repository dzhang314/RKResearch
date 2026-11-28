# Asymmetric rank-three third-copy obstruction on 13-site arithmetic grids

This is a separate extension of the canonical symmetric rank-three
Jacobi obstruction. It releases the symmetry of the three physical
mini ports but restricts the scalar mesh to 13 consecutive sites
\(\{j/m:\ell\le j\le\ell+12\}\) containing 0 and 1, with \(m\)
a positive integer, over \(S=\mathbb Z[1/12!]\). The three literal
merges use \(r,z,u\) as before. It excludes that rank-three
polynomial-injection **construction**, not other meshes, a
different injection, a rank-four bank, or an unrestricted
19-stage DIRK12.

## Actual asymmetric reduction

Retain the old Lagrange table and six old ports (true through size
six), with old indices 8 and 9 pure through size seven before
the final-row correction. After normalizing old index 5 to 1,
take the mini clocks \(1,t,s\) with no relation between \(t,s\).
The penultimate old clock is now \(L=z/c_5\) in this normalization
and its five actual donors are \(0,1,t,s,L\). All old clocks are
distinct. The same two actual size-six dirty profiles and
size-seven scalar deviation give
\(\det[\mathbf M,\mathbf C,\mathbf D]=0\) for rank at most three.
The exact determinant for the free pair has only one live factor,
\[
 -5a^2+2a(t+s)+3a-(t+s).
\]
The other factors \(s^3t^3(2a-1)^4(s-1)^3(s-t)(t-1)^3\)
or denominator zeros are excluded by the distinct old clocks or
the prior donor guards. Thus
\(\sigma=t+s=(5a^2-3a)/(2a-1)\).
The actual pure penultimate scalar size-seven condition means the
degree-five nodal polynomial's integral to \(L\) vanishes:
\[
 2L^3-3(1+\sigma)L^2+5(\sigma+\pi)L-10\pi=0,\qquad \pi=ts.
\]
If \(L=2\), this gives \(\sigma=2\) and
\((a-1)(5a-2)=0\). Both would collide donor clock \(a\) or
\(d=(3-5a)/(5-10a)\) with 1. Otherwise \(\pi\) is determined
rationally by \(a,L\).

As in the symmetric proof, the unique lower correction polynomial is
\(H=X(2X-1)(66X^4-132X^3+84X^2-18X+1)\); the terminal pad and literal
\(z\) merge force \(z=1/2\), so the physical scale is \(1/(2L)\).
The actual injection has \(\eta(x)=H(x)/H(r)\) on every proper
nonterminal physical suffix row. The eleven such sites are
distinct modulo every prime \(p>12\), since each denominator
\(m\le12\) and each nonzero difference of indices has absolute
value at most 12. If \(p\mid H(r)\) in \(S\), all eleven of
those \(H(x)\) would be zero modulo \(p\). This is impossible:
\(H\) has degree six and leading coefficient 132 is nonzero
modulo all such primes. Thus \(H(r)\) must be an \(S\)-unit.
The exact mesh census, with \(m\) even because \(z=1/2\), leaves
only
\[
 r\in\{1/12,1/6,1/4,1/3,2/3,3/4,5/6,11/12\}.
\]
This argument does not assume a nonzero individual weight residue
at any of the sites.

## Elimination and checks

The Jacobi values on the real mini rows must be in the same
two-dimensional projection as the tap columns. A necessary
determinant is \(\det[\mathbf C,\mathbf D,\mathbf H]=0\),
where \(\mathbf H\) evaluates \(H\) at the physical mini clocks.
The coefficient calculation reduces the two known tap functions
and \(H(X/(2L))\) modulo \(X^2-\sigma X+\pi\). Their remainders
have degree at most one. The norm denominators used in the
quadratic algebra are products of the actual values of the
tap denominators at \(t,s\), nonzero by the literal stencil
guards. The determinant at \(1,t,s\) is the remainder-coefficient
determinant multiplied by \(s-t\) and by nonzero scalar tap
normalizations. This gives an exact polynomial numerator \(G(a,L)\)
with no candidate lost to dividing by a zero pivot.

If \(r\) is mini clock 5, \(L=1/(2r)\); the explicit resultants
are unnecessary and the specialized numerator must vanish.
If \(r\) is either mini clock 6 or 7, \(2Lr\) is a root of the
monic quadratic. The cleared quadratic equation and \(G\) must
share a root in \(L\), giving the exact univariate resultant in
\(a\). The script checks their gcd has degree zero before
forming the resultant; no common branch was discarded.
Nonlinear factors of all the resulting polynomials have integer,
degree-preserving finite-field nonroot certificates. Each certificate
also excludes a rational root with denominator divisible by its
prime, by the leading homogeneous congruence. The exact
factorizations are reconstructed by multiplication.

The only rational candidates beyond the immediately forbidden
\(a=0,1/2,1,2/5,3/5\) are these:
- \(r=1/12\) at mini clock 5, \(a=9/5\) or \(6/13\).
  Both yield \(\pi=0\), colliding a mini clock with the origin.
- \(r=1/6\) at mini clock 6 or 7, \(a=1/3\) or \(4/5\).
  Each remaining exact gcd in \(L\) is \(L-1\), colliding the
  penultimate old clock with the first mini clock.

Run the standalone SymPy replay from this directory. Its
44 coefficient nonroot certificates and concise exact transcript
are included. They concern coefficient polynomials, not reduction
of an unknown tableau. This asymmetric extension is an exact
mathematical result with an arithmetic replay, not a full native
Lean proof. The separate symmetric packet has core Lean receipts
for its two modular gates.
