# The fixed-horizon dirty relay cannot collide with an invisible late clock

Use the [literal nine-stage dirty-sixth relay](../erk10-dirty-sixth-relay/README.md)
at horizon \(\xi=1\) relative to the final unit step, so its ghost
and clean clocks are \(z=1/3,w=2/3\).
Keep the [physical decoder splice](../erk10-dirty-sixth-distinct-tail/README.md)
and append six strict rows, output supported on the origin and high rows.
If exactly one late slot collides with one of \(0,1,w\) and there is
no other late repeat or collision, order ten is impossible over
\(\mathbb Q\). This covers asymmetric and signed rational meshes.
Other horizons are not covered.

## Set-up and actual marked co-order

The size-six ghost has zero output mass by the actual size-six
defect already verified. The remaining possible scalar support has
eight sites containing both 0 and 1, even if their weights vanish.
By the [anchored degree-nine scalar lower bound](../rational-endpoint-moment-nine/README.md),
each of the five visible late sites (those off \(0,1,w\)) has a
nonzero output mass. More than one such collision/repeat would
leave at most seven sites and is impossible. For a visible site
\(u\), put
\(Q(X)=X(X-1)(X-w)\) and \(F(X)\) equal to the hull of the five
visible sites. Its cardinal integral is
\[
       \mu_u=\int_0^1 \frac{Q(X)F(X)}{X-u}\,dX
              = Q(u)F'(u)b_u .
\]

For \(j=0,1,2,3\), let
\[
 r_{j,i}=(\boldsymbol b^\top C^jB)_i
             - b_i(1-c_i^{j+1})/(j+1)
\]
at late physical columns, with \(B\) the actual late-to-late block.
The literal rooted sources from the
[distinct-tail proof](../erk10-dirty-sixth-distinct-tail/README.md)
apply with \(j\) extra leaf children at the new root. They force
\(\boldsymbol r_j\) to annihilate the evaluations of
\(Q\mathcal P_{5-j}\). Their actual rooted budget is \(k+1+j\le10\)
when the source has size \(k\).
On five distinct visible sites, Vandermonde gives
\(r_{0,u}=r_{1,u}=0\) and
\[
 Q(u)F'(u)r_{2,u}=\Lambda,\qquad
 Q(u)F'(u)r_{3,u}=d_0+d_1u
\]
for some scalars. The invisible late column is irrelevant to these
tests since \(Q\) vanishes there. The barycentric forms follow by
the leading-coefficient interpolation identity.

Let \(v\) be the invisible late clock.
At the chronologically last visible slot \(x\) the only possible
later weighted tap is from \(v\); literal \(D(1)\) and \(D(2)\)
at that singleton then require the invisible slot last, with
nonzero weight, and \(v=(1+x)/2\).
For \(v=1\) this is already impossible since \(x\) is visible.
It remains \(v=0,w\), with \(x=2v-1\).

## Exact elimination for both remaining collisions

Write \(y,t\) for the previous two visible slots in reverse order.
At \(x,y,t\) the strictly later donor *sets* are respectively
\(\{v\},\{x,v\},\{y,x,v\}\).
Define \(I_u(f)=\int_u^1 f(X)\,dX\),
\(p_2=(X-x)(X-v)\).
Taking the quadratic donor hull (a double root at \(v\) if needed),
and using already exact degrees zero and one, gives
\[
 \Lambda=-\mu_x I_x((X-v)^2)
         =-\mu_y I_y(p_2).
\]
For the third-moment defect at each of these visible sites, set
\(D(u)=Q(u)F'(u)r_{3,u}\).
The monic third-degree donor test, allowing the dummy repeated
root at \(v\) at \(x\), then gives
\[
\begin{split}
 D(x)&=3v\Lambda,\\
 D(y)&=(x+v)\Lambda-\mu_y I_y(Xp_2),\\
 D(t)&=(y+x+v)\Lambda-\mu_t I_t((X-y)(X-x)(X-v)).
\end{split}
\]
The first line uses that \(v\) is the midpoint of \([x,1]\), so
\(I_x(X(X-v)^2)=v I_x((X-v)^2)\).
These equations work for signed taps or signed clocks.
The fact that \(D\) is affine supplies the single exact pressure
\((y-x)(D(t)-D(x))-(t-x)(D(y)-D(x))=0\).

Now \(F=(X-x)(X-y)V\) for a monic cubic \(V\).
The two scalar nodal constraints
\(\int_0^1 QF=\int_0^1 XQF=0\) and the displayed \(\Lambda\)
equation are three linear equations on its lower coefficients.
For each \(v\), the determinant's only rational zero is \(y=x\),
excluded by distinctness. Thus solve \(V\) exactly.
Use \(\mu_t=\int_0^1 Q(X)(X-x)(X-y)V(X)/(X-t)\,dX\)
with the synthetic quotient (valid because \(V(t)=0\)).
Reduce the final affine pressure modulo \(V(t)\) and eliminate \(t\)
by an exact resultant. The numerator has the linear factor
\(y-x\) and other factors of degrees \(2,5,7\). Every nonlinear
factor has no projective root mod a small prime; the determinant
quadratic also has this property. See the [exact audit](exact-audit.txt).
Thus both resultants have no permissible rational \(y\), including
the singular-pivot cases.

A projectively rootless certificate means both nonzero leading
coefficient mod its prime and no affine residue root. Any rational
root represented by coprime numerator and denominator would give a
projective root, whether or not its denominator is divisible by that
prime. No bound on numerator or denominator height is involved.
The Lean Core receipt checks every modular factor certificate.

## Reproduce

    python -B audit.py /tmp/ERK10DirtySixthInvisibleCollisionMod.lean
    lean /tmp/ERK10DirtySixthInvisibleCollisionMod.lean
    sha256sum -c sha256.txt

The Core receipt was checked on Lean 4.34.1, 4.35.0, 4.36.0, and
4.37.0-rc1, without axioms. The exact arithmetic computes, rather
than assumes, the coefficients received by that local test. The
actual rooted bridge and chronology are mathematical as above.
