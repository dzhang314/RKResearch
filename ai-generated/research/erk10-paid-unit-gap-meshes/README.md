# Pairwise-unit terminal mesh census for two rational ERK10 splices

At the sole paid regular canonical doubled-prefix horizon
\((\theta,v)=(5/2,5/3)\) from the
[opening gate](../erk10-paid-doubled-prefix/README.md), consider two
specific pure-high reverse chronologies. If their endpoint-anchored
scalar mesh is pairwise \(S\)-unit, \(S=\mathbb Z[1/210]\), neither can
pay the terminal size-six tests. This is **not** an obstruction to
arbitrary factorial-localized ERK10: nonunit gaps, different opening
families, other reverse entrances and more correction directions
are not covered.

## Finite scalar mesh space

Normalize final output horizon to one, and stipulate scalar sites \(0,1\)
with all differences of distinct sites \(S\)-units. Every other node is
then one of the 375 complete signed solutions \(u\) to the \(S\)-unit
equation \(u+(1-u)=1\), by the census and primary reference in the opening
packet. The graph on these 375 sites, joined when their difference is a
unit, has 9,900 edges. Every size-\((n-2)\) clique gives exactly one
legal pairwise-unit \(n\)-site mesh after adjoining \(0,1\).

Use the scalar cardinal integral
\(\mu_a=\int_0^1\prod_{x\ne a}(X-x)\,dX\)
and nodal reciprocal \(D_a=(\prod_{x\ne a}(a-x))^{-1}\).
The masses \(W_a=D_a\mu_a\) are forced by Vandermonde and are in \(S\).
A nine-site mesh additionally requires its degree-nine hull to have
zero integral; for ten sites scalar precision nine is automatic.
The replay tests every graph clique and every relevant orientation,
reducing by reflection only when enumerating the initial cliques.

Both charts apply the size-six terminal moment tests on
\[
   \{ f\in X(X-\xi)\mathcal P_3 : \ell(f)=0\},\qquad
   \ell(f)=f(2\xi/3)-(625/648)f(4\xi/5).
\]
Here \(\xi\) is the final raw reverse clock, folded into the physical
opening endpoint. This space is the actual decoder's size-six defect
space for \(v=5/3,\theta=5/2\); the two evaluations are \(v\xi/\theta\)
and \(2\xi/\theta\) from the doubled-prefix cubic primitive, with their
cofactor ratio as in the
[deterministic family](../erk10-sixteen-rational-mirror-family/README.md).

## Repeated raw entrance: nine distinct scalar sites

The raw reverse chronology is \(1,A,B,A,h,l,d,e,\xi\); the origin
has an additional output mass. Require the regular repeated head of
the deterministic family: nonzero \(W_1,W_A,W_B\), split the \(A\)
mass into two nonzero shares, the second reverse-read defect opposite
on these rows and zero off them, and the third read and first defect
response both in the span of this opposite difference and the
cofactor \(V_a=(a-1)D_a\), split in proportion to shares. With
\(p=1-A,q=1-B,y=1-x\), the actual first three reads require
\(\mu_Ap(3q-2p)=\mu_B q^2\). This entrance equation uses aggregate
weights and does not assume \(B=1-A\).

On the first four reverse donors the fused terminal density is
\(r_K R(y)-r_V L(y)\), where
\[
 L(y)=-y^4/4+(p+q)y^3/3-pq y^2/2,\qquad
 R(y)=\alpha y^2/2+\beta y^3/3
\]
and \(\alpha+\beta p=-1/\mu_A,\ \alpha+\beta q=-1/\mu_B\).
The increments in the two terminal reads from a compensated tap into
the first extra donor \(h\) are
\[
 r_K=W_h y_h(y_h-p)(y_h-q),\qquad
 r_V=(h-1)D_h-W_h y_h(\alpha+\beta y_h).
\]
Here \(r_K,r_V\) are not both zero, the regular first-extra-donor
guard in this census. In fact \(L\) is the size-four primitive
difference on the four base donors, and \(R\) is the cofactor
primitive there. A compensated tap into \(h\) changes their response
by \((r_K,r_V)\); fusing kills it. This is the same density
calculation as for the mirror family, retaining both general early
ordinates instead of imposing \(q=2p\).

Use \(F=X(X-\xi)(X-d)(X-e)\) and \(XF\).
They vanish at the last three raw receivers, where the remaining
free taps could enter. They also vanish at the old origin.
Thus on these probes all unresolved taps disappear after fusing.
The remaining tests have fixed values \(q_j=\int_0^1 X^j F(X)
[r_K R(1-X)-r_V L(1-X)]\,dX\), \(j=0,1\).
Necessarily \(q_0\ell(XF)=q_1\ell(F)\). If both \(\ell\) values
vanish, the stronger necessary condition is \(q_0=q_1=0\).

There are 190,620 nine-site cliques, 95,420 reflection representatives,
221 precision-nine representatives, and 222 actual oriented precise
meshes. Across all 250 admissible ordered head/extra-donor choices,
there are exactly six necessary determinant zeros; all six are
blind-both, with nonzero fused load. None pays both terminal tests.

## Distinct raw entrance: ten distinct scalar sites

Here the nine raw nodes after excluding the old origin are all
distinct and have nonzero scalar masses. Use the regular four-read
chart with second reverse-read cofactor defect \(\boldsymbol U\)
supported on the eight nodes other than the reverse origin,
annihilating monomials of degrees 1 through 7, and both the third
read and first defect response in
\(\operatorname{span}(\boldsymbol U,\boldsymbol x\odot\boldsymbol U)\).
The first two actual reverse rows determine the compression, and the
first three reads give the polynomial entrance equation implemented by
`E`. See the
[four-read reverse setup](../erk10-four-read-dense-prefix-obstruction/README.md)
for the actual early row equations. In the present use the terminal
defect space is the smaller doubled-prefix space displayed above,
not the older full four-dimensional space.

The first four donors give an invertible four-read base. Solve every
later row on these donors first (zero other taps), then list the two
terminal responses \(\boldsymbol Q\) of those base rows: cubic primitive
minus its exact target, and \(K(\boldsymbol x\odot\boldsymbol U)\).
For each possible extra donor \(x_4\), the effect of one compensated tap
has two entries \((z_1,z_2)\). The two probes \(F=X(X-\xi)(X-x_6)(X-x_7)\)
and \(XF\) cannot see any adjustable taps except into \(x_4\) at the row
just after it. On these two probes \(z_1 Q_2-z_2 Q_1\) therefore has no
unknown taps. Its two evaluations must obey the same determinant and,
if blind-both, the same pair of separate zero conditions.
The exact replay solves every guarded four-donor system and checks
both requirements. Tail order between \(x_6,x_7\) cannot change the probes.

The 55,935 oriented 10-site meshes give 478 regular exact entrance
triples. The program uses modular entrance screening at 11 and 13
only as an acceleration: all denominators there are units from the
pairwise-unit site assumption, and it rechecks every survivor exactly.
There are 104 blind-both failures and no other determinant-zero
chronologies, so no guarded survivor.

## Replay

From this directory with Python 3 and SymPy:

    python -B mesh_census.py nine
    python -B mesh_census.py ten
    sha256sum -c sha256.txt

Run time depends on Python and the machine. The two scans are independent
and use exact rational arithmetic for every retained test. The domain
of these exclusions is the two stated reverse constructions only.
There is no claim of an end-to-end Lean classification of the meshes.
