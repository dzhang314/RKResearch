# One exact 29-adic fixed-q ERK10 tableau, hence all powers of 29

The earlier [fixed-\(q\) F29 tableau](../erk10-fifteen-fixedq-f29/README.md)
has an exact compatible lift to \(\mathbb Z_{29}\).
Consequently 15 stages suffice for exact order ten
over every nonzero commutative ring of
characteristic \(29^j\), **for every \(j\ge1\)**.
They also suffice over \(\mathbb Q_{29}\) and
any nonzero \(\mathbb Z_{29}\)-algebra.
No rational tableau or new minimum is claimed.

The full six-variable scalar residual Jacobian
has rank three modulo 29 at the literal F29
point. This is not a full-Jacobian simple lift.
An exact algebraic certificate below accounts
for the remaining three nonlinear equations.
The finite literal checks through \(29^{11}\)
are separate readouts of the construction,
not the reason the lift exists for all powers.

## A simple algebraic root for the origin-cofactor branch

Use reverse ordinate \(y=1-x\), and fix the
rational outer/early tail labels
\[
                         g=6,\qquad R=15,\qquad d=26.
\]
The unknown pair ordinate \(c\) is the unique
29-adic root reducing to \(2\) of the following
primitive degree-ten polynomial:
\[
\begin{split}
P(X)={}&75851682979590000X^{10}-345177595434956400X^9\\
 &+691140376781707950X^8-801391965499578390X^7\\
 &+595327896073372740X^6-295624157281470449X^5\\
 &+99189988063653812X^4-22147907712268517X^3\\
 &+3137934176909504X^2-253467892079060X+8840760201800.
\end{split}
\]
This is the exact nonconstant factor of the
numerator of the origin-root condition
\(\widehat A_0(1)=0\) for these fixed \(g,R\);
no guess from finite lifts is used.
The script verifies its denominator is a
29-unit at \(c=2\), and that \(P\) is
irreducible over \(\mathbb Q\).
We have \(P(2)\equiv0\) and \(P'(2)\equiv16\pmod{29}\),
with unit leading coefficient.
Hensel's lemma therefore supplies \(c\in\mathbb Z_{29}\)
and embeds \(K=\mathbb Q[X]/(P)\) in \(\mathbb Q_{29}\)
using this root.

Reconstruct \(h,f,e\) by the actual rational
late formulae, and \(s_h=a+b,\ p_h=ab\) by the
[exact two-row head solve](../erk10-fifteen-split-fixed-q-spectrum/HEAD-SYMMETRY.md).
All these rational functions have 29-unit
denominators at the chosen residue.
The monic head quadratic
\(Y^2-s_hY+p_h\) has distinct roots \(11,20\)
modulo 29, so take its Hensel root
\(a\equiv11\) and \(b=s_h-a\equiv20\).
This fixes the stage chronology, not just
the unordered scalar rule. The other ordering
is not used.

In particular the normalized old-forward
origin-root condition \(A(0)=0\) (here reverse
\(A(1)=0\)) holds exactly; the weighted-u
cofactor is proportional to \(1/F'(z)\)
at each ordinary singleton. The nonzero common
scale is chosen by the actual first row,
so may be omitted in checking the nonlinear
weighted pairings.

## Exact algebraic check of the nonlinear equations

Let \(D_7\) be the monic polynomial on
\(a,b,d,e,f,g,h\), formed over \(K\) directly
from the two symmetric head coefficients
and the five fixed/lifted tail factors.
The exact scalar cardinal polynomial
\(\widetilde\mu(y)\bmod D_7\) is computed by
divided differences, with no rounded values.
Let \(V_c\) be the actual terminal cubic and
\(C_\nu=(1-R)V_c(R)\).

The weighted dirt polynomial has factor \(y-R\).
After normalizing the nonzero \(u\) cofactor
scale, its remaining affine factor \(q_1\)
is determined from the two literal values at
\(f,g\):
\[
                    q_1(z)=-\frac{\widetilde\mu(z)V_c(z)}
                                      {zC_\nu}.
\]
The algebraic replay checks the same
equality at \(h\), exactly in \(K\).

For the other actual nonlinear pairings,
define the polynomial
\[
 U_0=(y-1)V_c/C_\nu,\quad T_4=(y-R)(y-f)(y-g)(y-h).
\]
The remainders of
\(\widetilde\mu U_0-y(1-y)q_1\) and
\(\widetilde\mu T_4\) modulo \(D_7\)
are proportional over \(K\), the latter nonzero.
This exact proportionality is checked
coefficientwise in the degree-ten field.
Therefore some \(\sigma\in K\) gives a
quartic \(U=U_0+\sigma T_4\) with
\[
       U\widetilde\mu\equiv y(1-y)q_1\bmod D_7,
                 \qquad U(R)=-1 .
\]
At each actual scored singleton \(z\), this
quartic equals \(-\eta_z\) because the literal
cardinal is nonzero.
The degree bound proves the two
\(\boldsymbol\eta\)-pairings with
\((y-c)(y-R)\boldsymbol u\) and its mark.
The value at \(R\) proves the remaining host
pairing by the exact cardinal partial fraction,
and then the physical \(c\)-pair is set by the
earlier Möbius equation. Thus all true nonlinear
coefficient constraints are established in
characteristic zero, not merely for every
modulus tested so far.

## Literal tableau and exactness over rings

Apply the
[fixed-q scalar-to-literal construction](../erk10-fifteen-split-fixed-q-spectrum/README.md).
All structural guards are 29-units at the
known seed: the ten distinct raw labels and the external origin are pairwise distinct,
the early and all seven scored singleton weights
are units, both \(c\) weights are \(5,13\),
the pair ratio is \(8\), and the old recovered
ratio parameters are \(t_0,s,p=(16,24,8)\)
modulo 29. The actual matrix pivots are chosen
among the unit pivots from this seed.
They stay units with the selected Hensel roots.
Thus the literal construction takes place in
\(\mathbb Z_{29}\) (not only its fraction field).
The number-field identities establish the
true hypotheses of that construction, and
its full rooted-order argument gives actual
order through ten. The next-tree defect
reduces to \(10\pmod{29}\), hence is a unit
in \(\mathbb Z_{29}\).

Reduce this one tableau modulo \(29^j\), then
map \(\mathbb Z/(29^j)\) into any nonzero
commutative ring of that characteristic.
Equivalently one can map the tableau directly
into any nonzero \(\mathbb Z_{29}\)-algebra.
The named rooted conditions are polynomial,
so are preserved; the next-tree unit stays
nonzero. This proves exactness as asserted.
The needed rational denominators through
order eleven are units already in
\(\mathbb Z_{29}\).

## Replays and formal scope

From this directory (with the scalar-spectrum
packet beside it), run:

    python3 -B origin_polynomial.py
    python3 -B algebraic_lift.py | diff -u algebraic-lift-audit.txt -
    python3 -B lift.py ../erk10-fifteen-split-fixed-q-spectrum --power 11 | diff -u lift-audit.txt -

The last command independently checks all 1,205
rooted equations on the actual literal output at
every \(29^j\) through \(j=11\), and prints the
unit bush defect. The stored
[literal modulo \(29^{11}\)](lift29p11.json)
is a deterministic finite representative.
The unbounded proof uses the exact algebraic
certificate and the ordinary Hensel lemma;
it is not yet an end-to-end Lean order theorem.
