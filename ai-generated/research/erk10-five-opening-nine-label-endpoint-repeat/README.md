# Nine distinct high labels: the repeated endpoint cannot occur anywhere

Keep exactly ten high rows, the
[actual five-opening order-ten budget](../erk10-five-opening-nonsplit-kernel/README.md),
and all nonzero high forward labels. Suppose nine of the
high forward labels are distinct, with the **only duplicate**
being \(1\), one of its copies in the first reverse row.
Then no such continuation exists over **any field with
\(10!\ne0\)**, regardless of the position of the second
endpoint or any individual or grouped score.

The consecutive endpoint block is covered in the
[contiguous proof](../erk10-five-opening-contiguous-endpoint-repeat/README.md),
and the second endpoint immediately after one interior row
is the \(m=9\) case of the
[first separated jump](../erk10-five-opening-first-endpoint-jump/README.md).
We treat every later placement below. This does not cover
other multiplicity patterns, a zero high forward clock,
or a reverse first row outside the endpoint.

## Actual defect ranks and the first two nonzero ordinates

Use the raw weighted actual reverse defects as in the
[first-jump argument](../erk10-five-opening-first-endpoint-jump/README.md).
The grade-two \(\boldsymbol u\) is nonzero at the first
live interior physical row. Its group aggregate cannot
be zero: with only an endpoint pair it would be supported
there with sum zero, but its first endpoint entry is zero
by causality. The nine-site grade-two cofactor space
is an interpolation cofactor times a linear polynomial.
A nonzero aggregate thus has support at least eight
labels. Its first two marks span the full \(D_4\), of
dimension three. A grade-three profile must have an
affine multiplier times \(\boldsymbol u\), since its
mark is still in \(D_4\) and a quadratic multiplier
would give a new cubic direction on this support.

Scale the first interior ordinate to \(1\), as in the
[first-jump proof](../erk10-five-opening-first-endpoint-jump/README.md#leaking-grade-two-a-nonzero-jump-fixes-kappa12),
with horizon \(H\ne0\), and use \(Y\) for the scaled
clock. We are in a chronology with at least two interior
rows before the second endpoint. These first two labels
\(1,b\) are distinct and nonzero because only the endpoint
repeats. The \(1\)-row has \(w_1\ne0\), else it is an early
blind coordinate; \(u_1=-w_1/2\) and \(h_1=0\).
Using the grade basis write
\[
 \boldsymbol h=\kappa(\boldsymbol Y-1)\odot\boldsymbol u,\quad
 \boldsymbol g=P(\boldsymbol Y)\odot\boldsymbol u,\quad
 \boldsymbol k=R(\boldsymbol Y)\odot\boldsymbol u,\quad
 K(\boldsymbol Y\odot\boldsymbol u)=Q(\boldsymbol Y)\odot\boldsymbol u,
\]
where \(P\) is affine and \(Q,R\) are quadratic at most.
The \(b\)-row must have \(u_b\ne0\): otherwise its
\(K\boldsymbol u\) equation kills its only available
nonzero-ordinate tap, and then \(w_b=0\) as well,
an early blind coordinate. On any such early blind
coordinate or endpoint contrast, the actual first two
different forward witnesses persist on later reverse
rows with distinct clocks, just as before.

## A causal two-level identity eliminates a half-strength jump

Suppose \(\kappa=1/2\). Before the second endpoint,
induction as in the nine-label proof gives
\(\boldsymbol w\odot\boldsymbol Y=-2\boldsymbol u\):
the actual \(K(\boldsymbol w\odot\boldsymbol Y)\)
read is simultaneously
\(\boldsymbol w\odot\boldsymbol Y^2/2+\boldsymbol u\)
and \(-2K\boldsymbol u\) on the next row. At every
early nonzero-\(u\) entry before the jump this implies
\[
 P(Y)+2Q(Y)=2Y^2/3 ,
\]
using the scalar primitive of \(\boldsymbol w\odot
\boldsymbol Y^2\). If at least three interior rows
precede the second endpoint, their three distinct
\(u\)-entries are nonzero: at the third, the two defect
reads \(K\boldsymbol u,K(Yu)\) would otherwise kill
both preceding distinct nonzero-\(u\) taps and give
\(w=0\), early blindness. Thus the polynomial equality
is global.

If exactly two interior rows precede the second
endpoint, its \(u\)-jump is nonzero. A zero value would
make both physical endpoint coordinates proportional
on \((w,u)\), hence on the entire observed space,
an early contrast with distinct later forward witnesses.
At that endpoint \(K(\boldsymbol w\odot\boldsymbol
Y^2)=-2K(\boldsymbol Y\odot\boldsymbol u)\) still uses
only the preceding rows satisfying the half relation.
The target clock is zero, so its nonzero jump yields
\(P(0)+2Q(0)=0\).
Combined with the evaluations at the first two labels,
this again proves the same global polynomial equality.

It now survives any nonzero endpoint jump. Define
\(\boldsymbol Z=\boldsymbol w\odot\boldsymbol Y+2\boldsymbol u\)
and \(\boldsymbol V=\boldsymbol Y\odot\boldsymbol Z\).
The actual scalar primitive and marked defect identities
give
\[
 K\boldsymbol V=\boldsymbol w\odot\boldsymbol Y^3/3+
                   (P+2Q)(\boldsymbol Y)\odot\boldsymbol u
                 =(\boldsymbol Y/3)\odot\boldsymbol V .
\]
At both endpoints \(\boldsymbol V=0\) by its leading
factor \(Y\). At all other rows strict causality and
\(Y\ne0\) give \(\boldsymbol V=0\) inductively.
Thus \(Y u=-wY^2/2\) everywhere. Its paid pairing
against \(X\) is the \(\boldsymbol u\)-test \(XY\)
(of degree two, with zero forward constant), which
would then give \(-I(XY^2)/2=-H^2/24\ne0\).
This excludes the half case independently of jump size.

## A similar causal identity eliminates \(\kappa=0\)

If \(\kappa=0\), the actual \(K\boldsymbol u\) at the
second interior row kills its tap onto the first.
Hence \(P(Y)=2Y/3\) from its first two distinct actual
values. Before any second endpoint, induction gives
\(u=-w Y^2/2\): by the old rows and \(K\boldsymbol u=0\)
the current row has \(K(\boldsymbol w\odot\boldsymbol
Y^2)=0\), and its literal \(P(Y)u\) identity yields the
ratio at nonzero \(Y\).
On the first two interior rows \(Q\) vanishes and
\(R(Y)=Y^2/2\), because the second row reads no earlier
nonzero ordinate. If a third interior precedes the
jump, its scalar reads \(K(wY), K(wY^2)\) are both zero
from the same ratios. The two earlier distinct
nonzero-ordinate scores are both nonzero. Thus it taps
neither, and \(Q=0,R(Y)=Y^2/2\) also there. Its
\(u\ne0\) follows from early blindness as above, so
\(R+2Q=Y^2/2\) is a global polynomial identity.

If the jump comes after exactly two interior rows,
its value \(j\) is nonzero by the same endpoint contrast
argument. Its two scalar taps satisfy
\(A+bB=j,\ A+b^2B=0\), since \(K\boldsymbol u=0\)
on the old ratio. Thus \(A+b^3B=-b j\).
The actual second-endpoint cubic and marked read
give \(R(0)=-b,\ Q(0)=b/2\), respectively:
\(K(Yu)=-K(wY^3)/2\) there.
Together with the first two values these again
give the global identity \(R+2Q=Y^2/2\).

Now take \(\boldsymbol Z=\boldsymbol w\odot
\boldsymbol Y^2+2\boldsymbol u\) and
\(\boldsymbol V=\boldsymbol Y\odot\boldsymbol Z\).
The cubic read and the marked defect yield
\[
 K\boldsymbol V=\boldsymbol w\odot\boldsymbol Y^4/4+
                 (R+2Q)(\boldsymbol Y)\odot\boldsymbol u
               =(\boldsymbol Y/4)\odot\boldsymbol V .
\]
Causal induction gives \(\boldsymbol V=0\) exactly as
before, implying \(Yu=-wY^3/2\).
Its \(X\) moment is then \(-I(XY^3)/2=-H^3/40\ne0\),
again contrary to the actual grade-two test.

## All other \(\kappa\) are incompatible with the allowed positions

For \(\kappa\ne0\), the
[one-pair first-three calculation](../erk10-five-opening-nine-label-one-pair/README.md#leaking-grade-two-normalized-first-three-interiors)
can be used as long as the tested interior rows precede
the second endpoint. It does not assume the unique endpoint
once restricted to this prefix: the active donors there
are exactly the first endpoint and preceding distinct
interiors. At least four prior interior labels force
\(\kappa=1/2\) by its exact \(5\times5\) distinct-row
compatibility determinant.

If the jump follows exactly two prior interior labels
\(1,b\), it is nonzero by the early endpoint contrast.
Divide its old \(\boldsymbol u\)-taps by this jump.
The \(K\boldsymbol u\) target is \(-\kappa\), the first
scalar primitive is \(1\), and the second scalar primitive
is \(P(0)\) (all normalized at \(Y=0\)). The actual first
two labels have ratios
\[
 L_1=-2,\qquad L_b=-2[1+2\kappa(b-1)]/b^2,
 \qquad P(Y)=2Y/3+\kappa(4b/3-2)(Y-1).
\]
The three equations on two taps have augmented determinant
\(-4\kappa(b-1)(2\kappa-1)/3\).
Thus compatibility again forces \(\kappa=1/2\).

If the jump follows exactly three distinct interior
labels \(1,b,c\), it too is nonzero by contrast.
The actual first-three ratios and polynomials in the
one-pair calculation apply, with
\(\Delta=3b\kappa-2c\kappa+c\ne0\) from its
third-row scalar equation. The score at the target
\(Y=0\) drops out of every positive primitive.
Of the five equations on the three old defect taps,
use the two marked \(\boldsymbol u\) equations and
the second and third scalar primitive equations.
This four-row augmented determinant is exactly
\[
 -4b^2c\kappa^3(b-1)(b-c)(c-1)(2\kappa-1)/\Delta^2 .
\]
All its factors except \(2\kappa-1\) are guarded, so
\(\kappa=1/2\) is necessary in this last case too.
The causal half obstruction already eliminates it.

All placements of the only repeated endpoint for
nine distinct high labels have now been counted.

## Replay

    python3 -B audit.py
    # From the overlay or repository root:
    sha256sum -c ai-generated/research/erk10-five-opening-nine-label-endpoint-repeat/sources.sha256

The exact replay checks both jump determinants and the two causal
grade transfers. The actual tableau/word and rank arguments
remain mathematical; the earlier endpoint and reduced determinant
gates have separate portable Lean receipts.
