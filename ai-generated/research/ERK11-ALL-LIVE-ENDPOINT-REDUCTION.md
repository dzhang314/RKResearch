# All-early-output-live reduction in the maximal ERK11 endpoint branch

Consider a 17-row strictly explicit order-eleven method, with literal
dense first eleven, rank two on the four positive shifted moments of
the prefix degree-six aliases, and maximal alias dimension four.
In addition assume that the eleven ordinary coefficients \(b_i\)
on that prefix are all nonzero. Below, “grade” is rooted degree
\(|t|-1\), \(E_j\) is the numerical stage span, \(F_j\) is its pure
zero-model subspace, and “tail restriction” means the six physical
coordinates 12–17, not the subspace of vectors supported there.
The post-premise deductions are over a field paying \(11!\).

**New structural results.** All seventeen \(b_i\) must be nonzero.
The full pure ranks are exactly 1,2,3 through grades 2,3,4, with
the grade-three and grade-four spaces identified on the tail by
their exact mixed-product kernels. In the half-clock branch the
quadratic defect has only one clock and one nonzero value across
the entire tableau. This yields a one-clock pure profile at
grades 3–5 and in one case a literal localization of the second
adjoint seed to all quadratic carriers. In the other clock
branch the quadratic defect follows one exact quadratic curve
on every carrier, and the only possible numbers of distinct
carrier clocks are 4,5,10,11. This does not exclude all those
possibilities or all 17-stage methods.

## 1. Precise tail premises used below

Use \(bA=bY\), \(Y=I-\operatorname{diag}(c)\), and the
[actual Jacobi endpoint atom](ERK11-ARBITRARY-PREFIX-JACOBI-GATES.md).
Thus \(e_{17}\in E_6\), row 17 is individually exact through grade
four, and every adjacent edge from 12 onward is live in the
[two-generator tail](ERK11-TWO-GENERATOR-ENDPOINT-TAIL.md).
For a nonzero scaled reflected clock \(y=1-c_{13}\), put
\(Z=Y/y\), \(D=A/y\). The physical \(Z\)-labels on 12–17 are
\[
                     (t,1,1,p,q,0)
\]
with \(t\ne0,1,p\), \(p\ne1\), \(q\ne0\).
If \(p\ne1/2\), also \(q\notin\{t,1,p\}\).
In that normal form \(x_0=u\) starts at row 12,
\(x_1=w\) at 13, and \(x_j=D^{j-1}w\) starts at row \(12+j\)
for \(j=2,\ldots,5\). The grade-six vectors \(u,w\) have
zero at row 17, and \(u_{13}=0\).
The \(b\)-reads on \(x_1,\ldots,x_5\) are
\(1,1,1/2,1/6,1/24\).
Writing \(v=1/t\), the two rows of normalized positive clock
moments on \(w,u\) are
\[
        (1,1,1,1),\qquad(d+v,d+2,d+3,d+4).
\]
The other required clock actions are
\[
\begin{aligned}
 Zu&=t u+e x_2+h x_5,&e&=12(t-1),&
       (d+6)(t-1)&=1,\\
 Zw&=w,\qquad Zx_2=x_2-x_3,\qquad
 Zx_3=p x_3+(2-4p)x_4+4(p-1)x_5,\\
 Zx_4&=q x_4+(1-4q)x_5,& Zx_5&=0.
\end{aligned}
\]
They concern the actual numerical six-slot basis, not an
independent reduced RK tableau. In particular \(x_2\) has
grade seven, \(x_3\) grade eight, and \(x_5\) can be taken
from grade six (because it is a multiple of the Jacobi atom).
Write \(\delta=Ac-c^{\odot2}/2\) for the pure grade-two defect
and \(L=\delta_{12}\).
The two-generator mixed product gate proves
\[
                L(2pq(t+1)-2t(p+q)+t)=0.
\]
For \(p=1/2\), only \(\delta_{13},\delta_{16}\) can be nonzero
on the tail. For \(p\ne1/2\), \(L=0\) means the whole tail
quadratic residual is zero; \(L\ne0\) means \(w\) is a
single physical coordinate at 13, and
\(2t(t-1)\delta_{14}=L\). The arguments below use these
precise premises and independently pay the new products.

## 2. Full output support and literal low pure rank

If \(f\in F_5\), the row \(b\operatorname{diag}(f)\)
annihilates \(E_5\) by the rooted product of cost at most ten.
If the weighted tail restriction of \(f\) is zero, this row
is supported on the first eleven, where \(E_5^{\rm pre}\)
has full numerical image. It is therefore zero coefficientwise.
All first-eleven \(b_i\ne0\), so \(f\) vanishes there.
The full numerical \(E_5\) has dimension eleven and restricts
injectively onto the first eleven in the rank-two branch.
Hence \(f=0\). In particular the weighted tail
restriction is injective on every \(F_j\), \(j\le5\).
This transfer does not assume that early pure vectors have
any special shape.

For \(F_4\), row 17 is zero and the two weighted rows
\(b\operatorname{diag}(u)\), \(b\operatorname{diag}(w)\)
annihilate it by the actual grade-six products.
The two weighting rows are independent on physical
coordinates 12–16: apply them to the positive powers of
\(Z\), whose reads give the two independent mode rows just
listed. Thus the unweighted image of \(F_4\) on the tail
has dimension at most three. Strict forward pure growth
from \(\delta\ne0\) gives \(\dim F_4\ge3\), so it is exactly
the three-dimensional joint kernel. If some \(b_i=0\)
for \(12\le i\le16\), the coordinate line \(K e_i\)
would lie in that kernel. Its pure preimage has weighted tail
zero, contradiction. As \(b_{17}\ne0\), this proves
**every stage has nonzero ordinary weight**.

Also \(\dim F_3=2\) by pure strict growth.
Its unweighted tail image additionally kills
\(b\operatorname{diag}(x_2)\) since \(x_2\) has grade seven.
That row is independent of the preceding two:
on \(Z,Z^2,Z^3\), its moments are \(1/2,1/3,1/4\) by
the paid clock words of length up to four on \(w\).
After subtracting \(d\) times the first mode from the
second and multiplying the third by 12, the columns
are \((1,1,1),(v,2,3),(6,4,3)\), with determinant \(v\ne0\).
Consequently the grade-three tail image is exactly the
two-dimensional kernel of those three weighted rows
and the terminal coordinate. This is stronger than an
inequality on possible defect dimensions.

## 3. Half-clock: one global defect clock and one defect value

Assume \(p=1/2\).
The quadratic defect is nonzero at row 16:
if only row 13 were nonzero, the vanishing paid product
\(b(w\odot\delta)\) would contradict \(b_{13} w_{13}\ne0\);
if both are zero, weighted tail injectivity would give
\(\delta=0\).
When \(q\ne1\), \(w\) is supported on 13,14 only, so
\(\delta_{13}=0\) by this same paid product.
When \(q=1\), both possible defect sites already have
the same clock. If both are nonzero, the two products
\(b(w\odot\delta)=b(w\odot\delta^{\odot2})=0\) force their
values to agree: with \(a=b_{13}w_{13}\ne0\) and
\(s=b_{16}w_{16}\), the equations are
\(a\delta_{13}+s\delta_{16}=a\delta_{13}^2+s\delta_{16}^2=0\).
All of these products cost at most ten.
In all cases the pure masks
\((Z-q)\delta\) and
\(\delta^{\odot2}-\delta_{16}\delta\) vanish on the tail;
they belong to \(F_3,F_4\) and vanish globally by the
transfer in §2. Hence the entire tableau has exactly
one physical clock for all nonzero quadratic defects
and exactly one nonzero defect value. A "carrier"
means a row with \(\delta_i\ne0\), at that clock.

Furthermore \(\delta_{16}\ne0\) forces
\(u_{16}=(x_2)_{16}=0\) from the paid products with
\(\delta\): \(u_{13}=(x_2)_{13}=0\).
Hence \((x_3)_{16}=0\) by its clock identity.
The actual support values \(u_{12},(x_2)_{14},(x_2)_{15}\)
are nonzero (the latter by
\((Z-1)x_2=-x_3\) at 15). At rows 14 and 15 the
ratios \(u_i/(x_2)_i=e/(Z_i-t)\) exist and differ.
For \(f\in F_3\), write
\[
        A_0=b_{12} f_{12},\quad
        B_0=b_{14}(x_2)_{14} f_{14},\quad
        C_0=b_{15}(x_2)_{15} f_{15}.
\]
The two exact kernel rows \(b\operatorname{diag}(x_2)\),
\(b\operatorname{diag}(u)\) give
\[
       B_0+C_0=0,\qquad u_{12}A_0+
                   \frac{e}{1-t}B_0+\frac{e}{p-t}C_0=0.
\]
Thus the three loads are either all zero or all nonzero.
If zero, the remaining \(b(w\odot f)=0\) ensures that
the only nonzero tail data of \(f\) are proportional
to \(\delta\): when 16 is the sole carrier, \(w_{16}=0\)
from the product with \(\delta\), and thus \(f_{13}=0\);
when 13 and 16 are carriers, their \(b_iw_i\) sum
vanishes, so \(f_{13}=f_{16}\).
By tail injectivity of \(F_3\), such \(f\) is proportional
to \(\delta\) everywhere. Therefore every independent
\(f\in F_3\) has nonzero off-carrier values at 12,14,15.

Take \(f=A\delta\), which is independent of \(\delta\):
otherwise, since \(C\delta\) is a scalar multiple of
\(\delta\), its line would be invariant under \(A,C\).
The chronological no-plateau argument, applied to
the quadratic primitive residual on that line, would
force the nonzero clock vector to be pure.
Since \(t,1,p\) are distinct and \(\delta=0\) at 12,14,15,
the exact pure filtration now gives
\[
        F_3=\langle\delta,f\rangle,\qquad
        F_4=\langle\delta,f,Zf\rangle,\qquad
        \langle\delta,f,Zf,Z^2 f\rangle\subset F_5
\]
with the final indicated subspace four-dimensional.

### Sole late carrier at 16: exact localization of the second seed

If \(\delta_{13}=0\) (in particular if \(q\ne1\)),
\(\delta\odot f-f_{16}\delta\) lies in \(F_5\) and
is zero on the tail. Thus \(f\) is constant on all
carriers. Its value at the first carrier is zero
by chronology, so \(f\) vanishes on every carrier.
In particular every carrier has the same clock and
the same grade-four profile. On grade five only
one extra pure direction beyond
\(\delta,f,Zf,Z^2f\) can distinguish them, so there
are at most two carrier rows in the literal prefix
(otherwise two distinct early row differences would
be dependent on the full numerical \(E_5^{\rm pre}\)).
The shift-two and shift-three taps vanish at every
carrier: their product with \(\delta\) kills \(E_5\),
and is supported in the first eleven because these
taps end before 16.

More strongly, let \(h_2=2bD^2-bZ^2\).
It annihilates the full \(E_8\) by the paid clock identities.
The exact normalized half-clock identities imply that
\(E_8^{\rm late}\) contains **all** the physical coordinates
12,13,14,15,17. Here is the literal argument.
Both \(u,x_2,x_3,x_5\) and \(w\) have zero at 16; for
\(w\) this follows from the single-carrier case of
\(b(w\odot\delta)=0\).
The combinations
\(x_2-2x_3+4x_5\) and \(x_3-4x_5\) are actual clock
eigenvectors at 1 and \(1/2\), leading at 14 and 15
respectively. Neither has a later same-clock coordinate
in its support (the possible site 16 was just excluded).
They are multiples of \(e_{14},e_{15}\).
The clock-one vector \(w\), leading at 13, now supplies
\(e_{13}\). Since \(u\) has zero at 16 and lies on the
tail, its projection modulo these and \(e_{17}\) yields
\(e_{12}\). All such vectors lie in the stated grade eight.

It follows that \(h_2\) has late support only at 16,
where its coefficient is \(-b_{16}q^2\).
The row \(b\operatorname{diag}(\delta)\) also annihilates
\(E_8\) by the actual degree-two product and sees only site
16 late. Comparing the two coefficientwise at late rows,
their indicated linear combination is supported on the
first eleven and annihilates \(E_8\), so it is zero.
This proves the exact row identity
\[
        h_2=-\frac{q^2}{\delta_{16}}\, b\operatorname{diag}(\delta),
       \qquad
        2bD^2=b Z^2\operatorname{diag}
                              (1-\delta/\delta_{16}).
\]
Thus in this surviving branch the whole second adjoint seed,
not only its terminal restriction, is clock-local to the
quadratic carriers. It is not by itself an order-preserving
deletion of those stages.

### Two late carriers at 13 and 16: final stage grade-five exact

Here \(q=1\), with both defects equal.
The cancellation \(b_{13}w_{13}+b_{16}w_{16}=0\)
gives \(b_{14}w_{14}=1\), since \(bw=1\) and all
three lie at clock one.
For \(f=A\delta\), its nonzero \(f_{14}\) then forces
\(f_{13}\ne f_{16}\) in the exact read \(b(w\odot f)=0\).
Hence \(\delta,\delta\odot f\) are independent on the
two carrier sites, while \(f,Zf,Z^2f\) are independent
on the three off-carrier sites 12,14,15.
All five are pure of grade at most five, so they
span \(F_5\). They all vanish at row 17.
This upgrades row 17 to **actual point exactness
through grade five**, not merely the original grade four.

## 4. Other clock branch: exact quadratic and remaining carrier counts

Suppose \(p\ne1/2\).
Then \(L\ne0\) under the all-live premise;
otherwise the entire tail defect vanishes.
Consequently \(w\) is supported only at row 13.
The only possible nonzero tail defects now occur
at 12,14,15,16 with four distinct clock labels
\(t,1,p,q\).
In fact all four are nonzero.
The products \(b(u\odot Z^j\delta)=0\), \(j=0,1,2\),
are paid through grade ten.
If one of those four sites had zero weighted charge
\(b_i u_i\delta_i\), three distinct-site scalar moments
would kill all remaining charges (the Vandermonde
determinant is a nonzero clock-difference product).
But the weight, \(u_{12}\), and \(L\) at 12 are live.
Thus all four charges and all four defects are nonzero.
It follows from the exact low pure ranks that
\[
                   F_3=\delta K[Z]_{\le1},\qquad
                   F_4=\delta K[Z]_{\le2}.
\]

A precise quadratic profile on the four carriers follows
by commuting multiplication \(M=\operatorname{diag}(\delta)\)
with \(Z\). Write \(Mu=L u+k_2 x_2+k_3 x_3+k_5 x_5\).
The three paid pure reads give
\(k_2=-6L(4+d-v)\), \(k_3=12L(6+d-2v)\).
As in the two-generator gate, let \(a=\delta_{14}\);
then \(2 t(t-1)a=L\).
From \(e M x_2=(Z-t)Mu\), compare the first three
coefficients \(x_2,x_3,x_4\) of \(Mx_2\):
\[
              a,\quad \frac{-k_2+(p-t)k_3}{e},\quad
                            \frac{(2-4p)k_3}{e}.
\]
Next \(M x_3=-(Z-1)M x_2\), and
\((2-4p)M x_4=(Z-p)M x_3\) since \(M x_5=0\).
The leading coefficients therefore give, at either
\(z=p\) or \(z=q\),
\[
          e(\delta(z)-a)=(z-1)(k_2-(z-t)k_3).
\]
After clearing denominators this reads
\[
         2t(t-1)^2\delta(z)=L\bigl(2(t-2)z^2+3z-t\bigr).
\]
It holds also at \(z=t,1\) by direct substitution.
Denote by \(Q\) the resulting degree-at-most-two
polynomial (divide by \(2t(t-1)^2\)).
The pure vector \(\delta^{\odot2}-Q(Z)\delta\in F_4\)
vanishes on the tail and hence globally.
Every physical carrier therefore has its defect value
exactly \(Q(Z_i)\), including the earlier carriers.
This is an actual curve restriction, not fitted scalar data.

There are at least four distinct noncarrier clocks
in the literal first eleven where \(Q(Z_i)\ne0\):
otherwise choose a nonzero polynomial \(R\) of
degree at most three vanishing at all such clocks.
Then \((Q(Z)-\delta)\odot R(Z)\) is numerically zero
there, but its nonzero model \(Q R\) is of degree at
most five, contradicting prefix separation.
Thus there are at most seven carrier rows in the prefix
and at most eleven distinct carrier clocks in total.

If there are at most nine distinct carrier clocks,
the nine paid tests \(b(Z^j\delta)=0\), \(0\le j\le8\),
force pooled \(b\)-mass zero at each such clock
because its common defect value is nonzero.
Hence each carrier type occurs at least twice,
using all-live support.
For a fixed physical clock and carrier/noncarrier status,
all profiles through grade four agree, and on grade five
row differences within such a type can see only the
single extra pure mode modulo \(\delta K[Z]_{\le3}\).
The monomial-origin representatives and the latter
four pure directions have equal readings in that type.
Thus there can be at most **one** same-type duplicate
across the entire first eleven: two additional duplicate
rows (whether at the same or different types) would
give dependent differences in a numerically full prefix.
The four distinct carrier types in the tail can each
use an earlier copy to cancel pooled mass; every carrier
type absent from that tail instead requires a duplicate
fully within the prefix. There can be at most one of
these additional types. Therefore the total number of
distinct carrier clocks lies in
\[
                             \{4,5,10,11\}.
\]
This leaves both small pooled and large unpooled branches.
It does not assume scalar clock count already equals
effective rooted rank.

## Lean and scope

ERK11LiveTailGate.lean checks the independent third
mixed read, same-value carrier gate, half-clock load
relations, low three-site charge gate and the propagated
quadratic without dividing by any clock node.
The support transfers, chronology and actual rooted
applications are mathematical proofs here, not a new native
order-eleven Lean theorem. The whole branch is still
conditional on maximal aliases and all first-eleven
ordinary weights live. The endpoint Jacobi and exact
two-generator normal forms are prerequisites, and the
ordinary ERK11 interval remains 17–18.
