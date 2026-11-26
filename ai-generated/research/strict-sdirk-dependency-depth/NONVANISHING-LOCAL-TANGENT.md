# One-extra-stage local evaluation-plus-tangent law and a finite diagonal condition

Mathematical proof, not kernel-checked. In the common-diagonal,
characteristic-zero \(s=p+1\) chart, assume order through \(p\),
the actual physical full-chain product \(L\ne0\), and the
separate paid top \(B_0=\lambda_{p-1}\ne0\).
This note never sets \(L\) equal to an unpaid scalar.
The local arithmetic arguments assume \(\gamma\ne0\).
A joint run is a consecutive nonzero-step arithmetic
clock run with constant normalized one-hole weights at
its strictly interior indices.

**Consequences.** A joint run of length ten is impossible,
as are two disjoint joint runs of lengths at least eight
and six, regardless of whether their steps agree.
For cyclic methods in this chart, \(p\ge17\) therefore
forces the scalar determinant \(\Delta=0\) from the
centered rectangle. By the earlier topology and canceled
chart exclusions, any common-diagonal \(s=p+1\) method
at \(p\ge18\) must have \(\gamma=0\), or a zero of a
specified nonzero degree-\(O(p)\) polynomial \(\det H_3\)
in the common diagonal. This is a finite-diagonal
necessity, not an unconditional \(p+2\) stage floor.

## 1. Actual extra hole gives evaluation plus tangent

Use the physical run-weight model of the companion
rectangle: the actual weight with a given set of holes
divided by \(L\) is the product over contiguous omitted
intervals of their normalized actual weights. For a
specified joint arithmetic run of step \(\alpha\), let
\(f_d\) denote the normalized constant factor of an
internal interval of \(d\) holes; \(f_1\) is given as a
joint-run hypothesis, and higher constants follow from
single-mark calibration below. Write \(\rho_d=\alpha^d f_d\).

For marked occupied gaps with desired counts \(d_i\ge1\)
take \(h=1+\sum_i d_i\) physical holes. The \(d_i\)-degree
mark at that link is
\(\prod_{r=1}^{d_i}(\text{clock difference}-r\alpha_i)\)
for the step of its own run. If the actual hole count is
\(g\), the factor is \(\alpha_i^{d_i}d_i!\binom{g}{d_i}\);
in particular it vanishes unless \(g\ge d_i\).
Thus at most one surplus hole remains, compared to the
desired counts. The word pays
\(1+(s-h-1)+\sum d_i=p\).
The reverse grade is \(\sum(d_i+1)\); it also budgets
the occupied links and is not the tree order.

The actual allocation is the same as in the prior local
Leibniz proof, except that the singleton sum is now \(B_0/L\).
To recall the exact count, let \(k_i\) be the marked
occupied links and \(u_i=k_i+\sum_{\ell<i}d_\ell\)
their primitive donors when the one surplus has not
yet been inserted. If the surplus is in an unmarked gap
\(\ell\), its index is \(\ell+1+\sum_{k_i<\ell}d_i\).
Those positions run through all physical indices except
the disjoint blocks \(\{u_i+1,\ldots,u_i+d_i+1\}\).
Every forbidden block is strictly interior to its run:
the targeted allocation putting the surplus in that
same link has endpoints \(u_i,u_i+d_i+2\) in that run.
An unmarked surplus is a separated singleton, so the
total of its factors is \(B_0/L-\sum_i(d_i+1)f_{1,i}\).
A surplus in marked gap \(i\) instead contributes the
binomial factor \(d_i+1\) and uses \(f_{d_i+1,i}\).
All these replacements retain the actual \(L\) as
normalization; no independent skip is divided by.

The formal model is \(T=J-\gamma I,X\), with \(J\)
integration from zero and \(X\) multiplication by the
variable. Inserting the \(d\)-degree gap mark replaces
its one \(T\) by a polynomial \(d!T^{d+1}F_d(\gamma/T)\).
This comes from \(d\)-fold gap commutators of \(B,C\)
mapping to \(\mathrm{ad}_X^d(T)=d!J^{d+1}\) for \(d\ge1\).
For a run with \(t=\alpha/\gamma,\ w=1+y\):
\[
 F_1=w^2-ty,\qquad
 F_2=w^3-\tfrac32ty w^2+t^2y^2,\qquad
 F_3=w^4-2ty w^3+\tfrac{11}{6}t^2y^2w^2-t^3y^3.
\]
The formal total after moving commuteable \(T,J\)
factors is \(T^{p-1}\) times the product of \(F\)'s,
so only paid scalar moments are used. Set
\[
       \mu(P)=\frac{\ell(T^{p-1}P(\gamma/T)1)}{B_0},
 \qquad \mu(y^j)=\frac{\gamma^j\lambda_{p-1-j}}{B_0}.
\]
Here \(\mu(1)=1\).
For a single local mark, combining the two actual surplus
types gives
\[
   \rho_{d+1}=\rho_1\rho_d+
        \frac{\alpha B_0}{(d+1)L}\big(\mu(F_d)-\rho_d\big).
 \tag{1}
\]
The single mark over \(d+1\) holes is safely located at
the physical donor of that interval, within its window
up to donor \(+d+2\). By induction this calibrates \(f_d\)
as a local constant for every internal interval with
endpoints in the run, starting from the given \(f_1\).

For all safely placed multi-mark tuples the resulting law is
\[
 \boxed{\quad
 \mu\left(\prod_i F_{d_i,t_i}\right)=\prod_i\rho_i
       +\sum_i(\mu(F_{d_i,t_i})-\rho_i)\prod_{j\ne i}\rho_j .
 \quad}                                                       \tag{2}
\]
The run labels may have different steps. Specifically the
signed singleton total provides the first product term
on the right before subtracting the forbidden-block
contribution, and the surplus within one marked link
provides precisely its directional correction from (1).
This is not ordinary independence or multiplicativity.

Use a free polynomial algebra on the labeled generators
to define \(\chi(F_{d,t})=\rho_d\), and \(\delta=\mu-\chi\)
on polynomial lifts. Formula (2) is exactly
\[
   \mu(PQ)=\chi(P)\chi(Q)+\delta(P)\chi(Q)+\chi(P)\delta(Q)
          =\mu(P)\mu(Q)-\delta(P)\delta(Q)
 \tag{3}
\]
within a paid combined grade. Thus the centered form
has rank at most one, and the uncentered form rank at
most two, on any linearly lifted polynomial spaces.
No claim is made that \(\chi\) descends through all
polynomial relations without checking paid products.

## 2. Scalar recurrence incompatibility

Let \(\mu_j=\mu(y^j)\), \(\xi=1/\gamma\).
The tall coefficient recurrence gives
\[
 (p-k)\mu_k=(\xi-2(p-1-k))\mu_{k+1}
                                     -(p-2-k)\mu_{k+2}.
 \tag{4}
\]
A fixed monic quadratic recurrence on sufficiently many
successive rows of (4) cannot hold for a nonzero sequence.
Here are the specific finite facts used below.
For a mode \(r^k\), the residual in (4) is
\[
 r^k A_k(r),\qquad A_k(r)=p-(\xi-2(p-1))r+(p-2)r^2
                                                    -k(1+r)^2.
\]
The coefficient of \(k\) vanishes only at \(r=-1\),
where the constant is \(\xi\ne0\).
The residual of \((a+bk)r^k\) is
\(r^k[(a+bk)A_k(r)+br\partial_r A_k(r)]\).
A nonzero such mode cannot have identically zero residual:
compare highest coefficients for \(r\ne-1\);
at \(r=-1\), use
\(A_k(-1)=\xi,\ \partial_r A_k(-1)=2-\xi\).
For distinct nonzero roots, their polynomial-exponential
components are independent: applying the shift-minus-other-
root to sufficient power annihilates the other mode and
is invertible on the first polynomial mode.
These arguments take place in an algebraic closure for
the proof only and require no real embedding.
A sum of such components satisfies the fixed recurrence
whose factors are the shifts minus the roots, each
with multiplicity one plus its polynomial degree.
As many consecutive zero values as that order force
the sum identically zero.

In particular the rectangular Hankel
\((\mu_{i+j})_{0\le i\le3,\ 0\le j\le2}\) cannot
have rank at most two. If its first two columns are
dependent, \(\mu(1)=1\) makes \(\mu_j=\mu_1^j\)
through the relevant rows. Either ratio zero violates
row zero immediately, or rows 0 and 1 rule out the
nonzero ratio by the affine residual check.
If the first two columns are independent, rank at most
two gives a monic quadratic recurrence for \(\mu\)
at \(k=0,\ldots,3\). For two distinct nonzero roots,
four residual rows kill its exponential-affine
residual; repeated nonzero roots need only three.
If one root is zero, from \(k=1\) on the other mode
is single geometric and rows 1 and 2 kill it; if no
nonzero root remains then \(\mu_2=\mu_3=0\) and
row 1 gives \(\mu_1=0\).
In either zero-root case row zero contradicts
\(\mu_0=1\).

## 3. Single ten-clock joint run, including the exceptional slopes

A joint run of length ten permits all products of reverse
grade at most eight in \(F_1,F_2,F_3\): for total degree
\(D\) mark \(q\) consecutive occupied gaps from the
first stage of the run; with \(h=D+1\) holes the
endpoint window has length at most \(h+q+1\le10\).
For \(t\ne1,2\), the prior explicit odd-part determinant
\(\tfrac43 k^3(k-1)(2k-1)^2\), \(k=t/2\ne0\), makes
\(1,F_1,F_2,F_3,F_1^2\) span degree at most four
at grades at most four. Choose arbitrary linear lifts
of the polynomial basis. Formula (3) makes the
moment pairing on degree at most four rank at most two,
hence also the rectangular Hankel of Section 2.
This is impossible.

For \(t=2\), set \(z=y^2,w=y^3\) so
\(F_1=1+z,F_2=1+z-2w\).
Put \(a=\chi(z),b=\chi(w),A=\delta(z),B=\delta(w)\).
If \(A=0\), formula (3) gives
\(\mu(z^k)=a^k\), \(\mu(z^k w)=a^k\mu(w)\)
in the required degrees. Thus
\(\mu_{k+2}=a\mu_k\) for \(2\le k\le5\).
For \(a\ne0\), the two distinct roots of \(Z^2-a\)
give an order-four residual of (4), impossible in
four successive rows. For \(a=0\),
\(\mu_2=\mu_4=\mu_5=0\), and (4) backwards
kills \(\mu_3,\mu_1,\mu_0\).

If \(A\ne0\), use the relation \(P=w^2-z^3=0\).
Its grade is six, and \(Pz\) has grade eight.
They give \(\mu(P)=0,\ \chi(P)\delta(z)=0\)
by (3), so \(b^2=a^3\) and \(2bB=3a^2A\).
If \(a=0\) then \(b=0\) and
\(\mu_4=\mu_5=0\), again impossible backwards.
Otherwise \(r=b/a\ne0\), \(a=r^2,b=r^3\), and
putting \(d=A/(2r)\) gives \(B=3r^2d\).
The paid expressions \(z,w,z^2,zw,z^3\) therefore give
\(\mu_j=r^j+d j r^{j-1}\) for \(2\le j\le6\).
Its three residuals at \(k=2,3,4\) are impossible
by the single repeated-mode check. Thus \(t=2\)
cannot occur.

For \(t=1\), set \(z=y+y^2,w=yz\), of grades two
and three via \(F_1=1+z,F_2=1+\tfrac32z-\tfrac12 w\).
Use the same symbols \(a,b,A,B\).
If \(A=0\), \(\mu(zP)=a\mu(P)\) in the paid range.
The polynomials \(P_k=z y^k\) have lifts of grade
at most \(k+2\): begin with \(z,w\) and use
\(zy^{k+2}=z(zy^k)-zy^{k+1}\).
Hence the sequence \(T_k=\mu(P_k)=\mu_{k+1}+\mu_{k+2}\)
obeys \(T_{k+2}+T_{k+1}=aT_k\) for \(0\le k\le4\),
paid through grade eight.
If \(a=0\), then \(T_k\) alternates for \(k\ge1\),
so \(\mu_j\) for \(2\le j\le8\) is affine in \(j\)
times \((-1)^j\). The residual check kills it and
then (4) backwards contradicts \(\mu_0=1\).
If \(a\ne0\), the roots of \(r^2+r-a=0\) are
neither 0 nor \(-1\). Thus \(\mu_j\), for \(1\le j\le8\),
is the corresponding two exponential modes (or one
repeated mode), plus an alternating mode: solve
\(\mu_{k+1}+\mu_{k+2}=T_k\), noting shift plus one is
invertible on each non-\(-1\) polynomial-exponential
component. One may extend the exact finite recurrences
to justify this representation through the stated range.
For distinct roots the residual has order at most five
(two exponential-affine modes, plus the constant-amplitude
alternating residual \(A_k(-1)=\xi\)); for a repeated root
it has order at most four. Rows \(k=1,\ldots,5\) of (4)
make it zero, forcing every mode zero. Row zero then
contradicts \(\mu_0=1\).

If \(t=1\) and \(A\ne0\), use \(P=w^2+zw-z^3=0\)
and \(Pz\), of grades six and eight.
They give \(b^2+ab=a^3\) and
\((2b+a)B+(b-3a^2)A=0\).
If \(a=0\), then \(b=0\) and the paid
\(zy,zy^2,zy^3\) values are \(B,-B,B\),
as follows from the same lifts and (3).
Hence \(\mu_j\) for \(2\le j\le5\) is affine
alternating and the residual rows 2,3 again kill it
and then \(\mu_0\).
Otherwise \(r=b/a\ne0,-1\) and \(a=r(r+1)\).
The derivative relation becomes
\((2r+1)B=r(3r+2)A\).
It precludes \(r=-1/2\), so \(d=A/(2r+1)\ne0\)
is defined. On \(z,w\) the tangent and character
values are exactly \(d\) times derivative and
evaluation at \(r\), hence (3) gives this on all
paid lifts \(zy^k,\ 0\le k\le4\).
It follows that
\(\mu_j=r^j+d j r^{j-1}+\eta_0(-1)^j\), \(1\le j\le6\).
The \(r\)-mode residual has degree at most two times
\(r^k\), with nonzero quadratic coefficient because
\(r\ne-1,d\ne0\); the other is
\(\eta_0\xi(-1)^k\). Its recurrence has order four,
so rows 1--4 of (4) and mode independence give the
contradiction. This treats both exceptional slopes
without requiring Schur or a rational-root restriction
on the nonvanishing diagonal.

## 4. Two-run exclusion: lengths eight plus six

Use the exact split placements proved for the canceled-top
Leibniz rule; they depend only on the one surplus hole,
not on its total signed factor. In brief, take the
eight-run first (reflect only the physical indices for
placement if needed). For two marks put one per run.
The only possible earlier overrun is the \((3,3)\)
pair with seven holes; if it occurs all holes have passed
and the later arithmetic mark kills it. For three marks
put two consecutive occupied links in the first run and
one in the second; the only possible one-site overrun
is at the second earlier receiver with six holes, again
killed later. For four marks all targets are one, split
two and two, with safe windows exactly eight and six.
Singles of degree at most three fit either run.
In each case, once the earlier group can survive, at
least its total target count \(D_A\) of holes has passed.
If the second physical run starts at \(b\), locate its
first occupied mark at \(b-D_A\); with \(q_B\) such marks,
its full physical window is
\([b,b+h-D_A+q_B]\), contained in its six-clock run.
Targets are ordered since the runs are disjoint and the
above earlier groups have at most four target holes.
All intended target-plus-extra allocations stay inside
the selected arithmetic runs, which also verifies the
forbidden block placement required in Section 1.
Reflection is only for selecting occupied slots; in the
actual words each link uses its original directed clock
difference and its original step.
These arguments give all required grade-eight products
in same-step labels and the mixed products specified below.

If the two steps are the same, the two local
\(F_1^2\) products (one on either run) and the mixed
\(F_{1,A}F_{1,B}\) product have identical formal left
sides. Let \(d_A=\mu(F_1)-\rho_{1,A}\),
\(d_B=\mu(F_1)-\rho_{1,B}\). Formula (3) gives
\(d_A^2=d_B^2=d_A d_B\), hence \(d_A=d_B\) in a
field, including zero. Thus \(\rho_1\) agrees, and
(1) makes each \(\rho_d\) agree through four
(the calibrations of \(d\le3\) fit either run).
The split placements therefore realize a single labeled
grade-eight law. Section 3 applies.

If the steps differ, keep separate labels \(A,B\)
(long and short). Then \(1,F_{1,A},F_{1,B}\) span
degree at most two, since their \(y^2\) coefficients
are one and their \(y\) coefficients differ.
For a cubic in the long run take \(G=F_{2,A}\)
unless \(t_A=2/3\). At that value take
\(G=F_{3,A}-uF_{1,A}^2\) canceling the quartic.
It is a genuine cubic: the cubic odd coefficient
of \(F_{3,A}\) in \(y+1-t_A/2\) is \(4/81\),
whereas \(F_{1,A}^2\) is even there.
Thus \(\{1,F_{1,A},F_{1,B},G\}\) spans degree
at most three. All its products with
\(\{1,F_{1,A},F_{1,B}\}\) are paid, with the assigned
labels: within the long run the largest are
\(F_{3,A}F_{1,A}\) and \(F_{1,A}^3\), fitting
length eight; within the short run only
\(F_{1,B}^2\), fitting length six.
Mixed products need at most \(F_{3,A}F_{1,B}\)
or \(F_{1,A}^2F_{1,B}\), covered by the split placement.
Apply (3) to linear lifts on these row and column
spaces. The rectangular Hankel then has rank at
most two, which Section 2 rules out. Equal offsets
or global clock distinctness are not required.

## 5. The actual finite scalar consequence

Consider cyclic \(s=p+1,\ p\ge17\) with paid \(B_0\ne0\).
If \(\Delta\ne0\), the companion centered rectangle
gives the no-split joint prefix of length \(s-4\),
or a split joint prefix and affine tail with their
lengths summing to \(s-3=p-2\). In the split, if the
tail step is zero, the constant-clock obstruction
gives tail length at most four, hence prefix length
at least \(p-6\ge10\). If the tail step is nonzero it
is joint by the actual cut formula, and the two
nonzero-step runs total at least fifteen.
Either one is at least ten, or one is at least
eight and the other at least six.
The no-split prefix is also at least ten.
Sections 3--4 contradict all these cases.
Thus \(\Delta=0\) is necessary.
For the zero diagonal \(\Delta=0\) already holds
directly; the local argument did not divide by zero.

In terms of paid scalar values alone,
\[
 \Delta=\gamma^4 B_0\det H_3,\qquad
 H_3=(\lambda_{p-5+i+j})_{0\le i,j\le2}.
\]
For a direct check put \(U=MK-B_0R,\ V=B_0S-K^2\).
The rectangle definitions give
\(E=-2\gamma D+\gamma^2 U\),
\(F=4\gamma^2D-4\gamma^3U+\gamma^4 V\), and
\(DV-U^2=B_0\det H_3\).
This determinant is a nonzero polynomial in \(\gamma\).
At \(\gamma=0\), \(\lambda_j=1/(j+1)!\).
Multiplying each row by its last factorial denominator
gives columns \(x(x-1),x,1\) at three distinct integer
arguments \(x\), hence nonzero determinant over
the rational prime subfield.

For \(p\ge18\), the distinct prior results give:
the paid-top-zero chart is impossible at \(s=p+1\),
and the paid-top-nonzero chart is physically cyclic.
Thus for any common-diagonal \(s=p+1\) method
in that range, \(\gamma=0\) or \(\det H_3(\gamma)=0\).
Over every characteristic-zero field this is a finite
set of possible diagonal values. In particular a
prescribed nonzero diagonal with that determinant nonzero
requires at least \(p+2\) stages there, by the earlier
\(s\ge p+1\) theorem. The proof does not exclude the
remaining nonzero determinant-zero diagonals, assign
a value to the actual \(L\), or claim any root attains
the bound.
