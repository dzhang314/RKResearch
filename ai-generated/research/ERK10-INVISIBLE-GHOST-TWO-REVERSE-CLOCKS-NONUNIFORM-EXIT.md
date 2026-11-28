# Two reverse defect clocks cannot carry a nonuniform one-clock ghost column

Work over any characteristic-zero field and the
[single invisible ghost ledger](ERK10-SINGLE-INVISIBLE-GHOST.md).
The hypothetical strict explicit 14-stage order-ten tableau
has sole zero output weight at physical 2; its original
quadratic defect is invisible. Let \(e=e_2\) and \(r=Ae\).
On the thirteen live sites let \(u\) be the true quadratic
defect of the actual reduced weighted transpose.

**Result.** If \(u\) is active at exactly two clocks, and \(r\)
is active at just one clock, then \(r\)'s nonzero amplitudes
must be uniform. This note excludes the nonuniform case,
not the uniform case or the ordinary 14-stage method.
All clocks and stage indices below use original physical order.
There is no assumed reverse order at high grades.

## 1. Genuine low rooms and the terminal kernel

The true dual room \(W_2=\langle u,Cu\rangle\) is invariant,
so \(r\in W_2\) on live rows is a multiple of the \(u\)-block
at one clock \(t\). Let \(s\) be the other nonzero \(u\)-block,
at \(v\ne t\), so \(W_2=\langle r,s\rangle\).
The old \(F_3=\langle e,r\rangle\) is invariant, hence the
grade-three outgoing rank and \(f_5=5\) force \(f_4=4\).
The fully paid rank-four projection \(F_4|_I=W_3\) earns
the old grade-four lift of \(s\) and any complement \(z\)
to \(W_2\) in \(W_3\). Choose all lifts ghost-zero by
subtracting the value there times \(e\).
In particular \(r,s,z\) vanish at the two old endpoints.

The linear incoming noninvariance of \(W_3\) and then the
old grade-five outgoing bound give at least three distinct
eigenclock labels of \(z\) in the quotient by the invariant
\(W_2\). Indeed its first two powers \(z,Cz\) give the full
live increment into \(F_5\); if their quotient were stable
it would make the old \(F_5\) stable and force \(f_6\ge8\).
Thus
\[
  F_5=Ke+\langle r,s,z,Cz\rangle,\qquad
  \ker(\mathrm{ev}_{14}\mid F_6)
                 =Ke+\langle r,s,z,Cz,C^2z\rangle .
\]
For the second equality, the displayed six actual pure
directions are independent by the quotient labels and are
zero at the terminal. The paid \(e_{14}\in E_5\) has a
model of mean \(b_{14}\ne0\). Its numerical zero advance
with the primitive model yields a pure \(F_6\) direction
of terminal value \(-b_{14}\). As \(f_6=7\), the kernel
has exactly rank six.

If \(r\) is nonuniform, its actual pure square \(r^2\) of
grade six is independent of \(r\) in the \(t\)-block. Since
\(r^2\) is terminal zero, it belongs to that kernel. Its
representation in the quotient is \(H(C)z\) for a
polynomial \(H\) of degree at most two. It is supported
only at \(t\) and is nonzero there in the quotient. Hence
\(H\) vanishes at every other quotient label: there are
exactly three labels, one of them \(t\), and \(H(t)\ne0\).
At \(t\) the literal \(z\) is therefore
\(z=\lambda r^2+\mu r\) with \(\lambda\ne0\).
In particular no \(r\)-dormant \(t\)-row is \(z\)-active.
Outside these three quotient labels, \(z\) vanishes except
possibly for a multiple of \(s\) at \(v\); if \(v\) is not
one of the three, subtract that multiple.

The actual fourth row has
\[
                      c_4=3t/2,\qquad (Ar)_4\ne0.             \tag{1}
\]
To check this without a high-rank premise, put
\(\theta=c_2\ne0\). Then \(r_3=t^2/(2\theta)\ne0\) and
the cubic primitive defect \(A c^2-c^3/3\), in
\(\langle e,r\rangle\), has \(r\)-coefficient
\(\theta^2-2\theta t/3\) by these first two live rows.
If \(c_4=t\), the genuine quadratic and cubic equations
force \(A_{43}=0\), \(r_4=r_3\), and the row sum gives a
literal duplicate of row 3; impossible. Thus \(r_4=0\).
The two equations become \(t A_{43}=c_4^2/2\) and
\(t^2 A_{43}=c_4^3/3\). A zero \(c_4\) would literally
duplicate origin. Therefore (1) follows, including the
nonzero \(Ar\)-read \(A_{43}r_3\).
As \(Ar\) is old pure grade four, (1) forces its clock to
be an active label of \(r,s,z\) different from \(t\).

## 2. Paid moments and the physical census

The true dual rows \(br,bs\) annihilate \(E_6\). Thus at
\(t\) the first three \(r\)-amplitude moments vanish
(\(1,r,r^2\) cost at most six), and at \(v\) we have
\(bs=bs^2=bsz=0\) (the old \(s,z\) cost four).
Nonuniform \(r\) requires at least four \(r\)-active
physical rows: with at most three, the three moments
annihilate each distinct nonzero amplitude separately, so
each group needs two physical rows and only one is possible.

The old pure grade-four vector \(z\) has zero pooled
\(bz\) at each of its three possible active labels by
its six clock moments. The square \(z^2\) is real old
grade eight, so the two pooled moments \(bz^2,bCz^2\)
are zero. The three grouped square masses are therefore
either all zero or all nonzero. At \(t\) the square mass
is \(\lambda^2\sum b_i r_i^4\), the lower powers having
zero moments. With exactly four \(r\)-active rows a
zero fourth mass forces all ordinary amplitude groups
to cancel; a nonzero fourth mass forces four distinct
amplitudes and a nonzero ordinary pool at \(t\).
If the ordinary pool were also zero, the Vandermonde
system in powers zero through three would force each
of the four physical weights to be zero.

For any off-\(t,v\) label with \(z\ne0\) there must be at
least two rows, by pooled \(bz=0\). If there are exactly
two and its square mass is zero, they have equal nonzero
amplitude and opposing weights, so contribute no ordinary
clock site. The \(s\)-carrier group uses at least two
rows and, if it has size two, is uniform and opposing by
its first and second moments. Every \(r,s,z\) direction
vanishes at the old endpoints, so there are at most eleven
non-fully-clean live rows. A fully clean row here means
\(r=s=z=0\), not an assumption on grade-five point exactness.
The ordinary support floor is six.

### A. The two other quotient labels are both off \(t,v\)

After the indicated adjustment, \(z\) is supported at \(t,a,b\)
with \(a,b\ne t,v\). Possible counts for the \(t\)-block,
\(v\)-block, total off-axis rows and fully clean rows are
exactly
\[
           (4,2,4,3),\quad(4,2,5,2),\quad(4,3,4,2),
           \quad(5,2,4,2).
\]
If all three \(z^2\) masses are zero, the four-row \(t\)
block cancels in the first three entries, the \(v\) pair
cancels, and each off-axis pair cancels. In the last entry
only \(t\) can contribute, and in the middle two only a
triple group can. The ordinary capacity is at most three
in every entry, contradiction.

In the nonzero square case the second and fourth entries
have capacity at most \(2+3=5\) (the \(v\) pair cancels).
The third entry would require all four labels \(t,v,a,b\)
effective together with the endpoints. They would all be
interior roots of the fixed six-site Lobatto \(L_4\).
But (1) would then give simultaneous roots \(t,3t/2\),
impossible by the exact norm below.
Thus the only count is \((4,2,4,3)\).
Its six effective labels require \(t,a,b\) and the three
fully clean sites, all distinct. The two \(s\)-rows are
uniform and opposing. By (1), as \(t,3t/2\) cannot both
be Lobatto roots, the fourth-row label must be \(v=3t/2\).
This is not a clean clock: if it were the internal clean
clock it would be a Lobatto root, and if it were 1 then
\(t=2/3\) is not a Lobatto root (it cannot be 0).
Thus there is no other live row at the clock \(v\) beyond
the uniform pair.

### B. One other quotient label is \(v\), the remaining one is off-axis \(a\)

On the physical union of the nonzero \(s,z\) entries at \(v\),
\(s,z\) are independent. The form with diagonal live \(b\)
is nondegenerate and \(s\) is orthogonal to \(1,s,z\)
by \(bs=bs^2=bsz=0\). Thus the union needs at least three
rows. If it has exactly three, \(1\in\langle s,z\rangle\)
(the three directions cannot be independent). The ordinary
mass at that active \(v\)-block is then zero since \(bs=bz=0\).
If in addition \(b z^2\) is nonzero at \(v\), pairing the
expression for \(1\) with \(z\) kills its \(z\)-coefficient:
then \(1\propto s\) on this union and \(s\) is uniform
and nonzero on every one of the three physical rows.

The three active labels have at least \(4,3,2\) rows
respectively. Eleven active rows would leave ordinary
capacity at most five. Ten could reach six only if the
\(v\)-block has at least four, since otherwise its mass
is zero, and if all three active labels are effective.
In that case all three are interior Lobatto roots, and
(1) again gives impossible simultaneous \(t,3t/2\).
Thus the only count is \(4,3,2\), with four fully clean
rows. The active \(v\)-block cancels and the other two
labels \(t,a\) are effective interior Lobatto roots.
The nonzero ordinary pool at the four-row \(t\)-block
forces its fourth amplitude moment nonzero by the preceding
Vandermonde test. Thus all three \(z^2\) pools are nonzero,
including the \(v\)-pool, so \(s\) is uniform on all of its
three active-union rows. By (1) again \(v=3t/2\).
This cannot be any of the fully clean clocks, as for A.

For clarity the standard six-site statement used here is
ordinary degree-nine scalar quadrature with the actual
endpoints 0 and 1 and four distinct remaining nodes:
the product of those four internal clock factors is,
up to scale, \(L_4\) by the anchored \(X(1-X)\)-Gram.
No ordering of the numerical clock values is required.
The exact norm in [the Lean receipt](../lean/RKCert/ReviewedNative/ERK10InvisibleTwoMiddleGate.lean)
is \(A(X)L_4(X)+B(X)\,[8L_4(3X/2)]=9287\) with
\[
\begin{aligned}
A(X)&=-12308436X^3+13451508X^2-3902094X+273591,\\
B(X)&=303912X^3-534744X^2+272748X-33038 ,
\end{aligned}
\]
and \(L_4(2/3)=-1/27\).

## 3. The two true compensated cuts

In A, let \(w\) be the unique fully clean internal clock.
The cubic \(P(X)=(X-t)(X-a)(X-b)\) is proportional to
\(L_4(X)/(X-w)\). At the uniform \(s\)-block with amplitude
\(\sigma\ne0\), remove \(P(v)\) by using
\[
                  T=P(c)-P(c_2)e-\frac{P(v)}{\sigma}s .
\]
This real numerical mask is supported on the two physical
endpoints and the one fully clean internal row. Its scalar
model is \(P\). The vectors \(CT,(1-C)T\) have paid
grade at most four: \(s\) is an actual old grade-four
pure vector but \(Cs=vs\) costs no higher grade.
Then \(A(CT)(1-C)T\) has total grade nine and is
numerically zero by strictness, yet its scalar model is
the known nonzero
[single-middle seam](ERK10-INVISIBLE-GHOST-UNBALANCED-AFFINE-CLOSURE.md#2-a-paid-scalar-and-causal-lemma-when-the-literal-response-is-cubic).
This excludes A.

In B, let the two fully clean internal rows have clocks
\(w,\omega\) in **physical chronological order**.
Take \(P(X)=(X-t)(X-a)\) and the same ghost and uniform
\(s\) corrections. Its true masked values are supported
on the four fully clean rows, and
\(P(X)(X-w)(X-\omega)\) is proportional to \(L_4(X)\).
Use two different paid grade-four masks
\[
                     C(C-w)T,\qquad (1-C)(C-\omega)T .
\]
Their scalar models have degree four and their \(s\)-terms
are still pure grade four, because \(s\) has the one clock
\(v\). The first support can start only at the later
internal row \(\omega\), while the second ends by the
earlier internal row \(w\).
Hence the actual product of the advance of the first
and the second is zero through the grade-nine budget.

After cancelling the square of the common polynomial
scale, this would give the mixed scalar equality
\[
 \int_0^1 J\!\left[X\,L_4(X)/(X-\omega)\right]\,
                        (1-X)L_4(X)/(X-w)\,dX=0.             \tag{2}
\]
The denominator notation signifies polynomial quotients
at the indicated roots. The exact distinct-root detector
in the companion excludes (2). For a compact description,
write \(Q(x,Y)=(L_4(Y)-L_4(x))/(Y-x)\) as a polynomial,
and scale the integral by \(50400/196\) to get the
integer polynomial \(I(x,y)\), where \(x=w,y=\omega\).
The unscaled matrix entries before taking the common factor
196 are
\(50400/((i+2)(i+j+3)(i+j+4))\) for \(i,j=0,\ldots,3\),
applied to the two cubic quotient coefficient vectors.
The companion verifies this scale and, for \(k=0,1,2\),
writes \(14Y^k I(x,Y)\) modulo \(Q(x,Y),L_4(x)\)
as the \(k\)-th row of a \(3\)-by-\(3\) matrix times
\((1,Y,Y^2)^{\mathsf T}\).
At \(x,y\) distinct roots, \(Q(x,y)=0\).
If \(I(x,y)=0\), all three rows kill \((1,y,y^2)\),
so the determinant is zero.
Modulo \(L_4(x)\) that determinant is
\(84(32130x^3-38535x^2+11985x-923)\);
the exact Bézout constant with \(L_4\) is 28823.
Thus it cannot be zero over a characteristic-zero field.
Both surviving physical charts contradict actual paid
cuts, so nonuniform \(r\) is excluded in this scope.

[ERK10InvisibleTwoMiddleGate.lean](../lean/RKCert/ReviewedNative/ERK10InvisibleTwoMiddleGate.lean)
checks the clock norm, all scaled polynomial identities,
the 3-by-3 determinant implication and both nonzero
certificates. The ranked lifts and physical census above
are mathematical, not a full checked order-ten bound.
