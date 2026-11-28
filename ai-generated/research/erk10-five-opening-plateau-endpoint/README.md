# A paid rank plateau forces an exact first reverse primitive

**Paid-field theorem.** Let the high block have \(n\le10\)
strictly explicit physical stages and satisfy the actual
order-ten short reverse word budget specified below. Over
any field with \(10!\ne0\), its true score vector obeys
\[
                     K\boldsymbol w=Y\boldsymbol w,
\]
where \(K=B^T\) in reverse causal coordinates and
\(Y=\operatorname{diag}(1-\boldsymbol x)\). This is an
equality on every high physical row, not just on clock pools.
In particular the **last nonzero-weight high stage in forward
order has clock \(1\)**. This need not be the last physical
stage, and the result does not assert stiff accuracy. No
score, clock, clock difference, or ordering is assumed in
the theorem beyond the stated scalar field condition and
word budget.

**Rational consequence.** The full
[literal five-opening, ten-high decoder architecture](../erk10-five-opening-nonsplit-kernel/README.md)
is impossible over \(\mathbb Q\), with any valid placement
of endpoints, high zeros, repeated clocks, and zero, signed
or cancelling scores. This now combines the paid endpoint
necessity with the complete reverse-first endpoint census.
This is **not** an unrestricted rational 15-stage ERK10
lower bound. A different opening, output support or
interface can still give a rational tableau.

## Exact hypotheses on the construction

The field theorem needs only a strictly lower forward high
block \(B\), high clock vector \(\boldsymbol x\), high scores
\(\boldsymbol w\), and the following exact tests. Let \(E\)
denote evaluation on the high clocks, and \(J\) the formal
polynomial lower primitive on \([0,1]\), integrating from
zero. For every forward word \(W\) in \(B\) and forward
clock marking of length \(m\le5\), and \(f=X^k\) with
\(1\le k\le9-m\), require
\[
  \boldsymbol w^T W E f=I(W_s f),\qquad
  I(p)=\int_0^1p(X)\,dX .
\]
\(W_s\) replaces \(B\) by \(J\) and the mark by multiplication
by \(X\); the empty word gives the scalar moments of degrees
one through nine. Here all integrals are linear maps on
polynomials with the paid denominators \(1,\ldots,10\).
There is no analytic interval assumption. The old origin
can be scored arbitrarily: every source test used here has
zero constant value.

For the rational consequence we use precisely the regular
five-row decoder of the cited construction: opening clocks
\(0,e,s,p,q\), with \(e,s,p,q\ne0\), \(s,p,q\) distinct,
\(P=X^3+u_0X^2+v_0X\), \(P(s)\ne0\), and
\(p(3s^2+2su_0+2v_0)=s v_0\). The opening rows and
quadratic decoder \(\Pi\) are those in that packet. The
high-to-old block is literally \((EJ-BE)\Pi\), and the
high block pays the physical purity gate \(BEP=EJP\)
(purity through normalized stage-derivative size five).
Only the opening origin may carry an opening output
score. This exact chart earns the short word budget from
the actual trees. No claim is made for arbitrary five-row
openings, high profiles that fail that purity gate, or
opening scores off the origin. The field theorem itself
also applies to any other construction that earns all
the same short tests.

## Actual reverse graded observers

Let \(Y\) be the diagonal mark by reverse ordinates
\(\boldsymbol y=\boldsymbol1-\boldsymbol x\). In
reverse chronological indexing \(K=B^T\) is strictly
lower causal. For a reverse word \(V\) in \(K,Y\), let
\(V_s\) replace them by the formal reverse primitive
\(J_y\) and multiplication by \(y\). Its literal defect
is \(V\boldsymbol w-\boldsymbol w\odot(V_s1)(\boldsymbol y)\).
Let \(D_j\) be the increasing span of all such defects
of length at most \(j\). In particular
\[
\begin{split}
 \boldsymbol v &=K\boldsymbol w-Y\boldsymbol w\in D_1,\\
 \boldsymbol u &=K(Y\boldsymbol w)-Y^2\boldsymbol w/2\in D_2 .
\end{split}
\]

A defect of grade \(j\le5\) annihilates every positive
forward polynomial of degree at most \(9-j\).
Indeed \(K\) is the true transpose and the nominal
adjoint to \(J\) is \(J_y\), by polynomial
integration by parts. Each occurrence of \(Y\) is
the identity minus the forward clock mark in this
adjoint calculation, so expands into paid words of
no greater length. In particular \(D_4\subseteq\ker\mu\)
for \(\mu(\boldsymbol f)=\boldsymbol x^T\boldsymbol f\).
Clock marking \(Y\) and transport \(K\) both send
\(D_j\) into \(D_{j+1}\): for \(Y\) this is exactly
the longer marked word. For \(K\), subtract from the
longer word the primitive error on the earlier nominal
polynomial, which is a sum of \(K Y^i\) word defects
with \(i\le j\). Hence these are deductions using
real score-weighted words, not a stage-order assumption.

## The actual rank-three cap

The five nominal vectors
\(\boldsymbol w\odot\boldsymbol x^{\odot j}\),
\(0\le j\le4\), are independent modulo \(D_4\).
Their first five positive forward probes give
\(H_{ij}=1/(i+j+1)\), \(1\le i\le5,\,0\le j\le4\),
with determinant \(1/(2^{12}3^7 5^5 7^4)\).
The [portable integer inverse](../../lean/RKCert/ReviewedNative/ERK10EndpointHilbertFive.lean)
certifies this nonsingularity by casting its product at scale
2520 into the paid field. Equivalently take powers of \(y\) by an invertible
triangular basis change. This also shows **at least
five distinct nonzero forward clock pools are live**:
the same matrix factors through those pools. A
possibly scored high \(x=0\) or the scored opening
origin does not contribute to any of these positive
moment pairings.

There are two independent actual forward residuals
annihilating both \(D_4\) and the nominal span. Take
the column map \(T(f)=BEf-EJf\) for \(f=X,\ldots,X^4\).
It annihilates the nominal rows by the short tests
with a real extra \(B\) and the same nominal primitive.
For a reverse-word defect of grade at most four,
the \(EJf\) pairing is zero by its positive tests
(\(\deg Jf\le5\)); the \(BEf\) pairing is zero by
dualizing a word of length at most five and the
same integration-by-parts identity as for the
nominal polynomial. Thus the whole residual image
annihilates the combined space.

For its rank, use the first nonzero forward
high clock \(a\) and the first different nonzero
one \(b\) in forward causality. The two physical
residual rows on \(X^k\) are
\[
 -a^{k+1}/(k+1),\qquad S a^k-b^{k+1}/(k+1),\qquad 1\le k\le4,
\]
where \(S\) sums the actual preceding \(a\)-taps.
All earlier zero clocks disappear from these expressions.
If dependent, with ratio \(r=b/a\ne0,1\), then
\(r^{k+1}\) is affine in \(k+1\); its first second
difference is \(r^2(r-1)^2\ne0\), contradiction.
The rank ledger is therefore
\[
                       5+\dim D_4+2\le n\le10 .
\]
The masked nominal score also satisfies
\(\mu(Y\boldsymbol w)=I(X(1-X))=1/6\ne0\).

## Why a pure plateau cannot occur

Let \(S\) be the *silent* subspace
\[
  S=\{\boldsymbol f:\mu(Y^k\boldsymbol f)=0
                              \text{ for every }k\ge0\}.
\]
It is invariant under \(Y\). Equivalently these are
precisely vectors with zero aggregate at each distinct
nonzero forward clock: multiply by \(X\) and use
Lagrange polynomials in \(y\) to isolate each visible
pool, noting that its \(X\) is nonzero. A high \(x=0\)
coordinate remains free.

Suppose a subspace \(F\subseteq S\) is invariant under
both \(K\) and \(Y\), and contains the actual
\(\boldsymbol u\). Let \(Q\) be the global projection
killing every coordinate with \(y=0\). It is a polynomial
in \(Y\), for example evaluate
\(1-\prod_{a\ne0}(1-Z/a)\) on \(Y\), with one factor for
each distinct nonzero reverse ordinate \(a\).
Thus \(QF\subseteq F\). Restrict to *all* nonzero-\(y\)
rows; write \(F_*\) for the restrictions and \(K_*\)
for the literal strict principal block. \(K_*\) preserves
\(F_*\), since a restricted vector lifts to \(F\) with
zero \(y=0\) coordinates by \(Q\); \(Y_*\) also preserves
it. The actual equation
\[
 (K_* -Y_*/2)(Y\boldsymbol w)_*=\boldsymbol u_*
\]
uses exactly this block because \(Y\boldsymbol w\)
is zero at every omitted coordinate.
The operator \(K_*-Y_*/2\) has nonzero diagonal and is
strict triangular off it, hence is invertible.
Its restriction to the finite-dimensional \(F_*\)
is injective and maps into \(F_*\), so is surjective
there. Therefore \((Y\boldsymbol w)_*\in F_*\),
and the zero lift by \(Q\) gives
\(Y\boldsymbol w\in F\subseteq S\). This contradicts
\(\mu(Y\boldsymbol w)=1/6\). Alternatively it would
give \(yW_x=0\) at every visible pool, leaving at most
the endpoint against the five-live-pool ledger.

Whenever \(D_j=D_{j+1}\subseteq S\) for \(1\le j<4\),
this is such an impossible invariant space (it contains
\(\boldsymbol u\in D_2\subseteq D_{j+1}\)). The portable
native endgame uses the equivalent already established
causal-coordinate correction lemma, which proves the
same membership without explicitly inverting a matrix.

## Rank spent by nonsilent directions

To avoid any generic-node or distinctness assumption,
form the augmented flag \(W_j=D_j+S\). Each \(W_j\)
for \(j\le4\) is in \(\ker\mu\), and \(Y W_j\subseteq
W_{j+1}\). If some \(D_j\not\subseteq S\), its
augmentation begins strictly above \(S\), and every
subsequent inclusion through \(W_4\) is strict.
Otherwise a plateau would be an invariant subspace
inside \(\ker\mu\) and hence lie in \(S\) by repeated
\(Y\)-marking, a contradiction. Thus an escape at
grade \(j\) costs at least \(5-j\) dimensions modulo
\(S\) in \(D_4\). Formally use
\(\dim(D_4+S)-\dim S=\dim D_4-\dim(D_4\cap S)\).
This argument needs no cofactor computation; only the
\(X\)-test at grade four and the true mark transitions.

First \(D_1\subseteq S\), since an escape would cost
four dimensions. Suppose now \(\boldsymbol v\ne0\).
This supplies at least one pure dimension in \(D_1\).
An escape at grade two would cost three more, so
\(D_2\subseteq S\). The first-to-second inclusion is
strict by the pure plateau obstruction; hence \(D_2\)
supplies at least two pure dimensions. An escape at
grade three would cost two more, so \(D_3\subseteq S\)
as well. Both \(D_2\to D_3\) and \(D_3\to D_4\) must
be strict by the same plateau obstruction. This forces
\(\dim D_4\ge4\), contradiction. Thus \(\boldsymbol v=0\)
on every actual row. Strict causality at the first
reverse row with nonzero score gives \(0=(1-x)w\)
there, proving \(x=1\) over the field.

For a commutative ring inverting \(10!\) with the
same actual normalized word tests, each coordinate
of \(K\boldsymbol w-Y\boldsymbol w\) is nilpotent.
Indeed reduce modulo each prime and pass to the
fraction field of the quotient; the paid-field theorem
applies, so the coordinate is in every prime. In a
reduced ring the entire profile is zero. In a general
ring this argument does not cancel a zero-divisor
weight to assert an endpoint value. The ring deduction
uses algebraic specialization, not ordering.

## Trimming unscored terminal rows and padding only for the earlier census

The paid theorem does not require any trimming. To apply
the earlier **physical first reverse endpoint** census
over \(\mathbb Q\), delete the initial reverse run of
score-zero high rows before the first live one.
These are the last forward stages, unused by any
surviving stage because the tableau is strictly explicit.
They contribute no output. Every surviving row profile
and weighted rooted output are unchanged; directly,
every forward word on the surviving rows ignores
removed columns by causality. The five opening rows
are untouched, and all surviving decoder and purity
equations use the same shorter \(E,B\) and identical
older columns. The paid theorem guarantees the
new physical first reverse row is \(x=1\).

If fewer than ten high rows remain, restore the original
width by inserting unscored literal clones immediately
after any surviving nonendpoint high row in **forward**
order. A clone uses only the original row's predecessors
with precisely the same coefficients, no row reads
the clone, and the original row does not read itself.
Its clock and normalized stage profile are the
original's. The actual decoder and \(BEP=EJP\)
continue to hold row by row; the tree outputs and short
word tests stay unchanged. Such a nonendpoint row exists
by the five-live-pool ledger; its clones remain
before the last forward high row \(x=1\).
Now the [full reverse-first endpoint census](../erk10-five-opening-zero-high-seven/README.md)
rules out the rational tableau with or without any
high zero. This padding is solely a bridge to that
exact-width census, not part of the field proof.
The known [15-stage characteristic-17 method](../erk10-fifteen-f17/README.md)
has the required last live endpoint and is not excluded.

## Replay and native scope

`python audit.py` checks the exact rank constants,
the forward second difference, and algebraic fixtures
for the global projection and actual triangular solve.
Add `--f17 path/to/tableau.json` to check the complete
raw grade-one equality and last live clock on the
published 15-stage prime-field literal.
See [Lean verification scope](LEAN.md). The [native module](../../lean/RKCert/ReviewedNative/ERK10EndpointPlateau.lean)
checks the augmented flag dimension cost, the invariant
plateau proof of the full physical primitive equality
and final live endpoint, and the two-paid-moment
nonzero nominal target. It consumes the actual maps
and an explicit rank-three flag. The derivation of
that flag from the short words, the rational census
integration, and the ring specialization are
mathematical here, not end-to-end Lean order theorems.
