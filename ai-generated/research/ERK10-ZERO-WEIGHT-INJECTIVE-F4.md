# Injectivity in grade four forces one zero ERK10 output and a marked reverse

Use genuine rooted profiles on a strict explicit fourteen-stage
order-ten tableau over a characteristic-zero field, with at least
one zero output weight. Let \(I=\{i:b_i\ne0\}\),
\(B=\operatorname{diag}(b)\), \(c=A{\bf1}\), \(C=\operatorname{diag}(c)\),
and \(E_j,F_j\) as in the
[order-ten equality ledger](ERK10-FOURTEEN-STAGE-EQUALITY.md).
Assume **\(B\) is injective on the original \(F_4\)**.
Then there is **exactly one zero-weight physical coordinate**.
Its genuine reduced weighted transpose has the same graded
pure profiles through four, as described below.
If the single ghost is the origin, that reverse is **exact to
weighted size nine** (rooted grade at most eight), but it **fails
ordinary order six** by one exact grade-five alias.
The interior ghost and the noninjective case have separate
conditions, not treated as ordinary exact reversals.

All stage numbers below are one-based original physical
indices unless an order is explicitly called reversed.

## 1. Exact low-grade live-reverse theorem

From the paid grade budget, \(B F_4\) as a row space
is contained in \(V_3=E_5^\perp\), of rank three.
Injectivity and the universal low pure rank give
\[
       f_j=j-1\quad(2\le j\le4),\qquad
       B F_4=V_3 .
\]
So all the annihilator rows \(V_1,V_2,V_3\subset V_3\)
are entirely live. In particular each ghost coordinate
indicator \(e_g\) belongs to \(E_5\). For any of its
degree-five polynomial models \(P_g\), moment exactness gives
\[
             \int_0^1 X^a P_g(X)\,dX=0,\qquad 0\le a\le4.
\]
For an original grade-at-most-three pair \((x,P_x)\),
the true ghost tap satisfies
\[
 \langle x,Ae_g\rangle_B
    =\int P_x\, J P_g
    =\int (\bar J P_x)P_g=0 ,
\]
where \(J=\int_0^X,\ \bar J=\int_X^1\).
The first product costs at most \(3+6=9\);
the last zero uses \(\deg\bar J P_x\le4\).
No vanishing of \(P_g\) at an origin ghost is assumed.

Let \(A^\vee=B_I^{-1}(A_{I,I})^{\mathsf T}B_I\)
with reverse physical chronology. Its clock is \(Y_I=1-c_I\)
by the old equality \(bA=bY\). For \(2\le j\le4\),
the actual old projected pure space \(F_j|_I\) is exactly
\((E_{9-j}|_I)^{\perp_{B_I}}\):
all old rows in the annihilator are live, so restriction
does not change its codimension, and equality follows
from the paid dimension \(j-1\).
It also vanishes at the reversed origin (physical 14)
by old grade-four point exactness.

For any old input \(x\) and test \(z\), actual submatrix
adjointness gives
\[
 \langle A^\vee x_I,z_I\rangle_{B_I}
 =\langle x,A z\rangle_B-
            \sum_{g\notin I}z_g\langle x,Ae_g\rangle_B.
\]
For reverse unary grade \(j\le4\), its degree-\((j-1)\)
reverse input lifts to an old pair with the same model
in variable \(X\), by induction. The ghost correction
just shown is zero. Testing the functional against
\(E_{9-j}\) pays the scalar integration by parts exactly,
so the reverse unary defect belongs to \(F_j|_I\).
Products of the lower numerical and polynomial pieces lift
to original products, with the same total grade.
This proves the true reverse pure inclusion
\(\bar F_j\subset F_j|_I\) through grade four.
A zero numerical reverse pair with polynomial \(P\) now
pairs to zero against every degree-\(\le j\) ordinary
clock polynomial; degree \(2j\le8\) and the nonsingular
Hilbert Gram give \(P=0\). Thus the reduced reverse
is polynomially separated through four, and its
strict pure growth forces equality of the pure ranks.
In particular
\[
               \bar F_j=F_j|_I,\qquad
               \bar E_j=E_j|_I\qquad(j\le4)
\]
with the same low pure-plus-clock model after reflection.
This is the exact hypothesis used below, not full
ordinary order ten.

The [reviewed incoming Hermite gain](../lean/RKCert/ReviewedNative/ForwardNodalGain.lean)
now forbids \(C\)-invariance of \(F_4|_I=\bar F_4\):
if invariant, separated grade four and \(\bar f_3=2\)
give \(\bar f_4\ge 2+2=4\), contrary to 3.
The same incoming theorem on the old tableau forbids
old \(C\)-invariance of \(F_4\).

## 2. Exactly one zero weight: the terminal-marker argument

For a nonorigin ghost \(g\ne1\), its model \(P_g\)
vanishes at \(X=0\) since an old pure model agrees
with its origin evaluation. The five preceding moments
then give \(P_g=0\) by the anchored \(X\)-Gram on
\(P_g/X\). Thus \(e_g\in F_5\).
Any two such internal indicators are independent modulo
\(F_4\), since \(B\) is injective on \(F_4\).
If both existed they would fill the rank-two increment
\(F_5/F_4\). Then \(F_5|_I=F_4|_I\), making the latter
clock invariant (because \(CF_4\subset F_5\)),
contrary to §1. There is at most one nonorigin ghost.

If there is a ghost at physical 1, its anchor model
is the normalized degree-five shifted Legendre polynomial
\[
 \Lambda=1-30X+210X^2-560X^3+630X^4-252X^5.
\]
It has value 1 at 0 and zero moments against \(1,X,\ldots,X^4\);
uniqueness follows by applying the anchored \(X\)-Gram to
a difference with value zero at 0.
Its value at 1 is \(-1\). Consequently
\(w=e_1-\Lambda(c)\in F_5\) with **\(w_{14}=1\)**.
If a further internal ghost \(g\) existed, then
\[
                   F_5=F_4+K e_g+K w
\]
by the ranks: \(B\)-injectivity separates \(e_g\),
and \(w\)'s terminal coordinate separates it from
\(F_4+K e_g\). But \(C F_4\) has terminal coordinate zero
as \(F_4\) does, and hence \(C F_4\subset F_4+K e_g\).
After live projection this again makes \(F_4|_I\)
clock-invariant. Thus origin and internal ghosts cannot
coexist in this injective branch. Exactly one ghost remains.

One can also fix the *shape* of the surviving old low flag.
There is exactly one visible quadratic-defect clock
\(\theta\): at most one by the
[zero-weight frontier](ERK10-ZERO-WEIGHT-LIVE-TRANSPOSE.md),
and at least one because \(d=Ac-c^2/2\ne0\) and \(B\)
is injective on \(F_4\). The old pure vector
\(Cd-\theta d\) projects to zero, hence is itself zero.
The paid triangular argument makes \(r_0=Ad\)
independent of \(d\), so old
\(F_3=\langle d,r_0\rangle,\ F_4=\langle d,r_0,Cr_0\rangle\):
the final rank follows from noninvariance and \(Cd=\theta d\).
If \(r_0\) were supported outside \(\theta\) on at most
one other clock, this rank-three span would split into
its two numerical clock blocks and be invariant.
Therefore there are at least two different outside
support clocks. Now \(d^2\in F_4\), and its affine
\(r_0\)-coefficient vanishes at those two distinct clocks.
So \(d^2\) is proportional to \(d\), making all its
nonzero amplitudes equal. The same conclusion holds
for the actual reduced reverse quadratic defect since
its rank-one pure space is the same projected line.

## 3. Origin-only: exact mixed recursion and weighted size nine

Suppose the single ghost is physical 1. This is automatically
an injective \(F_4\) case, since all old pure vectors
vanish at the origin. For an original context pair
\((z,Q)\) of grade \(a\) with \(z_1=0\), and any actual
reduced reverse pair \((v,P)\) of grade \(g\) with
\(a+g\le9\), we have
\[
                        \langle v,z_I\rangle_{B_I}=\int P Q .
\]
The proof inducts on reverse rooted operations. The unit
case is old exactness. At a reverse unary step, actual
adjointness has no deleted-coordinate term since \(z_1=0\);
it moves to the old context \((Az,JQ)\), whose origin
value is still zero by strictness, with one grade used.
The scalar counterpart is formal integration by parts.
At a product of two reverse rooted factors one factor
has grade at most four because \(g\le9\).
Use its proved old lift from §1 (same model), and absorb
it into the old context by a Hadamard product.
The origin condition remains zero and the grade budget
is unchanged. Linearity handles spans of rooted pairs.

Taking \(z=c\) costs one grade and gives the actual
thirteen-row reduced reverse with output \(\beta=b_I C_I\)
exact for \(\int X P(X)\,dX\) through rooted grade eight.
In reflected variable \(y=1-X\) this is precisely
\(\int (1-y)P(y)\,dy\), the **shift-one weighted size-nine**
convention. The [weighted floor of 13](WEIGHTED-ORDER-NINE-SHIFT-ONE-ATLAS.md)
therefore applies. This reverse has no literal duplicate,
since that would preserve its weighted tests on 12
stages. The floor's case atlas excludes a 12-stage
candidate; it does not, by itself, exclude this 13-stage
equality chart or give ordinary order ten.

## 4. Exact grade-five rank and alias, not full ordinary order

For origin only, the actual reversed \(E_5\) is contained
in \(E_5|_I\): take in the mixed recursion any old
grade-four pure context \(f\in F_4\), which vanishes
at the origin and has zero model. Then every reverse
grade-five vector is orthogonal to \(F_4|_I\), and its
annihilator is exactly \(E_5|_I\) by \(BF_4=V_3\).
Since \(e_1\in E_5\) and it is the sole omitted
coordinate, \(\dim E_5|_I=10\).

We also need the physical fifth-rank gain in a version
**not assuming separation at grade five**. For the
present rank-three, single-clock reverse, the local
dependent fifth-grade proof from the
[paid grade-five surplus](../lower-bounds/paid-beta/01-PAID-GRADE-FIVE-SURPLUS.md)
has exactly that scope: if \(\bar f_5=4\), clock
noninvariance forces \(\bar F_5=\langle v,R,CR,C^2R\rangle\)
for a carrier indicator \(v\) and its response \(R\).
The first four-stage contact uses only separated
grade-four profiles, and the fifth contact uses just
that actual rank-three flag.
For clarity one may **compress on \(E_5\)**, keeping
independent evaluations from the start and redirecting
each omitted predecessor to its earlier \(E_5\)
combination, as in that cited proof. This preserves
all pairs through grade five and even the next unary
operation. This compression preserves actual rank and
pure pair-space despite a hypothetical polynomial
alias: restriction on the numerical \(E_5\) is an
isomorphism, and induction preserves the formal model.
There are still at least eight stages (already the
actual separated \(E_4\) rank), with no literal
duplicates. The
[fifth-head calibration including a carrier fifth row](ERK10-SINGLE-INVISIBLE-GHOST-DEPENDENT-THIRTEEN.md#4-the-actual-fifth-contact-including-a-carrier-there)
then pays \(c_4=c_5=p\), \(a_{54}\ne0\),
and \(p\ne c_3,\ R_4\ne0\).
The row
\(H=e_5^{\mathsf T}-\epsilon e_2^{\mathsf T}-(R_5/R_4)e_4^{\mathsf T}\)
(\(\epsilon\) the fifth carrier indicator) kills the
alleged pure grade-five span. It would kill \(A(CR)\)
too, but subtracting \(c_3H A R=0\) leaves exactly
\((p-c_3)a_{54}R_4\ne0\). This is the genuine
local contradiction; no grade-five polynomial
separation or ordinary reverse order was used.
Thus \(\dim\bar F_5\ge5\) (noninvariance also rules out a
plateau at rank 3).

The degree-five numerical clock space on the live set
has dimension six by the anchored ordinary quadrature
support floor. Any pure reverse grade-five member
that is a numerical clock polynomial \(P(c_I)\)
vanishes at physical 14, hence \(P(1)=0\).
The genuine mixed tests with \(z=X^j(c)\), \(1\le j\le4\),
give \(\int X^j P=0\) (the old origin values are zero).
Writing \(P=(1-X)R\), these four exact moments under
\(X(1-X)\) force \(R\) proportional to the fixed
degree-four \(L_4=42X^4-84X^3+56X^2-14X+1\).
Thus the intersection of the reverse pure \(F_5\)
with the numerical clock quintics has dimension at most one.
Together
\[
       10\ \ge\ \dim\bar E_5
       \ \ge\ 6+\dim\bar F_5-1
       \ \ge\ 10
\]
gives exact ranks and forces the actual nonzero alias line
\[
                         K\,P_*,\qquad P_*=(1-X)L_4(X).
\]
Indeed \(P_*(c_I)\in\bar F_5\), so subtract this pure
vector from its clock pair to get a numerical zero
with formal model \(P_*\). Its ordinary mean is
\(\int P_*=1/30\), nonzero, so the reduced reverse
with the original output weights **fails ordinary
order six**, notwithstanding its weighted size-nine
exactness. These are distinct output claims.

In particular put \(S=F_4|_I+C(F_4|_I)\), of rank four
by noninvariance and the old terminal marker.
The old projected \(F_5\) is \(S+K\Lambda(c_I)\)
and the actual reduced reverse pure \(F_5\) is
\(S+K P_*(c_I)\). They cannot be identified: the
old pure flag annihilates the ordinary output everywhere,
but the latter new column has the stated nonzero mean.

## 5. A sole internal ghost that is point-exact through four

For a sole internal ghost \(g\), its indicator is pure
\(F_5\) and the old projected \(F_5\) equals the rank-four
space \(S\) just defined, by noninvariance and the dropped
one-dimensional pure ghost line. In any case \(\dim E_5|_I=10\).
Suppose additionally that \(F_4\) vanishes at \(g\).
Then the upper inclusion \(\bar E_5\subset E_5|_I\) still
holds: at the one additional unary root the old pure
test \(f\in F_4\) has \(f_g=0\), killing its correction;
products use old pairs through grade four.
The same local fifth-rank gain applies.

For the possible grade-five pure clock polynomial
\(P(c_I)\), its actual weighted pairing against every
\(Q(c_I)\) with \(\deg Q\le4\) and \(Q(c_g)=0\)
is still \(\int P Q=0\) by the single-root adjoint
argument (and by the old low lifts on any product).
Again \(P(1)=0\). With \(P=(1-X)R\), multiplication
by \(X-c_g\) is injective on cubic polynomials and
produces a four-dimensional test space of quartics
or less. Nondegeneracy of the \(1-X\)-Gram on degree
four makes the common kernel on quartic \(R\) a line,
without any assumption ordering \(c_g\).
As with origin only, \(\dim\bar E_5=10,\ \dim\bar F_5=5\),
and this unique line of \(P\)'s is an actual reverse
quintic alias. Its mean is nonzero: if also tested
against 1 a zero mean were obtained, the entire
degree-four polynomial space would be tested, and
the same anchored Gram would give \(P=0\).
This is again ordinary reverse-order-six failure;
the weighted-size-nine propagation in §3 assumes
an origin ghost and is **not** used for internal ghosts.

There is no such point-exact internal ghost at clock 0
or 1. At clock 0 its evaluation on \(E_4\) equals the
earlier physical origin. Replace its frozen outgoing
column by an equal read of physical 1. The correction
vanishes on any original input grade at most four,
and on a higher pair is a multiple of \(Ae_g\in F_6\)
so preserves the old formal models by induction.
The new strict tableau can delete the zero-weight
ghost, contradicting the 14-stage floor. At clock 1
the ghost agrees on \(E_4\) with the later live terminal
at physical 14, so the
[exact stage-mixture revival](ERK10-REVIVING-MATCHED-ZERO-WEIGHT-STAGES.md)
would give an excluded all-live 14-stage tableau.
The same early deletion or later revival applies to
any \(E_4\) look-alike at an internal clock.
No such point exactness at a general ghost is presumed.

[ERK10ZeroInjectiveF4Gate.lean](../lean/RKCert/ReviewedNative/ERK10ZeroInjectiveF4Gate.lean)
checks the exact ghost-origin polynomial moments,
the special alias moments, and the graded mixed-root
induction as a reusable theorem with actual adjoint and
low-lift hypotheses. The pure-rank, initial-value and
rooted-model bridges are the mathematical proof above.
There is no unrestricted numerical stage improvement.

The [subsequent internal-stage argument](ERK10-ZERO-INJECTIVE-INTERNAL-EXCLUSION.md), combined with the sole-origin exclusion, rules out the entire injective case. It does not rule out noninjectivity.
