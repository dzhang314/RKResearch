# The invisible five-dirty-label face of normalized DIRK11/13 is empty

Take the explicit normalized hypotheses of the
[signed census](../causal-profile-reduction/dirk-order11-thirteen-signed-cubic-census.md):
literal lower triangular rooted order eleven in thirteen physical
stages, \(C(2),D(1),D(2)\), and the true grade-six surplus.
Assume \(r=0,d=z=5\), where all active cubic defects are invisible
and the five physical ghost dirty rows have distinct numerical
clocks. This is the five-label possibility left by the
[low-dirty census](../causal-profile-reduction/dirk-order11-thirteen-zero-one-low-dirty.md).
There are eight physical clean rows on seven numerical labels,
with a unique doubled clean class. This face is impossible.

The proof invokes the exact finite grade-six arithmetic of the
[fourth/fifth-clean packet](../dirk11-thirteen-fourth-clean/README.md),
but uses a different **weighted** reduction. It does not suppose
the two clean rows have opposite actual output weights. It works
over characteristic zero with the stated signed support and
rank premises, and asserts no new unrestricted stage bound.
The real interval remains **13–14**.

## 1. Exact annihilator and the five live ghost taps

Let \(y=1-c\), \(Y=\operatorname{diag}(y)\), and \(N=A^{\mathsf T}\)
in actual reverse chronology. Write
\[
 W(P)=bP(y),\qquad G=NW(X^2)-W(X^3/3).
\]
The \(d=5\) grade census gives
\(E_6=\mathcal P_5(c)+g\mathcal P_3(c)+K e_T\) and
\(E_7=\mathcal P_5(c)+g\mathcal P_4(c)+K e_T\).
All \(E_7\) vectors agree on the two clean rows of the doubled
class, and the nonzero row \(G\) spans its contrast.
Its latest active nonunit pivot \(j\) belongs to that class,
at reflected clock \(V\ne0\), with
\(A_{jj}=V/2\), \(G_j=b_j V^3/6\).
Thus for \(B=G/(V^3/6)\) one has \(B_j=b_j\), the other
entry \(-b_j\), and all others zero. This is the actual
annihilator contrast, not the restriction of \(b\) at that class.

Set \(D=NB\). The vector \(D\in U_0=E_6^\perp\) is independent
of \(B\). Otherwise the pair-equality subspace would be invariant
under \(A\) and coordinate products, so folding the later member
into the earlier would preserve all rooted tree outputs and
lower triangularity and contradict the thirteen-stage floor.
The \(g\)-weighted \(D\) reads on the five ghosts kill degrees
zero through three, by \(g\mathcal P_3(c)\subset E_6\).
Therefore either every ghost coordinate of \(D\) is nonzero
or all are zero. In the latter case its ordinary moments
through degree five and terminal zero would kill all six
nonterminal clean numerical class sums, leaving just \(B\),
contradiction. So all five ghosts are \(D\)-live. Since \(D=NB\),
each ghost is physically after \(j\) in reverse chronology.
The true \(j\) is the first row after the terminal in reverse:
all other nonterminal ordinary classes are live except possibly
the actual origin, and the other doubled member is earlier
forward.

Put
\[
 \widetilde b=b-B,\qquad \widetilde D=D-(V/2)B .
\]
At \(j\), \(\widetilde b_j=\widetilde D_j=0\), since \(D_j=b_jV/2\).
At the other clean twin, \(\widetilde b\) is the entire ordinary
class mass, not zero: at the five non-endpoint ordinary labels
these masses are all nonzero by the true degree-ten nodal test.
The origin is the only possibly zero-weight *ordinary*
representative. The weights \(\widetilde b\) retain every ordinary
scalar moment, since \(B\) has zero aggregate at its one label.
No assertion of RK tree order for \((A,\widetilde b)\) or for
\(N\) is made or needed.

As before, \(Z_5=E_5^\perp\cap\{T=0\}\) is exactly
\(\langle B,\widetilde D,Y\widetilde D\rangle\) by its dimension
and the two distinct nonzero ghost reads. Likewise
\[
 Z_6=E_4^\perp\cap\{T=0\}
     =\langle B,\widetilde D,Y\widetilde D,Y^2\widetilde D,H\rangle .
\]
Here \(E_4=\mathcal P_4(c)+g\mathcal P_1(c)\), and \(H\) is the
true clean barycentric head supported on the six nonterminal
ordinary representatives of \(\widetilde b\).
Use the singleton origin row even if unweighted, and place
the doubled-class \(H\) mass entirely on the other member,
so \(H_j=0\). It is genuinely in \(Z_6\) by the polynomial
and \(g\)-support tests. Independence follows from the five
distinct live ghost labels and the nonzero clean class sums
of \(H\). Its normalized value at each live non-endpoint
representative \(y=s\) is \(H_s/\widetilde b_s=sJ_4(s)\),
with the common scaling as before, from the true ordinary
Jacobi cardinal read.

## 2. Exact reflected reweighting in the paid equations

Let \(\widetilde W(P)=\widetilde b P(y)=W(P)-P(V)B\).
For positive power \(m\), the actual primitive difference
on this weight is
\[
 N\widetilde W(X^m)-\widetilde W(X^{m+1}/(m+1))
  =G_{m+1}+\frac{V^{m+1}}{m+1} B - V^m D,                     \tag{1}
\]
where \(G_{m+1}=NW(X^m)-W(X^{m+1}/(m+1))\) is paid
from the original \(b\). In particular \(G_2=0\) and
\(G_3=(V^3/6)B\). The actual \(G_4,G_5,G_6\) have the
old annihilator shapes
\[
 \begin{array}{l}
 G_4 = \text{constant}\cdot B+\mu D,\\
 G_5 = \text{constant}\cdot B+\nu(Y)D,\qquad \deg\nu\le1,\\
 G_6 = \text{constant}\cdot B+R_2(Y)D+\chi H,\qquad \deg R_2\le2 .
 \end{array}
\]
Here the ranks and payments are respectively \(E_6,E_5,E_4\)
against grades \(4,5,6\), with actual terminal zero. Substituting
\(D=\widetilde D+(V/2)B\) in (1), the coefficient of \(B\) is
constant because \(B\) is supported at numerical clock \(V\).
That coefficient is **zero**: at \(j\) the modified ordinary
input through that receiver is zero for every positive power
(the only preceding physical row is the zero reflected
terminal), and \(\widetilde b_j=\widetilde D_j=H_j=0\), while
\(B_j\ne0\). Thus (1) becomes exactly
\[
\begin{array}{ll}
 -V^m\widetilde D, &m=1,2,\\
 (\mu-V^3)\widetilde D, &m=3,\\
 (\nu(Y)-V^4)\widetilde D, &m=4,\\
 (R_2(Y)-V^5)\widetilde D+\chi H, &m=5.
\end{array}                                                       \tag{2}
\]
There is no need to reweight the constant-power read \(m=0\).

Similarly the actual rows \(N\widetilde D\in Z_5\) and
\(N(Y\widetilde D)\in Z_6\) have zero \(B\) coefficient,
read again at \(j\) since their inputs are zero through
\(j\). Thus their exact shapes are an affine \(\widetilde D\)
multiplier and a quadratic \(\widetilde D\) multiplier plus
an \(H\) term, respectively. This is the same compensated
marked system as before, with the stationary \(V/2\) baseline
already subtracted. The extra physical \(j\) is silent in
both marked rows because \(\widetilde D_j=0\).

These calculations hold also *at the other clean twin*:
it is an ordinary receiver of weight \(\widetilde b_i\),
even if its original physical \(b_i=0\).
No division by the original weight at that twin is used.
The only division there is by \(\widetilde b_i\), the nonzero
ordinary mass of that class.

## 3. Literal suffix and transfer of the finite obstruction

Order the five live non-endpoint representatives of
\(\widetilde b\) in actual reverse physical order, \(u,v,w,a,b\).
No label is repeated there. The only nonregular stages
after silent \(j\) are the five \(D\)-live ghosts.
Using (2) at \(u\) and its actual inclusive donor set,
only its own label contributes a \(\widetilde b\) positive
power (the terminal is at 0). The first two paid scalar
equations eliminate its diagonal and show
\[
 u\ne V,\qquad
 \widetilde D_u/\widetilde b_u=-u^3/[6V(V-u)],
 \qquad \mu=V(V-u)(V-u/2)
\]
with the third equation. In particular the first
ordinary representative cannot itself be the twin \(V\);
that would make the difference of the second equation
and \(V\) times the first an impossible \(V^3/6=0\).

If a ghost appears before \(w\), its possible positive-power
ordinary donor labels are within \(\{u,v\}\).
Apply \(P=Y(Y-u)(Y-v)\) to equation (2): as in the prior
packet, \(P(V)=\mu\) follows by \(\widetilde D_i\ne0\).
But this gives both \(v=u/2\) and \(v=2u\) using the same
literal scalar read at \(v\). Thus no ghost precedes \(w\).
The \(v\)-nonzero guard for \(\widetilde D_v\) uses its
one earlier regular \(u\) and the genuine \(N\widetilde D\)
equation exactly as before; the silent \(j\) contributes
zero.

For the same cubic \(P\), the actual commutator
\(\mathcal R=CA-AC-A^2\) satisfies
\(\mathcal R^{\mathsf T}\widetilde W(P)\in Z_5\):
the original \(W(P)\) is paid against \(\mathcal R E_5
\subset F_7\), and the correction \(-P(V)B\) annihilates
\(E_7\). This uses the original rooted order, not an
invented order for the reweighted array. Its strictly
included entries at \(j,u,v\) make it identically zero
(first kill the \(B\) coefficient at \(j\), then the
affine \(\widetilde D\) multiplier at \(u,v\)).
Thus the debut \(w\) is literally explicit. The exact
undivided fourth-moment and diagonal formulas of the
previous macro packet apply to (2) and give the same
\(J=0\). The seven-site ordinary scalar measure of
\(\widetilde b\) gives the same Jacobi pencil; all
degree-60 macro candidates are those already certified.

For clarity the shift used in that proof still adds
\(k_s/[u(V-u)]\) to the normalized ordinary donor tap
at \(u\), now with
\(k_s=V(V-u)\widetilde D_s/\widetilde b_s\).
By (2) this gives exactly its first four scalar targets
and same fifth scalar/marked profiles. For a ghost,
division by the nonzero \(\widetilde D_i\) gives exactly
its nonregular compensated moment targets. The
finite proof uses neither the number four of those
ghosts nor any identification of their actual \(g\)
values. It only needs distinct ghost numerical labels,
nonzero marked coordinates, and the actual earliest
optional row. All hold here with five ghosts.
Before \(a\), all ghosts would have the same prescribed
\(z\), so at most one exists and its explicit marked
diagonal is \(z-w\) by the same commutator row.
The optional-fourth residual excludes it. After \(a\),
only the first possible nonregular before \(b\) matters;
the previous two fifth determinants exhaust the with-
and without-intervening-ghost alternatives. Thus all
three prime-101 unit gates transfer to the actual
reweighted equations, a contradiction.

The companion Lean scalar lemma verifies the single-clock
coefficient calibration in (1)–(2) independently of the
particular physical sizes. The field-valued support
and grade transfer in this note is mathematical, and the
already published exact finite replay supplies the
same three scalar exclusions. Neither the still-open
six-ghost face nor arbitrary unnormalized arrays are
covered by this reduction.
