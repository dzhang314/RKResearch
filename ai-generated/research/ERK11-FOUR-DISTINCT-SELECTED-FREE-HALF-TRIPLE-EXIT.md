# Four distinct calibrations: excluding the selected-free chart when a half is the triple

**Scope.** In the four-distinct part of the
[nonzero-mass eight-clock atlas](ERK11-LIVE-TRIPLE-EIGHT-CLOCK-HANKEL.md),
take left extras \(\{e,t\}\) and right extras \(\{h,t\}\),
sharing the same free label \(t\). This packet excludes
a triple at one of the halves \(h,e\), over characteristic
zero. When neither is the triple the earlier
[two-half crossing packet](ERK11-FOUR-DISTINCT-TWO-HALF-CROSS-EXIT.md)
already excludes the chart. Thus this selected-free geometry
is entirely closed; other four-distinct schedules remain.

## 1. Additional actual inner support

The common selected free label \(t\), as well as both halves
\(h,e\), occurs once on each front. Let \(q\) be the half which
is the triple, and \(u\) the other free label (not selected on
either front). Then the three inner rows are \(\{q,u,u\}\),
since the triple needs one more occurrence and the pair at
\(u\) needs both. There are no internal dormant noncarriers
in the thirteen-active chart.

The actual forward and reflected grade-four square-clock
vectors \(V_L,V_R\) have models
\(V_a=X^2(X-a)^2\) and \(V_b=(1-X)^2(X-d)^2\).
Their numerical product is supported only on physical
rows 8 through 10 by the two genuinely new seventh
boundaries. Multiply by \((C-qI)(C-uI)\) to annihilate
this actual product. Since \(4+4+2=10\), the corresponding
model equality is paid by order eleven using the common
actual low-grade spaces:
\[
 \int_0^1 V_a(X)V_b(X)(X-q)(X-u)\,dX=0.
\]
No forward or reverse fifth-grade square is needed.
Write \(I_j=\int_0^1 X^j V_aV_b\) for \(j=0,1,2\).
This constraint is \(I_2-qI_1+u(qI_0-I_1)=0\),
and no division by the linear coefficient is used.

## 2. Exact two-polynomial clock intersection

Use the 3-by-3 Hankel determinant \(D=0\), its proved-live
minor \(\Delta\ne0\), and Cramer numerators \(A,B\) with
scaled free quadratic \(Y^2+AY+\Delta B\). These are
the four-distinct guards of the existing atlas. The
first contact on rows 7 and 11 yields its norm \(C=0\)
from the **same selected free root** choice of the
two-half packet; this contact is independent of whether
the halves are pairs or triples. That earlier proof's
crossover equality is not used here.

For each \(g=h,e\) form the polynomial
\[
 E_g(Y)=\Delta(I_2-gI_1)+Y(gI_0-I_1)
\]
and take its quadratic norm modulo \(Y^2+AY+\Delta B\).
The norm for \(g=q\) vanishes because evaluation at the
actual \(Y=\Delta u\) is zero. The product of the two norms
is necessary, and is symmetric in \(a,b\): reflection
exchanges the half roles and the integration variable,
and preserves the product. Exact powers of \(\Delta\)
in each norm can be divided out because this pivot
is proved live. The symmetric contact likewise uses its
exact primitive polynomial after removing only powers
of \(\Delta\) and constant integer content.

In \(S=a+b,\ T=ab\) the \(T\)-resultants of \(D\) with the
primitive contact norm and with the primitive support
norm product both have degree 108 in \(S\). Their gcd has
only a degree-4 factor once and a degree-10 factor twice.
For each of these actual coefficient fibers, exact
Euclidean arithmetic gives the common \(T\)-gcd of the
three equations monic and of degree one, dividing
\(\Delta^2\). Thus any genuine layout would have
\(\Delta=0\), contrary to the earlier pivot proof.
No lead-degree exceptions or projected fibers have
been discarded.

The [standalone Python replay](erk11-four-distinct-selected-free-half-triple-exit/replay_four_same_selected_half.py) checks
the symmetric coefficient construction, both resultants,
and both actual exceptional-fiber implications exactly.
This smaller additional elimination is mathematical
with exact SymPy replay; no additional Lean replay is
claimed.
