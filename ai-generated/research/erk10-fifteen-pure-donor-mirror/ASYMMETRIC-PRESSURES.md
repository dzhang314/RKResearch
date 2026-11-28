# Sufficient short reverse pressures in the asymmetric pure-donor case

The [mirror obstruction](README.md) leaves non-symmetric meshes open.
The following criterion reduces full order ten to a short list of
actual reverse pressure tests in the intended pure-donor triple.
It supports a literal construction search; it does not supply a
new order-ten witness.

Retain the [canonical opening and decoder](../erk10-fifteen-signed-triple-cubic-pressure/ACTUAL-ORDER-ADAPTER.md)
with \(r\) pure through derivative size five, actual high clock
quadrature exact through degree nine, and the literal weighted
transpose \(L\). Write \(Y=1-X\) for reverse polynomials, and let
\(L\boldsymbol1=\boldsymbol y\). Assume the three raw defects
\[
 \boldsymbol u=L\boldsymbol y-\boldsymbol y^{\odot2}/2,\quad
 \boldsymbol g=L\boldsymbol y^{\odot2}-\boldsymbol y^{\odot3}/3,
 \quad\boldsymbol h=L\boldsymbol u
\]
are supported on the physical triple, with zero weighted aggregate.
This includes, but is stronger than, grouped exactness of the first
and second raw defects. Put
\[
 \boldsymbol k=L\boldsymbol y^{\odot3}-\boldsymbol y^{\odot4}/4,
 \qquad
 \boldsymbol m=L\boldsymbol y^{\odot4}-\boldsymbol y^{\odot5}/5.
\]
A vector is said to annihilate polynomials by the weighted pairing
\(\sum_i w_i v_i f(x_i)\), not by unweighted row sums.
Define \(U=X(X-r)\mathcal P_2\) and
\(F=X(X-r)\mathcal P_3\).

**Criterion.** Full ordinary order ten in this chart is equivalent
to the following:
\[
\begin{array}{ll}
 \boldsymbol k,L\boldsymbol g,L\boldsymbol h
       &\text{annihilate }F,\\
 \boldsymbol m,L\boldsymbol k,L^2\boldsymbol g,L^2\boldsymbol h
       &\text{annihilate }U .
\end{array}
\]
In the familiar balanced signed-share setup put
\(\boldsymbol v=\boldsymbol g/2+\boldsymbol h\). There
\(\boldsymbol g=a\boldsymbol u-\boldsymbol v\) and
\(\boldsymbol h=(3\boldsymbol v-a\boldsymbol u)/2\).
The tests then reduce to the two vectors
\(\boldsymbol k,L\boldsymbol v\) on \(F\) and three vectors
\(\boldsymbol m,L\boldsymbol k,L^2\boldsymbol v\) on \(U\).

## From the pressures to true outer words

An outer word is made from high \(B\) (one actual primitive)
and the high clock diagonal \(C\) (one actual same-root leaf
mark). For a word \(W\), write \(W_s\) for the ideal polynomial
word with \(B\) replaced by \(J\) and \(C\) by multiplication
by \(X\), preserving all orders. Its scalar read error is
\[
 \mathcal E_W(f)
    =\sum_i w_i (WEf)_i-\int_0^1 W_s f(X)\,dX
\]
for zero-constant \(f\) within the degree budget. All values
through word length three are identically zero. At length
four the error annihilates \(F\); at length five it annihilates
\(U\). To prove this, move the word onto the output by the
literal weighted transpose. Then operate on the initial
\(\boldsymbol1\) with \(L\) and multiplication by \(x\);
the exact adjoint reverse scalar operations are \(J_Y\) and
multiplication by \(1-Y\). One may use multiplication by
\(Y\) instead since constants give shorter words.
Integration by parts is valid at each step within the same
total scalar degree.

Through length three, new defect terms are precisely linear
combinations of \(\boldsymbol u,\boldsymbol g,\boldsymbol h\)
or their clock marks. These are supported at one clock and
their weighted aggregate vanishes. At length four the only
new defect *directions* modulo those are
\(\boldsymbol k,L\boldsymbol g,L\boldsymbol h\): multiplying
any triple defect by \(Y\) gives its common reverse clock
\(a\) times that defect, and \(L\boldsymbol u=\boldsymbol h\).
At length five the new directions are
\(\boldsymbol m,L\boldsymbol k,L^2\boldsymbol g,L^2\boldsymbol h\)
and the \(Y\)-marks of the length-four directions.
Since \(U+XU=F\), the latter marks annihilate \(U\) by
the length-four tests. This proves the three stated
word-error properties. Conversely true order ten supplies the
word tests through length five on the actual early-null size-five
source space \(U\), and through length four on \(F=U+XU\)
by adding a clock mark to those sources. Each listed vector
is a linear combination of appropriate true word differences,
so the pressures are necessary too.

## Why the exceptional evaluation errors cancel

Length-four errors on \(X\mathcal P_4\) can survive at \(r\):
each is a multiple of evaluation \(f\mapsto f(r)\) because
it annihilates \(F\). A construction needs more than these
projected co-orders alone unless their contributions can be
canceled in the actual tree recursion. Here there is an exact
cancellation using the pure-\(r\) opening row.

Normalize true elementary stage derivatives through size ten
so that pure profiles of order \(n\) equal \(X^{n-1}\), as
in the actual-order adapter. Let \(f_s=\Pi\boldsymbol\Phi_s^{old}
-X^{|s|-1}\), and let \(\boldsymbol\delta_t\) be the actual
high profile minus its pure model. If \(t\) has no immediate
child of size at least five, the high profile is pure.
Otherwise it has just one such child \(s\) (two would give
\(|t|\ge11\)); all other child primitives are pure and
\[
 \boldsymbol\delta_t
  =|s|\, C^{\,|t|-1-|s|}
       \big[(EJ-BE)f_s+B\boldsymbol\delta_s\big].
\]
Here the \(\delta\) recursion is literal at every physical
stage and no tall tree order above ten is used.

Expanding along the unique large-child path gives error terms
of the form \(\alpha W(EJ-BE)f_s\), where
\(|W|=|t|-|s|-1\). Their weighted outputs are
\(\alpha(\mathcal E_W(Jf_s)-\mathcal E_{WB}(f_s))\).
Indeed the two nominal integrals are exactly the same.
Every integrand has degree at most \(|t|-1\le9\).

- For \(|s|\ge7\), both word errors vanish: the longer length
  is at most three.
- For \(|s|=6\), the only possible surviving term is
  \(-\alpha\mathcal E_{WB}(f_s)\) with length four. This is
  an evaluation at \(r\), up to constant. It vanishes if all
  children in \(s\) have size at most four, since that row
  actually pays their primitives. Otherwise \(s=[u]\) with
  a single size-five child \(u\).
- For \(|s|=5\), \(f_s\in U\), so the second word term always
  vanishes. The first can survive only at length four; if the
  word ends in \(C\) it also vanishes by the length-three test
  on \(X J f_s\). Thus survival requires a unary immediate
  parent of size six.

For \(s=[u]\) with \(|u|=5\), the old \(r\) row reads only
\(0,p,q\), where \(\Pi\) interpolates every actual old source
value, and its taps integrate the cubic \(\Pi\boldsymbol\Phi_u^{old}\)
exactly from 0 to \(r\). Thus
\(f_s(r)=5(J f_u)(r)\). The two potential terms are consequently
\(-\alpha\mathcal E_{WB}(f_s)\) from \(s\) and
\(5\alpha\mathcal E_{WB}(Jf_u)\) from \(u\); they cancel by
the same length-four evaluation functional. This completes
the output proof on every tree through ten. The opening
origin contributes no defect (all larger true rooted profiles
vanish there).

This is a mathematical criterion; it does not certify an
actual tableau until the finite pressure equations and all
literal rooted conditions are checked on a specific coefficient
matrix. Its efficient construction coordinates are the
two degree-four raw errors and the three explicit terminal
profiles above, rather than a direct solve in 1205 equations.
