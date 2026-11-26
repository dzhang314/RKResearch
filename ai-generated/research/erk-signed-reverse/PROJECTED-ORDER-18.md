# An exact 63-stage explicit method of order eighteen

The method has coefficients in \(\mathbb U_{18}\coloneqq\mathbb Z[1/18!]\) and has exact order eighteen after any nonzero commutative base change from that ring. It saves one stage relative to the 64-stage short-grid method. The new reverse chart does not recover every ninth-order derivative polynomial. The direction it omits makes no contribution to the rooted conditions of order eighteen.

## The two charts

Use the 22-row forward prefix through size eight from [the earlier order-thirteen construction](../erk-thirteen-moment-splice/ORDER-13-IN-41-STAGES.md). In the centered coordinate \(u=2x-1\), its last four primitive rows are at \(-5,-1/3,1/5,1/3\). Denote its decoder by \(\Pi_F\).

In the reverse direction retain the same first eighteen rows and reflect the four primitive nodes. The reverse coordinate is \(v=2y-1\), so the new four nodes are \(-1/3,1/3,-1/5,5\). With both endpoint reads and the first two moments they give a decoder \(\Pi_{R,8}\) through tree size eight. One more exact scalar read through tree size nine comes from these four primitive stages: the readings divided by \((1-v^2)^2\) determine a cubic, whose integral against the same weight gives the read.

The projected decoder \(\widehat{\Pi}_R\) uses eight observations: the two endpoints, the mean, that weighted read, and four contrasts at the centered nodes \(-1/3,-1/5,-1/2,1/2\). The polynomial these observations omit is
\[
 q(v)\coloneqq(1-v^2)
 \bigl(153v^6-155v^4+35v^2-1-48v(17v^4-10v^2+1)\bigr).
\]
For each new actual clock \(z\), put \(a\coloneqq2/3\) and
\[
 d_z\coloneqq \frac{q(2z-1)}{q(1/3)}.
\]
The denominator \(q(1/3)=-256/729\) is a unit. At clock \(z\) the new incoming coefficient row is
\[
 I_z\Pi_{R,8}-d_z I_a(\Pi_{R,8}-\Pi_{R,7}).
\]
Here \(\Pi_{R,7}\) is the previous decoder padded with zeros, and the old stage at clock \(a\) has incoming row \(I_a\Pi_{R,7}\). The new row has clock \(z\), since the two decoders agree on the constant. At tree size nine the only error can occur at a unary root with an eight-vertex child. On that child the two decoder readings differ by the old scalar residual. The error at the new stage is therefore \(d_z\) times the error at the old stage at \(a\). Subtracting \(d_z\) times that old derivative read realizes the exact scalar contrast \(E_z-d_zE_a\) through tree size nine. This contrast annihilates \(q\).

The decoder fits the eight observations in degree at most seven. Its actual coefficients, along with all 26 reverse rows, are computed by [the exact constructor](construct.py). The leading coefficient of \(q\) is a unit, so this choice of degree selects a unique representative modulo \(q\).

## Why the omitted direction is harmless

Write \(g_t(x)\coloneqq |t|x^{|t|-1}/t!\). Both charts and their first excesses can be checked on just the rooted trees through size nine. The [projection verifier](verify-projection-18.py) checks the following identities on the literal charts:

- Both charts read \(g_t\) exactly when \(|t|\le8\).
- If \(|t|=9\), the reverse reading differs from \(g_t\) by a multiple of \(q(2y-1)\).
- If \(|t|=9\) and \(\rho_t\coloneqq g_t-\Pi_F\boldsymbol\Phi_t(A_F)\), then
  \[
   \int_0^1 q(1-2x)\,(I_x\rho_t)\,dx=0 .
  \]

These tests involve only paid polynomial arithmetic. In particular the zero integrals are identities before any base change. The verifier checks all 486 trees through size nine on each chart, including every tree of size nine, rather than sampling the first-excess space.

In [the signed reverse proof](CONSTRUCTION.md), take \(m=8\) and \(r=9\). An individual reverse receiver has the exact word values through length eight because its outer primitive only uses donor data through size eight. The remaining length-nine read can be inexact only when the forward source has size nine. In that case its discrepancy is a multiple of \(q(1-2x)\). In the weighted source pairing, the corresponding change is the integral of that polynomial times \(I_x\rho_t\), which is zero by the displayed test. The bound of seventeen on polynomial degrees still holds. Also, a tree with two first-excess child errors would have at least nineteen vertices. The signed reverse proof therefore gives every rooted condition through order eighteen.

## The literal tableau and exact order

Use the seventeen reverse sites \(y=(1+v)/2\) at
\[
 v\in\{0,\ \pm1/5,\ \pm1/3,\ \pm1/2,\ \pm2/3,\ \pm1,\ \pm3/2,\ \pm2,\ \pm5\}.
\]
They contain all reverse donor clocks, and their differences are units in \(\mathbb U_{18}\). The interpolatory rule is symmetric and exact through degree seventeen. The usual signed-copy mergers leave one pure row at each site. The forward chart already has a zero row. It also prescribes the earlier output as its mean on arbitrary input, so the pure clock-one row is identical to that earlier row. Thus the count is \(22+26+17-2=63\).

In the [literal tableau](tableau-18.json), the two [order-nineteen defects](witness-18.json) are \(-53127107/2309658624000\) and \(2609/9372963600\). Their denominators are units and their numerators have greatest common divisor one. Thus their linear combinations include one in \(\mathbb U_{18}\), without dividing by nineteen. The arithmetic replay checks both values and also samples 430 rooted conditions on the full tableau. The all-tree proof is the chart argument above, not that sample.
