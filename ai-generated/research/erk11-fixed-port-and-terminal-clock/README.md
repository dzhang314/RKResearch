# Two scoped diagnostics for universal order-eleven stage compression

These are exact algebraic constraints, not a lower bound for arbitrary
twenty-one-stage tableaux.

## Four-stage seed: the last clock is one

Lean theorem: RKResearch.Certified.ERK4TerminalClock.terminal_one.
For every commutative ring and every strictly explicit four-stage tableau
of order at least four, its last row sum is one. No ordered, domain, field,
nontriviality, or distinct-clock hypothesis is needed. The result applies
before rescaling the seed.

Write \(\boldsymbol c=A\boldsymbol 1\), with entries \(0,a,b,c\)
in chronological order, and let \(\boldsymbol w\) be the output weights.
Put \(s=w_3A_{32}+w_4A_{42}\), \(t=w_4A_{43}\),
\(f=A_{32}\), and \(z=w_3\). The corresponding order-three tall,
order-four child-bush, mixed, and tall equations give
\[
 6(as+bt)=1,\quad 12(a^2s+b^2t)=1,\quad
 8(c(as+bt)+(b-c)afz)=1,\quad 24tfa=1.
\]
The bush moments evaluated on \(X(X-a)(X-c)\) give
\(12zb(b-a)(b-c)=3-4(a+c)+6ac\).
The first two displayed equations yield \(12b(b-a)t=1-2a\),
while the first and third give \(24(b-c)afz=3-4c\).
Multiplying, using the tall equation and then the bush identity, yields
\(2a(1-c)=0\). The tall equation makes \(2a\) a unit, so \(c=1\).

This explains why the earlier reverse-seed endpoint and its endpoint
evaluation row have the same clock in the tested paired-row architecture.
It does not say that their incoming rows or full elementary derivatives
coincide, or rule out alternative balancing architectures.

## Fixed scalar ports modulo thirteen

Lean theorem: RKResearch.Certified.ERK11FixedSevenPortsF13.no_weighted_rule.
A degree-ten quadrature with the centered moments of the uniform
distribution on \([-1,1]\) cannot be supported on
\(0,\pm1,\pm1/2,\pm1/3\) and at most three other sites over
\(\mathbf F_{13}\). Signed weights, repeated sites, and zero weights are
allowed. In particular the fixed-port chart cannot give an order-eleven
tableau over \(\mathbb Z[1/11!]\) with only three other scalar sites:
reduce the centered bush moments and the tableau coefficients modulo
thirteen. This restriction does not apply once any fixed port moves.

Modulo thirteen the seven-port hull is \(H(X)=X^7-X^5+4X^3+9X\).
Its means against \(1,X,X^2,X^3\) are \(0,10,0,5\). For three new
sites \(u,v,w\), the mean of \(H(X)(X-u)(X-v)(X-w)\) must vanish,
forcing \(uv+uw+vw=6\). Among the six unused residues
\(\{\pm2,\pm3,\pm5\}\), no three distinct residues satisfy this.
If a candidate coincides with another or with a fixed port, the
quadratic hull for the at most two surviving sites instead yields
\(u+v=0,\ uv=6\), also impossible in this field.

## Lean replay

From ai-generated/lean, with the pinned Mathlib and Lean 4.36.0:

    lake build +RKCert.ReviewedNative.ERK4TerminalClock
    lake build +RKCert.ReviewedNative.ERK11FixedSevenPortsF13

See lean-4.36-audit.txt for the checked axiom output. No other
Lean release is reported as checked.
