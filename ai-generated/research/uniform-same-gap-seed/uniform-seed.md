# An exact signed rational seed for the uniform same-gap ladder

There is a rational rule for \(\mathcal I(f)=\int_0^1 f(X)\,dX\)
with **10 distinct contributing sites and exact order 12**, whose
two-shift completion curve has a certified nontorsion infinity
difference. The rule may use signed weights and sites outside
\([0,1]\); this is not an interval-constrained or positive rule.
It starts the fixed-functional same-gap ladder on the actual
uniform moments, not on a freely chosen synthetic functional.

The seed is specified by a short straight-line rational program
and checked directly. It uses no search over rational grids or
floating-point moment matches.

## 1. Start with a confluent Jacobi factor

Use the nonnegative weight \(X(1-X)^4\), whose moment of degree
\(j\) is \((j+1)!\,4!/(j+6)!\). Its monic degree-two orthogonal
polynomial is
\[
        G_0=(X-1/6)(X-1/2)=X^2-\tfrac23X+\tfrac1{12}.
\]
This follows by substituting the four moments in the two
orthogonality equations. Thus the confluent nodal polynomial
\[
        P_0=X(X-1)^4(X-1/6)(X-1/2)
\]
satisfies \(\mathcal I(P_0)=\mathcal I(XP_0)=0\),
\(h_0=\mathcal I(X^2P_0)=1/30240\), and
\[
 \bigl(\mathcal I(P_0/(X-x))\bigr)_{x=0,1/6,1/2,1}
        =(1/252,-1/140,1/252,-1/5040).
\]
These are polynomial cofactor values, not ordinary quadrature
weights at a repeated site. No scalar rule is asserted at this
confluent intermediate stage.

The starting pattern is systematic. For the Jacobi weight
\(X^A(1-X)^B\) with nonnegative integers \(A,B\), the beta moments
give the monic quadratic
\[
 X^2-\frac{2(A+2)}{A+B+4}X+
             \frac{(A+1)(A+2)}{(A+B+3)(A+B+4)} .
\]
Its discriminant is
\(4(A+2)(B+2)/[(A+B+3)(A+B+4)^2]\).
Thus it splits rationally when
\((A+2)(B+2)/(A+B+3)\) is a rational square. The present choice
\(A=1,B=4\) gives \(9/4\) in this test and concentrates all
duplicate occurrences at just one endpoint.

## 2. Remove three occurrences of the repeated endpoint

For a multiset polynomial \(P\) with the two paid shifts, let
\(h=\mathcal I(X^2P)\), \(C_i=\mathcal I(P/(X-i))\) for a
distinct support value \(i\), and choose different values \(u,v\)
with \(h C_u C_v\ne0\). Put
\[
 \ell=v-u,\qquad a=\frac h{C_u\ell^3},\qquad
 b=-\frac h{C_v\ell^3}.
\]
If the following expressions exist and are distinct, replace one
copy each of \(u,v\) by the three sites
\[
 u+\ell\frac{a(b+1)}{a-b},\qquad
 u+\ell\frac{a-b}{a+1},\qquad
 u+\ell\frac{a+1}{b+1}.                                  \tag{1}
\]
The three numbers are the earlier
[two-shift rank-free triple](../two-shift-elliptic-transfer/elliptic-transfer.md)
in normalized coordinates. Their cubic may also be checked
directly: with \(S\) the sum of their physical coordinates,
\(\tau=S-u-v\), and \(B_0=(X-u)(X-v)\), it is
\[
 G_\tau=(X-\tau)B_0+
      \frac h{C_u\ell}(X-v)-\frac h{C_v\ell}(X-u).
\]
The new polynomial \(Q=(P/B_0)G_\tau\) pays the two shifts:
substitute the displayed formula, use
\(\mathcal I(XP/(X-i))=iC_i\), and see the contributions of
the last two terms sum to \(0\) in the first equation and
\(-h\) in the second. Nothing in this calculation requires
\(P\) or its retained factor \(P/B_0\) to be squarefree.
Nonzero cofactors and the next unpaid moment are checked
separately at each step.

Starting with \(P_0\), take the three named pairs, in order,
\[
          (1/2,1),\qquad(1/6,1),\qquad(0,1).
\]
At each step recompute \(h,C_u,C_v\) from the current
polynomial, and apply (1). This is an exact specification
of the final rational sites without listing long numerators.
The first triple is \((25/57,-3/32,51/70)\), and the second
is
\[
       (9777623/76372175,\ 163552904863/878981491848,\
          875570293937/858514304382).
\]
The [checker](verify-uniform-seed.py) independently multiplies
the polynomials, verifies the partial-fraction cubic, confirms all
cofactors nonzero and both paid shifts, and checks the next defect
at every step. The triples avoid every retained value, so
the multiplicity at 1 falls \(4\to3\to2\to1\); the final
degree-ten polynomial \(P_3\) is squarefree.

For each final site \(x\), set its rational weight to
\(\mathcal I(P_3/(X-x))/P_3'(x)\). These are the actual
nonzero Lagrange weights. Polynomial division by \(P_3\) then
proves exactness for degrees \(0,\dots,11\) using the two paid
shifts, and the nonzero \(\mathcal I(X^2P_3)\) is the first
defect (integral minus rule), at degree 12. The checker
also evaluates all those scalar rule moments directly.

## 3. A small nontorsion certificate on the actual seed

Take the distinct final sites \((25/57,51/70)\) as the pair.
Use their exact cofactors and defect in the definitions of \(a,b\).
The smoothness test \((a+b-1)^3+27ab\ne0\) holds. In the
[explicit Weierstrass model](../two-shift-elliptic-transfer/elliptic-transfer.md)
the three coefficients after the leading \(X^3\) and the
coordinates of \(D\) are integral at 23. The model and point
reduce to
\[
       Y^2=X^3+X^2+10X+6,\qquad D=(0,12)\quad\bmod23,
\]
with cubic discriminant \(2\bmod23\). The exact affine
chord-and-tangent chain is well-defined through \([12]D\):
every required denominator is a unit mod 23, so the same
rational formulas have affine values upstairs. In particular
\[
   [6]D=(3,16),\quad [9]D=(11,21),\quad [12]D=(11,2)
                    \qquad\bmod23.
\]
Thus none is the identity over the rationals. The model has
rational 3-torsion, so Mazur's theorem makes this an exact
certificate that \(D\) is nontorsion. No height or analytic
rank estimate is used.

## 4. Consequence and limits

The [fixed-functional ladder](../same-gap-seed-ladder/seed-ladder.md)
can therefore start at width 10 and exact order 12 for the
uniform interval functional. Its hypotheses are genuinely met
on an ordinary squarefree scalar rule. It gives, abstractly,
an exact signed rational rule on \(p-2\) distinct contributing
sites at each order \(p\ge12\), allowing sites anywhere on the
rational line. This is a support upper bound in that domain,
not a minimality claim, a finite order-20 coefficient table,
a prescribed-interval or positive quadrature, or an RK stage
bound. The explicit exact replay only constructs the order-12
seed, not a higher-order tableau or rule.

Run `python3 verify-uniform-seed.py`
([expected output](exact-check.txt)) for the independent
stdlib rational-arithmetic verification.
