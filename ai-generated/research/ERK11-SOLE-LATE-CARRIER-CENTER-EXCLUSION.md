# Ordered ERK11 central carrier: exclusion when both boundaries are new

**Scope.** Continue [the sole-late-carrier two-front reduction](ERK11-SOLE-LATE-CARRIER-TWO-FRONT.md).
Keep its extra hypothesis that the response at physical stage 13 is zero; removing that hypothesis from the tableau bridge remains under review.
Assume the actual maximal half-clock 17-stage chart has three
quadratic carriers. They are necessarily physical \(2,9,16\).
Assume also that both seventh-stage boundaries (physical 7 and 11)
are genuinely new in the corresponding normalized fronts.
This rules out that subchart over any ordered field. The case of
two total carriers and the three-carrier case with at least one
repeated boundary remain open here. No ordinary stage bound changes.

The companion ERK11SoleLateCenterGate.lean checks the moment
interpolation, exact determinant/cofactor interpolation and a
finite exact Bernstein sign certificate. No full native tableau/order bridge is claimed.

## 1. Three paid crossings produce two plateau equations

Return to the ordinary model variable \(X\). Let \(a\ne0\) be
the left plateau clock, \(b\ne0\) the plateau clock in the reflected
physical variable \(1-X\). The ordinary right plateau clock is
\(1-b\); here \(b\) as a scalar is not the output vector, whose
components are written \(b_i\). The two actual grade-four vectors
\(v_L,v_R\) of the two-front note can be rescaled to models
\[
     p(X)=X^2(X-a)^2,\qquad q(X)=(1-X)^2(1-X-b)^2.
\]
The physical \(v_L\) vanishes through row 7 and at 9; \(v_R\)
vanishes from row 11 onward and at 9. Put \(P=Jp\) and \(Q=\bar Jq\),
with primitives starting at 0 and 1 respectively. The actual
grade-five \(Av_L\) is zero through row 8 and \(A^\star v_R\)
is zero from row 10 onward, so their support intersects only at 9.

Let
\[
 H=\int Pq=\int pQ,\qquad
 C_1=\int XpQ,\qquad B_1=\int XPq,\qquad
 D_j=\int X^j p q \quad (0\le j\le2)
\]
with all integrals over \([0,1]\). The first equality is the
actual primitive adjoint identity. The integral \(H>0\) over
ordered fields: it is the simplex integral of the nonzero
polynomial square \([u(1-v)(u-a)(1-v-b)]^2\) on \(0<u<v<1\).
On its finite degree space the rational simplex Gram is positive
definite over the reals, hence has a rational elimination with
positive pivots, which remains positive over any ordered field.

The paid pair of \(v_L,A^\star v_R\) overlaps only at row 8:
the possible other site 9 is a carrier with \(v_L|_9=0\).
The paid products with and without one clock factor (cost
\(4+5+1=10\)) give \(c_8=C_1/H\).
The reflected pairing of \(Av_L,v_R\) similarly gives \(c_{10}=B_1/H\).
Their mixed pairing with \(Av_L\) or \(A^\star v_R\) is valid
by the order-ten reversal's annihilator at grade five and the
common order-eleven pairing in the preceding note. No square of a
reverse pure grade-five vector is used.

The support of \(v_L,v_R\) itself intersects only at 8 and 10.
Testing their product with \((X-c_8)(X-c_{10})\) pays \(4+4+2=10\).
After eliminating those two clocks the exact equality is
\[
     D_2 H^2 - D_1 H (B_1+C_1) + D_0 B_1 C_1=0.             \tag{1}
\]

For the second equality, write \(N\) for the integer-scaled inverse
Gram of the monomial basis \(1,X,\ldots,X^4\) with weight \(X(1-X)\):
the inverse is \(210N\) as checked in
[the four-carrier mask certificate](ERK11-FOUR-CARRIER-TERMINAL-MASK.md).
Set \(K(x,y)=(1,x,\ldots,x^4)N(1,y,\ldots,y^4)^{\mathsf T}\).
The anchored model evaluation at \(a\) on the left and \(1-b\)
on the right yields inverse anchored-Gram pairing
\(210ab K(a,1-b)\): factor \(X\) from each left model and \(1-X\)
from each right model.

At physical 9 those evaluation rows are multiplied by some
nonzero \(h_L,h_R\). The exact inverse middle Gram diagonal
is consequently \(b_9 h_L h_R(210 ab K(a,1-b))=1\).
The support of \(Av_L,A^\star v_R\) reads only 9. Its mixed
grade-ten pairing gives
\(\int P Q=b_9 h_L h_R P(a)Q(1-b)\).
Eliminate \(b_9h_Lh_R\) with the inverse relation and use the
formal primitives \(P(a)=a^5/30,\ Q(1-b)=b^5/30\).
Dividing only by \(ab\ne0\) gives the second exact equation
\[
           210 K(a,1-b)\int P Q - a^4 b^4/900=0.             \tag{2}
\]

## 2. Symmetric determinant and cofactor constraints

Set \(S=a+b,\ T=ab\). Multiply the left side of (1) by
871363785600000 and of (2) by 19800. In the companion Lean
file these are \(F(S,T)\) and \(E(S,T)\) with coefficient
lists named fa and fb (ascending \(T\), then ascending \(S\)).
Each has total degree at most six in \(S,T\). The two expressions
before the substitution have separate degrees at most six in
\(a,b\). Checking equality on the exact rational \(7\)-by-\(7\)
grid thus fixes every coefficient by interpolation.

Let \(f_i(S),e_i(S)\) denote the \(T\)-coefficients.
The \(6\)-by-\(6\) Bezout matrix \(M(S)\) has entries
\[
 M_{ij}(S)=\sum_{\substack{0\le k\le\min(i,j)\\ i+j+1-k\le6}}
   \bigl(f_{i+j+1-k}e_k-f_k e_{i+j+1-k}\bigr),\quad 0\le i,j\le5.
\]
It is the coefficient array of the polynomial in \(X,Y\)
\((F(S,X)E(S,Y)-E(S,X)F(S,Y))/(X-Y)\).
At a common \(T\)-root it annihilates
\((1,T,T^2,\ldots,T^5)^{\mathsf T}\), even for a drop of specialized
degree. Its determinant \(D\) vanishes.

The companion computes \(D(S)=d_*\,(55S^2-33S+6)^2 R(S)\),
where \(d_*=433933237584000000\) and \(R\) is the signed degree-30
integer polynomial detFactor. The quadratic is positive over
ordered fields because \(220(55S^2-33S+6)=(110S-33)^2+231\).
Hence every real candidate is a root of \(R\).
Let \(a_0,a_1\) be the first two entries of the first column
of \(\operatorname{adj}(M)\), divided by their common
constant \(21696661879200000\). They are pivot0 and pivot1 in Lean.
They are checked by the two specified signed cofactors.
The degree estimate \(\deg M_{ij}\le11-i-j\) bounds the
determinant by degree 36 and the two cofactors by 25 and 26;
the exact \(37\)-point interpolation verifies all three polynomials.

If \(a_0(S)\ne0\) at a common root, that nonzero cofactor
makes the matrix rank exactly five. Its adjugate column and
\((1,T,\ldots,T^5)^{\mathsf T}\) are proportional. Hence
\[
          T=a_1(S)/a_0(S).
\]
We check directly that every real root of \(R\) has
\[
                   a_0(S)\,[S^2 a_0(S)-4a_1(S)]<0.          \tag{3}
\]
This proves the required nonzero cofactor at the same time,
and gives \(S^2-4T<0\), contrary to \((a-b)^2\ge0\).

## 3. Exact sign on every real determinant-root interval

Write \(R_+=-R\) and \(U=a_0(S)(S^2 a_0(S)-4a_1(S))\).
The coefficient lists of \(R_+(-X)\) and \(R_+(2+X)\)
are both strictly positive, so a real root of \(R\)
must be between 0 and 2. The companion checks these signs.

On \([0,2]\) use Bernstein coefficients of \(R_+\) and \(U\).
For a polynomial \(A(X)=\sum_i a_i X^i\) of degree \(n\),
its Bernstein coefficients on this interval, cleared by \(n!\),
are
\[
                b_j=\sum_{i=0}^j a_i 2^i
                          \frac{j!\,(n-i)!}{(j-i)!},
                      \qquad 0\le j\le n.
\]
Indeed \(A(2t)=\sum_j (b_j/n!)\binom nj t^j(1-t)^{n-j}\).
If all coefficients have one strict sign, the polynomial
has that sign on the full closed interval, including endpoints.
Half-interval coefficients are given by the triangular
averages of adjacent coefficients (de Casteljau subdivision).
Keeping each averaging level undivided, then scaling its
output by the remaining power of two, computes the exact same
signs with integers only. Both identities follow by expanding
the binomial basis, so apply over every ordered field.

The checked partition of \([0,2]\) has 14 closed dyadic leaves.
The pair \((h,k)\) denotes the interval
\([2k/2^h,\,2(k+1)/2^h]\). On each of nine leaves the \(R_+\)
coefficients have a single strict sign:
\[
 (2,0),\ (4,7),\ (3,4),\ (4,11),\ (5,26),\
 (6,54),\ (8,220),\ (7,111),\ (3,7).
\]
On the other five leaves all coefficients of \(U\) are strictly
negative:
\[
                    (3,2),\ (4,6),\ (4,10),\ (4,12),\ (8,221).
\]
They form one exact binary subdivision, with no gap. Thus
every real root of \(R\) has \(U<0\), including any potential
partition endpoints. This is (3). No floating-point root
isolation, real completeness or characteristic-zero complex
resultant inference is needed for the real sign.
