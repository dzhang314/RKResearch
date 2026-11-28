# Literal site decomposition in the six-active-pair ERK11 branch

**Scope.** Continue the maximal all-live, half-clock, two-total-carrier
chart (carriers 2 and 16) with both middle boundary clocks new.
Assume the pooled first response vanishes at each active noncarrier
clock, there are exactly six such clocks, and exactly twelve active
rows. This is the six-pair case, not the 13-active case with a triple.
The unconditional deductions below are characteristic zero after the
existing tableau premises. A signature observation uses ordering.
The last section gives a *conditional* order-preserving change of
tableau, not a deletion or an ordinary stage-bound improvement.

Write \(F=\theta r\) for any fixed nonzero scaling of the actual pure
grade-three response; in the present normalization use \(\theta r\).
Let \(x\) range over the six active clocks, with actual pair responses
\(u_x,v_x\ne0\), weighted by \(b_{i_x},b_{j_x}\ne0\) and physical
\(i_x<j_x\). There are three additional dormant noncarrier **slots**,
including both endpoints, not necessarily three new clock labels.
They stay separate in this argument.

## 1. Exact pure response slopes and scalar slots

The first-response pool \(\nu_x=0\) at each active clock.
The five paid moments of \(F^2\) give
\[
                    \mu_x=\sum_{c_i=x}b_iF_i^2=\kappa/D'(x),
               \qquad D(X)=\prod_{\text{active }x}(X-x).
\]
If \(\kappa=0\), every pair has equal responses and opposing weights,
so the only ordinary scalar support would be three dormant sites,
contrary to the ordinary moment floor. Thus every \(\mu_x\ne0\).
At each pair the two responses differ; its scalar pool \(B_x\) and
third-response pool \(\tau_x\) satisfy
\[
          B_xu_xv_x=-\mu_x,\qquad
                   \tau_x=(u_x+v_x)\mu_x .
\]
In particular \(B_x\ne0\). Two paid moments of \(\tau\), at grades
nine and ten, give a polynomial \(U_3\) of degree at most three with
\(u_x+v_x=U_3(x)\) at the six clocks.

On a literal pair every stage vector splits uniquely into one scalar
value (constant on the pair) and a slope \(\rho_x\) times the actual
response \(F\). The weight form in these two directions is
\(\operatorname{diag}(B_x,\mu_x)\), since \(\nu_x=0\).
In particular this is a nondegenerate splitting, even over an
unordered field. There are nine independent scalar slots (six pair
constants and the three dormant sites) and six response slots.
The two carrier rows supply a separate nondegenerate plane, on
which the pure indicator \(s\) is isotropic by \(b(s)=0\).

For a numerical vector \(z\) of actual grade \(j\), \(3\le j\le7\),
the rooted products with \(C^kF,\ 0\le k\le7-j\), give
\(\sum_x x^k\mu_x\rho_x=0\). These products have grade at most
\(3+k+j=10\), and all clock factors are actual. Barycentric
interpolation with the formula for \(\mu_x\) shows that the six
slopes are values of one polynomial of degree at most \(j-3\).
For grades at most two the slope is zero: both noncarrier profiles
are identical on the low clock models and \(s\).
No order or rank is inferred from numerical clock collisions.

In particular subtracting \(P_2(C)F\) from the actual extra pure
grade-five vector \(h\) gives a pure \(h^0\) constant on each
active pair. The same works for the reverse extra \(\bar h\):
the required three products follow from the forward \(E_5\)
annihilator of the reverse pure grade-five space, without paying
a reverse square. The two vectors are zero on carriers because
the first carrier in each orientation has zero pure response and
the paid pairing with \(s\) then kills the other. At their actual
origin they vanish by pure anchoring.

If the two clean plateau rows on a front are active, they form
a full pair with distinct responses. Normalize \(h\) so it is
the coefficient of \(P(a)\) in the anchored left lift, as in
the [earlier two-front calculation](ERK11-SOLE-LATE-CARRIER-TWO-FRONT.md).
Its values at the two plateau rows are \(0,F_5/F_4-1\).
Thus the slope removed at that clock is \(1/F_4\), so the
common resulting value \(h^0\) on both actual stages is \(-1\).
The reverse calculation gives \(\bar h^0=-1\) on the two
right plateau rows whenever both are active. This is a
same-clock literal row identity; no late step is reindexed.

## 2. Measured spaces and actual masks

Let \(\mathcal Q\) be the nine-dimensional scalar slot space with
carrier values zero, and let \(\mathcal R_j\) consist of numerical
noncarrier response profiles \(P(C)F\) of degree at most \(j\),
with carrier values zero. Because \(s\) belongs to \(E_2\),
subtracting \(P(\theta)s\) from a clock polynomial representative
kills both carrier values without changing its model or any
noncarrier value. Thus
\[
 \begin{aligned}
 E_4&=(\mathcal Q_{\deg\le4})\ \oplus\mathcal R_1\oplus\langle s\rangle,\\
 E_5&=(\mathcal Q_{\deg\le5}+\langle h^0\rangle)\
                      \oplus\mathcal R_2\oplus\langle s\rangle,\\
 E_6&=\mathcal Q\oplus\mathcal R_3\oplus\langle s\rangle .
 \end{aligned}
\]
The first two are the known full pure spaces joined to actual
clock polynomial representatives (the six active labels
separate them). The last is exact because the right side
is \(F_4^{\perp_B}\): scalar profiles never pair with response
profiles; response slopes obey the two moments with \(F,CF\);
and the carrier values are equal. The known \(E_6\) rank
is fourteen, so the inclusion is equality. In particular the
direct sum does not collapse the dormant slots at coinciding
clock labels.

There is an actual grade-five vector supported entirely at the
three dormant slots. Fit a degree-five polynomial \(P\) to
\(-h^0_x\) on the six active labels and put
\[
                  T=P(c)+h^0-P(\theta)s .
\]
Its pure correction and model are actual, it is zero on both
carrier rows, and its linear conditions come from the forward
order budget. It is not the zero vector: otherwise \(h^0\)
would be a polynomial in the grade-five quotient, contrary
to its nonzero pure class and grade-five separation.
There is a corresponding reverse-grade-five mask using
\(\bar h^0\) and its six interpolating values. Their mixed
grade-ten product is legitimate by the cross Gram, but
a clock inserted into the norm of either fifth-grade mask
would cost eleven. No use of such a product is made.

Separately
\[
                        F^2-U_3(C)F
\]
is an actual pure grade-six vector, scalar on every active pair
with value \(-u_xv_x\) and zero at all dormant/ carrier rows.
Its ordinary pooled values are exactly \(\mu_x\). This is a
second, genuine scalar response, of grade **six**, not an
extra fifth-grade equality.

Over an ordered field the scalar-slot form on \(\mathcal Q\)
has exactly one or two negative directions. The six response
weights have three of each sign because they are the nonzero
barycentric weights on six distinct real-ordered labels;
the carrier plane adds one of each sign. The finite forward
grade-five form has six positive model directions and a
five-dimensional totally isotropic pure rank, so the original
form has at least eleven positive directions. Thus at most
two scalar-slot signs are negative. At least one is negative
because \(h^0\) is a nonzero isotropic scalar-slot vector
(the actual grade-ten square is paid).
In particular the six pairs cannot all have same-sign
responses: \(B_xu_xv_x=-\mu_x\) would force three negative
scalar pair weights. Also, if the possible scalar support
happens to have only seven distinct labels including
the endpoints, and all four front calibration labels are
nonendpoints, the two-front Jacobi doubling obstruction already
applies. This last statement needs no extra sign assumption.

## 3. Conditional literal reweighting if the earlier response is cubic

There is a further exact algebraic route if the six **earlier**
pair values \(u_x=F_{i_x}\) lie on one polynomial \(U\) of degree
at most three. This does not follow just from the cubic **sum**
\(U_3\) proved above.

At each pair \(i<j\) make a lower triangular linear change of stages
\(S\) that keeps the first row and replaces the second coordinate
by \((b_i z_i+b_j z_j)/B_x\). Leave dormant/ carrier slots unchanged.
Then \(S\mathbf1=\mathbf1\), \(SC=CS\), \(S\) is invertible, and
\(A'=SAS^{-1}\) is strictly lower triangular by literal chronology.
The row \(b'=bS^{-1}\) has zero at each earlier member of a pair
and \(B_x\) at each later member. The transformed response \(SF\)
is supported exactly on the six earlier, zero-output slots.

For actual inputs \(z,w\) of grades \(i,j\) with \(i+j\le10\),
write the preimage error as
\[
     S^{-1}\bigl(S(z\odot w)-(Sz)\odot(Sw)\bigr).
\]
It vanishes if one grade is at most two. Otherwise, at each pair
its only possible nonzero coordinate is the later member and
it is \(v_x(v_x-u_x) P_i(x)P_j(x)\), where \(P_i,P_j\) are the
two response slope polynomials of degrees at most \(i-3,j-3\).
This is the actual pure vector
\[
                [F^2-U(C)F]\,P_i(C)P_j(C)
\]
of grade at most \(i+j\). The ordinary rooted induction now
shows every transformed grade-\(\le10\) tree vector is \(S\) of
an actual old vector with its exact model: unary operations
commute under conjugation, and a product only subtracts the
paid pure preimage error just calculated. Thus the transformed
explicit tableau is also ordinarily exact through order eleven.
The operation gives a concrete zero-output-copy chart for future
analysis, **not** a justified removal of those internal stages.

[The Lean scalar gate](../lean/RKCert/Research/ERK11SixPairSiteGate.lean) checks the weighted pair, constant plateau and
preimage error arithmetic on Lean 4.34.1, 4.35.0, 4.36.0, and 4.37.0-rc1. The rank, grade and chronology bridges are
the mathematical proofs above.
