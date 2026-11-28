# Conditional realization of the remaining eleven-coordinate raw word block

This is a constructive linear reduction of the
[sole ordinary-pair geometry](../erk10-fifteen-split-host-grade-five/README.md),
not an order-ten tableau or an existence theorem for
its rational scalar data. It reconstructs a strict
raw block from a finite set of exact score/cofactor
ratios, leaving only three strict taps free after
a suitable choice of linear row solves.

Use reverse normalization \(0,1,b,c,c,d,e,f,g,h,R\)
and horizon \(H\), so the external origin is \(H\).
All clocks except the repeated \(c\) are distinct
and the ordinary clocks avoid \(0,H\).
Take \(\kappa=c/(2c-4b)\) with the usual nonzero
head denominators. Let \(I\) be the normalized
formal integral on \([0,H]\) and \(J\) the primitive
from zero. Use the earlier one-pair \(P,Q_0,R_0,N\)
polynomials (the actual low-grade profile
coefficients; \(Q_0\) here is not the weighted
host-dirt polynomial).

## Data required by this conditional construction

* The physical scores \(\boldsymbol w\) have exact
  scalar moments through degree nine with an extra
  scalar score at \(H\); \(w_0\ne0,\ w_R=0\).
  Start, for example, with scalar cardinal masses
  on the ten nodes other than \(R\), and split the
  mass of \(c\).
* A vector \(\boldsymbol u\) has \(u_0=0\) and
  the grade-two aggregate on the nine ordinary
  nodes is \(A(z)/((H-z)F'(z))\), where \(F\) is
  their monic product and \(A\) is nonzero affine
  (degree at most one). This is exactly the
  positive moment kill through degree seven.
  Require \(u_1,u_b,u_d,u_e\ne0\).
* The two physical \((w,u)\) restrictions at the
  pair \(c\) are independent, and the first \(c\)
  row has nonzero \(u\) and the actual first-\(c\)
  ratio \(L_c\) of the
  [paid head](../erk10-five-opening-nine-label-one-pair/README.md#leaking-grade-two-normalized-first-three-interiors).
  Given pooled \(W_c,U_c\), this is possible
  whenever \(W_c\ne L_c U_c\): choose any
  first \(u\ne0\), set its weight to \(L_c u\),
  and let the second supply the two remainders.
* The four singleton ratios \(w_z/u_z\) at
  \(z=1,b,d,e\) are \(N(z)/(z^2(z-c))\).
  Take \(e\) from the exact rational Möbius
  gate of the grade-five note.
* Define \(\boldsymbol L,\boldsymbol Z,\boldsymbol G_*\)
  and \(P_Z\) as in the terminal and grade-five
  sections. Let \(Q_Z\) be the cubic with
  \(Q_Z(c)=0\) and \(Q_Z(z)=-(w_z/u_z)P_Z(z)\)
  for \(z=1,b,d\).
  Require the actual scalar equation
  \(w_f P_Z(f)+u_f Q_Z(f)=0\) and \(Z_f\ne0\).
  No rank or score guard at \(g,h\) is needed
  for the following strict row realization.

All these conditions are necessary in the actual
split-host ordinary-pair survivor. They do not yet
impose all its nonlinear conditions; in particular
a raw realization is not being substituted for
an original five-opening tableau.

## Specify the adjoint action on eight actual vectors

First define the adjoint map on
\(\mathcal H_3=\boldsymbol w{\cal P}_3+
\boldsymbol u{\cal P}_1\) by the six literal
primitive equations of the paid head:
\[
\begin{aligned}
T(\boldsymbol w)&=Y\boldsymbol w,&
T(Y\boldsymbol w)&=\boldsymbol w Y^2/2+\boldsymbol u,\\
T(Y^2\boldsymbol w)&=\boldsymbol w Y^3/3+P\boldsymbol u,&
T(Y^3\boldsymbol w)&=\boldsymbol w Y^4/4+R_0\boldsymbol u,\\
T(\boldsymbol u)&=\kappa(Y-1)\boldsymbol u,&
T(Y\boldsymbol u)&=Q_0\boldsymbol u .
\end{aligned}
\]
Here polynomial multiplication of vectors is
componentwise. Extend to
\(\mathcal H_4=\boldsymbol w{\cal P}_4+
\boldsymbol u{\cal P}_2\) by
\[
\begin{split}
 T(\boldsymbol Z)&=\boldsymbol w P_Z+\boldsymbol u Q_Z,\\
 4T(\boldsymbol G_*)&=(Y-d)\boldsymbol Z-T(\boldsymbol Z).
\end{split}
\]
These two extra input directions are independent
modulo \(\mathcal H_3\): their top coefficients
in \((\boldsymbol wY^4,\boldsymbol uY^2)\)
are \((1,-N_1),(1,2-c)\), with
\(N_1+2-c=-c^2/(2b-c)\ne0\).
The checked scalar identity
\(4T(\boldsymbol L)=\boldsymbol Z\) already
holds on \(\mathcal H_3\) by expanding its six
equations; no hypothesized strict \(K\) is
needed for this algebra.

The four ratios at \(1,b,d,e\) and the Möbius
gate give \(T(\boldsymbol Z)=0\) there:
the defining polynomial
\(N P_3+Y(Y-c)Q_2\) from the grade-five proof
has the first three roots \(1,b,d\), and its
nonzero value at \(0\) determines the fourth
via its value at \(c\). Comparing those values
gives precisely the displayed formula for \(e\).
It has \(\deg\le4\), and the guards ensure
the fourth root is finite and distinct.
The outputs \(T(\boldsymbol Z),T(\boldsymbol G_*)\)
both vanish on the first seven rows.

## Strict row realization

A row is a linear functional on preceding
coordinates. Work in the declared reverse order.

1. On the first rows \(0,1,b,c\), the known literal
   low-grade head equations give the required causal
   taps on the five positive/defect columns of
   \(\mathcal H_3\). A remaining endpoint tap
   supplies \(T(\boldsymbol w)=Y\boldsymbol w\)
   because its \(w_0\) is nonzero, while all
   five other inputs vanish at that endpoint.
   The inputs and outputs \(\boldsymbol Z,\boldsymbol G_*\)
   are zero here, so impose nothing extra.
2. At the second copy of \(c\), a scalar multiple
   of the first-\(c\) solution realizes the wanted
   \(u\) with reference weight \(L_c u\).
   To vary the weight independently, change the
   three earlier taps on \(\boldsymbol u\) at \(1,b,c\)
   in the direction \(v=(c-b,1-c,b-1)\), which
   kills both defect moment rows. The exact
   audited scalar read ratios of this direction are
   \[
    \sum v_i L_i Y_i^2=\frac{2c}{3}\sum v_i L_iY_i,
    \qquad
    \sum v_i L_i Y_i^3=\frac{c^2}{2}\sum v_i L_iY_i ,
   \]
   with the rightmost first read nonzero by the
   paid head factors. Thus rescale it to realize
   any desired change of weight. The three physical
   donor \(u_i\)'s are nonzero, so converting the
   weighted taps back to matrix coefficients is legal.
   Again the endpoint tap freely adjusts the
   constant-weight equation.
3. The restriction of \(\mathcal H_3\) to the first
   six rows is injective. Indeed a vanishing pair
   observer has \(p_3=Y(Y-c)p_1\) and
   \(q_1=(Y-c)q_0\) for polynomials \(p_1,q_0\) of
   degrees at most one and zero, respectively,
   from the live endpoint and physical pair
   independence. At \(1,b,d\) the ratio forces
   \(N p_1+Y(Y-c)q_0\) to vanish at three sites.
   This quadratic is zero. Evaluate at \(0,c\),
   where \(N\ne0\) at both, to conclude \(p_1=0\),
   then \(q_0=0\). Thus on the first five rows
   its kernel is the line of \(\boldsymbol L\),
   which is nonzero at \(d\). The needed \(d\)-row
   output kills this remaining input direction
   because \(4T(\boldsymbol L)_d=Z_d=0\).
   This realizes \(T\) at \(d\) from preceding
   rows, also respecting the two vanishing extra
   directions.
4. At \(e\) the first-six restriction of
   \(\mathcal H_4\) has rank six (by the
   \(\mathcal H_3\) restriction), with remaining
   kernel \(\langle\boldsymbol Z,\boldsymbol G_*\rangle\).
   The required \(e\)-output kills both.
   At \(f\) the first-seven restriction has rank
   seven: \(G_{*,e}=(e-d)L_e\ne0\) by the exact
   anchor factorization, and \(Z_e=0\).
   Its remaining kernel is \(\boldsymbol Z\);
   the scalar \((w_f,u_f)\) equation earns
   \(T(\boldsymbol Z)_f=0\).
5. Since \(Z_f\ne0\), the first-eight restriction
   of \(\mathcal H_4\) is bijective. Thus all further
   rows admit the required values on all eight
   input vectors, with no additional row-rank
   conditions. One can take a unique \(g\)-row
   solution, then one free \(h\)-tap and two free
   \(R\)-taps under unrestricted linear solves.

This constructs a strictly causal \(K\) with
literal action \(K|_{\mathcal H_4}=T\).
To return to actual time \(x=1-Y/H\), transpose
and reverse the indices, and take \(B=K^T/H\)
in that chronological convention. The forward
mark is the assigned \(x=1-Y/H\). The factor
\(1/H\) converts the normalized \(J\) below to
the ordinary adjoint primitive on the unit
interval; there is no row-sum condition.

## Why the reconstructed raw words are really exact

For every adjoint word of length \(j\le4\),
its \(\boldsymbol w\)-nominal part is the prescribed
scalar polynomial of degree at most \(j\), and
its defect is \(\boldsymbol u\) times a polynomial
of degree at most \(j-2\) (zero for \(j\le1\)).
This follows inductively from the six specified
equations and clock marking. At \(j=5\) one
also allows a scalar multiple of
\(\boldsymbol w C_L\): the two extra transport
values have their correct primitive nominal
parts modulo exactly that Jacobi direction
and \(\boldsymbol u{\cal P}_3\).
The latter parts kill all required positive
forward tests of degrees at most \(9-j\),
by the actual degree-seven aggregate
cofactor for \(\boldsymbol u\).
At grade five the extra Jacobi direction kills
the four positive tests by its exact orthogonality.
The scalar nominal parts match by degree-nine
quadrature and formal integration by parts.
Thus the complete raw short-word budget holds.

The remaining real-tree and old opening gates
are not supplied by this construction.
In particular one must still earn the true
nonlinear host profile and check the full
1,205 rooted order conditions for any candidate.
The absence here of a rational spectrum
meeting the displayed scalar conditions
is not asserted either.

## Replay

    python3 -B audit.py | diff -u exact-audit.txt -

From the overlay or repository root:

    sha256sum -c ai-generated/research/erk10-fifteen-split-host-raw-realization/sources.sha256
