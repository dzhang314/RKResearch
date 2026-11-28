# A finite two-neighbour pencil for the ordered four-carrier ERK11 middle

Continue the maximal all-live half-clock branch with four carriers and the
[actual six–five–six middle calculation](ERK11-FOUR-CARRIER-MIDDLE-GATES.md).
Thus both actual directions have ordinary order eleven and the same
grade-five space, the four carriers are precisely physical 2,5,13,16 at
the one clock \(\theta\ne0,1\), and \(M=\{7,8,9,10,11\}\) is the
noncarrier middle. Work over an **ordered field** after these premises.
In particular the two middle boundary clocks are new, and all four
internal adjacent edges are live by that calculation. This note does
not apply to zero weights or to the different terminal branches.

**Result.** After fixing the two sixth-clock fronts and \(\theta\),
physical clocks 8 and 10 each have at most **two** possibilities.
Their combination must pass an additional bidegree-\((3,3)\) inverse
Gram test. Given those neighbours, there is an exact center-clock
polynomial of degree at most seven with six known distinct roots;
unless it vanishes identically, at most one genuinely new clock is
possible at physical 9. In the identically-zero case a separate
scalar equation fixes the eighth clock uniquely. This is a smaller
finite residual chart conditional on the continuous front parameters,
not a universal 17-stage impossibility.

## 1. Genuine first and second middle functionals

Use the exact grade-five left-zero and right-zero lifts \(L,R\) and
anchor polynomials of the
[middle gate](ERK11-FOUR-CARRIER-MIDDLE-GATES.md).
They vanish on all four carriers. In physical model variables
take bases \(X^k,(1-X)^k\), \(1\le k\le5\), respectively.
Write \(L_i,R_i\) for their evaluation rows at middle physical site \(i\).
The actual grade \(5+5=10\) product gives
\[
              L^{\mathsf T} B_M R=H,\qquad
            H_{k\ell}=k!\ell!/(k+\ell+1)! .
\]
In particular \(L,R\) are invertible, with
\[
                       R H^{-1} L^{\mathsf T}=B_M^{-1}.
\]
Consequently for distinct middle sites \(i,j\),
\(L_i N R_j^{\mathsf T}=0\), where \(N=H^{-1}/210\).
The earlier
[opposite corner](ERK11-MIDDLE-INVERSE-CORNER.md)
computed this for \(i=7,j=11\), giving their exact
two-point Hermite functionals. Here we use the other corners,
without presuming the first/last middle rows are generic.

Normalize the left clock by \(\theta\) and the left response by
the same scalar. Put \(z=c_6/\theta\), and
\[
        x=(7z-8)/(6z-7)=c_7/\theta,\qquad u=c_8/\theta.
\]
The three clean nonorigin calibration nodes on the left are
\(1/2,1,z\) with respective response values
\(1/8,-1/2,z^2(1-z)\). These are all nonzero and the nodes
are distinct. The local \(P_0=X^2(X-1)^2\) has a genuine
grade-four left-zero lift vanishing at row 7. Thus \(L(JP_0)\)
is also zero at row 8 by strictness: its only prior middle
donor could be site 7, where \(L(P_0)\) is zero. Primitives
in these normalized variables differ from physical primitives
only by a nonzero scalar. No extra root is being paid.

For normalized degree-\(\le5\) anchored \(P\), write
\[
       L(P)_i=P(v_i)+f_i T_P(v_i),\qquad v_i=c_i/\theta,
\]
where \(T_P\) is the quadratic interpolant with values
\(-P(t_j)/f_j\) at the three calibration sites.
For \(A_0=JP_0=X^3(6X^2-15X+10)/30\), the exact equation
\(L(A_0)_i=0\) is
\[
                       D(v,z)f+J_0(v,z)=0,                    \tag{1}
\]
where the two polynomials are
\[
\begin{aligned}
 D(v,z)&=(6z^2-24z+20)v^2+(3z^2+12z-18)v-7z^2+8z,\\
 J_0(v,z)&=v^3(6v^2-15v+10)(z-1)^2.
\end{aligned}
\]
Thus \(T_{A_0}(v)=D(v,z)/(30(z-1)^2)\).
The common positive quadratic is
\(6v^2-15v+10=6(v-\tfrac54)^2+\tfrac58\).
For \(i=8\), \(v=0\) would force \(f=0\) by
\(D(0,z)=z(8-7z)\ne0\), making its entire \(L\) row zero.
A clock at \(1/2,1,z\) forces the matching old response from
\(L(A_0)_8=0\) and the nonzero primitive at that node,
again making the row zero. Finally \(u=x\) forces \(f_8=f_7\):
at \(x\ne0\) the nonzero primitive and (1) give \(D(x,z)\ne0\),
so equal clock gives equal response. The two numerical
\(L\) rows would coincide. All are prohibited by invertibility.
Consequently the second middle clock obeys
\[
            u\notin\{0,1/2,1,z,x\},\qquad
            D(u,z)\ne0,\qquad f_8=-J_0(u,z)/D(u,z)\ne0.       \tag{2}
\]

## 2. The cubic row pencil and the quadratic residual choices

For a normalized clock \(v\) and response satisfying (1), with
\(v\notin\{0,1/2,1,z\}\), the actual ordinary \(L\)-evaluation row
is a nonzero scalar multiple of the **cubic pencil**
\[
         U_\theta(v,z)=(w_1,\ \theta w_2,\ \theta^2 w_3,\
                                     \theta^3 w_4,\ \theta^4 w_5),
\]
where
\[
\begin{aligned}
 w_1={}&(36z^2-48z+6)v^3+(-66z^2+90z-15)v^2
                     +(18z^2-29z+10)v+7z^2-8z,\\
 w_2={}& zv\big((24z-30)v^2+(51-42z)v+7z-8\big),\\
 w_3={}&3zv^2\big((6z-8)v-11z+14\big),\\
 w_4={}&2zv^2\big((6z-9)v-15z+20\big),\\
 w_5={}&-5zv^2(v+4z-6).
\end{aligned}
\]
Before inserting the physical powers the common normalized scalar
is \(v(v-1)(v-z)(2v-1)/(zD(v,z))\).
One check is to multiply the five interpolation numerators by
\(D\) and use (1); the residual common factor is
\((z-1)^2v(v-1)(v-z)(2v-1)\) in the denominator-cleared
interpolants \(\mathrm{den}=z(z-1)^2\).
The Lean companion verifies all five interpolation fits, the
unary numerator and the five factorizations.
This applies both to \(L_7\) (\(v=x\)) and \(L_8\) (\(v=u\)).
It is the actual grade-five row, not a hypothetical derivative
at a new stage.

The coefficient rows of \(v^0,\ldots,v^3\) in \(w_1,\ldots,w_5\)
have rank four. The minor of their first four columns is
\[
                  6z^4(7z-8)^2(24z^2-57z+34).
\]
The last factor is \(24(z-19/16)^2+5/32>0\), and the
other guards hold. Thus the row span of the pencil is precisely
the four-dimensional hyperplane annihilating the ordinary
\(JP_0\) model on the left (with \(P_0=X^2(X-\theta)^2\) in
physical variables).

Let \(\beta=1-\theta\), \(t=(1-c_{12})/\beta\),
and \(y=(7t-8)/(6t-7)=(1-c_{11})/\beta\).
Right reflection gives \(R_{11}\) proportional to
\(U_\beta(y,t)\), and \(R_{10}\) proportional to
\(U_\beta(v,t)\) for \(v=(1-c_{10})/\beta\)
with exactly the reflected guards of (2).
In particular the prospective neighbor \(u\) satisfies the
ordinary cubic polynomial equation
\[
              K_{\rm left}(u):=
                       U_\theta(u,z) N U_\beta(y,t)^{\mathsf T}=0 . \tag{3}
\]
It is **not the zero polynomial**. Otherwise \(N R_{11}^{\mathsf T}\)
would lie on the unique annihilator line of the four coefficient
rows, hence be proportional to the \(JP_0\) coefficient column.
That would make \(R_{11}(Q)\) a nonzero scalar multiple of
\(\int (JP_0) Q\) on the entire actual anchored right model space.
But \(R_{11}(Q_0)=0\) for \(Q_0=(1-X)^2(X-\theta)^2\), while
\[
  \int_0^1 (JP_0)Q_0
   =\frac{560(\theta-\tfrac12)^4+80(\theta-\tfrac12)^2+1}{100800}
   \ne0 .
\]
This uses ordered positivity only in the final nonvanishing
and the earlier discriminant/clock guards.

The known \(x\) at row 7 is a root of (3) by the actual
\(7,11\) inverse corner; \(u\ne x\), so \(K_{\rm left}/(X-x)\)
is a **nonzero polynomial of degree at most two** that must
vanish at \(u\). The exact reflected argument says
\[
         \frac{U_\theta(x,z)N U_\beta(Y,t)^{\mathsf T}}{Y-y}
\]
is nonzero of degree at most two, and vanishes at \(v\).
Thus there are at most four pairs to check once the fronts are
fixed, and every pair must additionally obey the actual corner
\[
                         U_\theta(u,z)N U_\beta(v,t)^{\mathsf T}=0.
\]
This is a bidegree-\((3,3)\) test. Equivalently, with actual degrees
at most two in the two charged quotients, their iterated resultant
against this bidegree test must vanish if both have a permitted
root. No irreducibility or generic leading coefficient is assumed.

## 3. A center pencil with six known roots

There is a further paid constraint without adding a sixth
charge moment. Work again in the left normalized model variable.
Let \(P_1=X(X-1)(X-\tfrac12)(X-z)\) and take the three
grade-five models
\[
        P_A=J P_0,\qquad
        P_B=(X-u)P_0,\qquad
        P_C=(X-x)P_1-kP_0,\quad
        k=(u-x)L(P_1)_8/L(P_0)_8.
\]
The denominator is live by the already proved unique middle
path. These three genuine left-zero lifts vanish at both
7 and 8: for the middle two use their indicated clock factors
and the literal scalar \(k\). They are independent model
polynomials: their orders at the model origin are respectively
3, 2, and 1, with the last derivative \(xz/2\ne0\).
The right lift \(R(\bar J Q_0)=A^\star R(Q_0)\) vanishes
from physical 10 onward and is nonzero at 9 by the live
adjacent middle path. All these products pay \(5+5=10\).
As a result the scalar functional
\[
                    I(P)=\int_0^1 P(X/\theta)\,\bar J Q_0(X)\,dX
\]
reads only **row 9** on the three selected left models.
Moreover \(I(P_A)\ne0\): up to a nonzero scaling it is
\(\int J^2P_0 Q_0\), the positive inner-path integral
already checked in the middle gate.

Set
\[
 \widetilde P_B=P_B-\frac{I(P_B)}{I(P_A)}P_A,\qquad
 \widetilde P_C=P_C-\frac{I(P_C)}{I(P_A)}P_A .
\]
Their literal left evaluations vanish at row 9.
Eliminating its (single) response value from the two equations
yields the degree-at-most-seven necessary polynomial
\[
    D_{\rm cen}(X)=\widetilde P_B(X)T_{\widetilde P_C}(X)
                 -\widetilde P_C(X)T_{\widetilde P_B}(X)=0
                        \quad\text{at }X=c_9/\theta .
\]
It already vanishes at the **six distinct** nodes
\(0,1/2,1,z,x,u\): the first from anchoring, the next three
from the defining interpolation, the last two from their
actual equal row-zero readings. If not identically zero,
there is at most one further distinct clock possibility.
If either correcting quadratic is nonzero at a candidate clock,
the response there is then fixed by that row equation.

Even if the center polynomial is identically zero, it gives an
additional exact front relation. Its derivative at zero is
\(-\widetilde P_C'(0)T_{\widetilde P_B}(0)\), and
\(\widetilde P_C'(0)=xz/2\ne0\).
Now \(T_{P_B}(0)=u\) and
\(T_{P_A}(0)=D(0,z)/(30(z-1)^2)=:\Gamma\ne0\),
by the actual \(P_0\) interpolant \(X-1\).
Hence the identically-zero case requires
\[
               \big(I(P_A)+\Gamma I(P_0)\big)\,u
                                   =\Gamma I(XP_0).
\]
The right side is nonzero in an ordered field:
\(I(XP_0)\) has the nonzero sign of \(1/\theta\) by its
literal polynomial integral (or after real closure), and
\(\Gamma\ne0\). Thus this exceptional case fixes \(u\)
uniquely in terms of the original front parameters.
The reflected center constraint is also required;
we do not assume this exception actually occurs.

Once actual middle clocks and response values in both directions
are supplied, the two evaluation matrices, hence \(B_M\), are
fixed by the exact inverse identity. The literal strict
middle matrix is also unique from the two left and two right
grade-four advances: the left head fixes entries
\((2,1),(3,1),(3,2)\) in local middle indices, via the
independent first-two \(L(P_0),L(P_1)\) values. The right
head fixes \((5,4),(5,3),(4,3)\) by the analogous independent
last two and actual nonzero weights. The remaining entries of
rows 4 and 5 are their columns 1 and 2, uniquely fixed by the
same left two-by-two fit. All other advance equations remain
consistency tests. This is a determination of the literal
middle block conditional on the measured data, not a claim
that any such data fit the full RK tableau.

[ERK11NeighbourPencilGate.lean](ERK11NeighbourPencilGate.lean)
verifies the interpolation, cubic factorization and minor
identities and the exact positive numerator comparisons.
The original inverse Gram, true root payment, cutoff
and polynomial root counts are the arguments above.
