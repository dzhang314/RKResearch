# Alpha-two live cubic: partial exclusions and correction

## Correction: the general live-cubic exclusion is withdrawn

The general exclusion asserted in the original report below is **not established**. The grade-seven replay computes its numerator and the other columns in forward coordinates, using the reflected carrier `cx = refl(c)`, but forms their pseudo-remainders modulo the unreflected carrier `c`. The argument requires reduction modulo `cx`. The archived `clock.py` and its historical output therefore do not certify an exclusion of the regular and singular cubic-profile towers. They are retained here to make the error and the research history reproducible, not as validated evidence.

The separate lost-quartic-coefficient argument in §2 and the finite cases checked by `finite.py` use only the actual reverse eliminant and do not depend on `seventh`. The earlier quadratic-carrier and zero-multiplier cubic exclusions are unaffected. This reopens both general nonzero-multiplier cubic counts from the original report. The [separate corrected adjacent proof](../dirk11-thirteen-invisible-six-alpha-two-live-cubic-beta-zero/README.md) restores only the count with no middle ghost, leaving the other general count open. The real stage interval remains **13–14**. The adjacent alpha-one zero-multiplier arithmetic uses the shared tower representation, not this erroneous grade-seven computation.

## Archived original report (general conclusion superseded)

**Result.** The normalized no-late invisible-six thirteen-stage
DIRK11 chart has no cubic carrier with live reciprocal multiplier
\(\tau\ne0\) and \(\alpha=2\). This excludes both
\((\alpha,\beta,\gamma)=(2,0,4),(2,1,3)\), over any
characteristic-zero field, with the original normalized hypotheses.
No ordering of the scalars is used. In particular this does not
establish a stronger general thirteen-stage exclusion: the unrestricted
real stage interval remains **13–14**.

Use the actual signed normalized hypotheses of the
[early ghost proof](../dirk11-thirteen-invisible-six-alpha1-five-zero/README.md),
the [early profile census](../dirk11-thirteen-invisible-six-early-profile-census/README.md),
and the [two-ghost debit](../dirk11-thirteen-invisible-six-alpha-two-debit/README.md).
The literal reverse chronology is
\(T,v,u,w,z_1,z_2,V,[\beta],B,[\gamma],O\).
The six individually live ghost clocks are distinct from one another;
they all have weight zero. The five nonendpoint ordinary clocks
are distinct, nonzero, different from 1, and weighted. **We do not
assume numerical ghost–ordinary disjointness.** The clock notation
is reverse \(Y=1-c\) with \(N=A^{\mathsf T}\) in literal reverse
order; \(W(P)=b_{\rm wt}P(Y)\). In forward coordinates write
\(a=1-V,\ b=1-B\) and \(\phi=U(c)-g\).
The cubic \(U\) is live at all six nonterminal clean sites because
the reciprocal identity there is live. Its reflected polynomial
is denoted \(U_r(Y)=U(1-Y)\).
The proved alpha-two debit gives \(d_V=0\).

## 1. Two actual reverse reads and elimination without a pivot

Set \(R=Y^3+c_2Y^2+c_1Y+c_0\), the old hull of \(v,u,w\),
and \(P_0=YR\). Let \(I\) be the polynomial primitive from zero.
Choose a common gauge in which \(k(Y)=G/b_{\rm wt}\) on regular
sites satisfies \(k(Y) U_r(Y)=YJ_4(Y)\); on the three old clocks,
\(k(Y)=Ym(Y)\) for the old interpolant \(m\) of degree at most
two. The values of \(m\) on those clocks are live.
Define the **unreduced** polynomials
\[
 L_0=IP_0/Y,\qquad L_1=I(YP_0)/Y
\]
and by remainders in the old cubic algebra,
\[
 M=(J_4/m)\bmod R,\quad
 W_0=(L_0/m)\bmod R,\quad Q_0=(L_1/m)\bmod R.
\]
The quadratic \(W_0\) has exactly the two distinct first-gap
ghost roots. Write \(w_2\ne0\) for its leader. Since \(U_r\)
agrees with \(M\) on all old clocks,
\(U_r=M+tR\) for a live \(t\).
The exact polynomial quotients
\[
 D_4=(L_0 M-W_0 J_4)/R,\qquad
 D_5=(L_1 M-Q_0 J_4)/R
\]
exist by the defining old residues.

The quartic primitive difference \(W(IP_0)-NW(P_0)\)
is the actual reverse row \(G W_0(Y)\). Its weighted inputs
through the old rows and two ghosts vanish. At \(V\) the diagonal
is zero, so this difference is its primitive output.
Cancelling the live \(V,R(V),U_r(V)\) where appropriate gives
\[
 D_4(V)+t L_0(V)=0.                                                \tag{1}
\]
The actual quintic primitive difference for \(YP_0\) is
\(GQ+\theta H_{\rm bary}\), with \(\deg Q\le3\), using the
grade-six space \(Z_6\). Because \(H_{\rm bary}/G\) equals
\(U_r\) on all five regular sites, old reduction yields
\(Q=Q_0-\theta U_r+\mu R\). At \(V\) the two \(\theta\)
terms cancel and \(d_V=0\), so
\[
 \mu J_4(V)=D_5(V)+t L_1(V).
\]
At both first ghosts the weighted inputs and output weight
vanish, as does \(H_{\rm bary}\). Thus the evaluations of
\(Q_0+\mu R\) agree with those of \(\theta U_r\) at these
two distinct roots of \(W_0\). The two **linear remainders**
have zero two-coordinate determinant, allowing also
\(\theta=0\) or an identically zero remainder.

For the computation, write \(q,m_*,r\) for the length-two
remainders of \(Q_0,M,R\), multiplied respectively by
\(w_2,w_2,w_2^2\). With \(j=J_4(V)\) and
\(\wedge\) the ascending two-coordinate determinant, the
cleared quintic is exactly
\[
 J_0+tJ_1=0,\qquad
 \begin{split}
 J_0&=j w_2(q\wedge m_*)+D_5(V)(r\wedge m_*),\\
 J_1&=j(q\wedge r)+L_1(V)(r\wedge m_*).
 \end{split}
\]
Subtracting the multiple of (1) eliminates \(t\) **without**
a division by \(J_1\) or by \(L_0(V)\):
\[
 E=L_0(V)J_0-D_4(V)J_1=0.                                      \tag{2}
\]

## 2. The lost quartic coefficient is an exact contact contradiction

If \(L_0(V)=0\), the literal quartic at \(V\) gives
\(W_0(V)=0\) since \(k(V)\ne0\). Thus \(V\) equals one
of the two first ghost clocks numerically, even though it
does not coincide physically. Use instead the **actual**
degree-five input \(P_5=(Y-V)P_0\). All its inclusive
weighted inputs through \(V\) vanish. Its primitive error
has shape \(GQ_5+\eta H_{\rm bary}\) and \(Q_5\) vanishes
at both first ghost clocks. Hence **\(Q_5(V)=0\)** by this
numerical contact, even though \(G_V\) is live. Consequently
\[
 \eta=IP_5(V)/(VJ_4(V)).
\]
Since \(W_0\mid Q_5\), its old residue is in the span of
\(W_0,YW_0\). Cancelling the common old multiplication by
\(m^{-1}\) gives
\[
 \det\big(L_0,\;YL_0,\;IP_5/Y-\eta J_4\big)\bmod R=0,
\]
where the determinant is on the three ascending old
coefficients after taking each remainder. This is precisely
the verified degree-24 exact ordinary field obstruction of
[the earlier debit, Section 3](../dirk11-thirteen-invisible-six-alpha-two-debit/README.md#3-both-tau0-cubic-counts);
the scalar replay there only uses \(IP_0(V)=0\) and the
displayed \(\eta\). No old-profile case split is needed
for this contact, and no coefficient of a cubic carrier
is divided here.

## 3. An independent, actual grade-seven condition

Now \(L_0(V)\ne0\). The cleared cubic
\[
 \widetilde U_r=L_0(V)M-D_4(V)R
\]
is \(L_0(V)U_r\) by (1), so its leader is live; let
\(\widetilde U=\widetilde U_r(1-X)\).
All the forward mask identities below are homogeneous in
the carrier, so we may take \(U=\widetilde U\) for this
calculation, scaling \(\phi\) and the defect head together.

Take the actual grade-six column
\(\psi=C(C-a)(C-b)\phi\). In both chronologies **all**
inclusive donors to the six ghosts or to \(a,b\) are
ghosts, the origin, or \(a,b\). All those coordinates of
\(\psi\) vanish. Set \(F=I[X(X-a)(X-b)U]\) and
\(H=XJ_4(X)\). The established actual masked-primitive
budget gives \(A\psi-F(c)\in F_7\), with
\(F_7=g\mathcal P_4+(e_T-H_T)\mathcal P_1\)
as in [the grade-seven ingress](../dirk11-thirteen-invisible-six-constant-exclusion/README.md#1-actual-grade-seven-head-and-two-forward-clean-samples).
Thus \(F-HL+UQ_4\) vanishes on the six distinct ghost
clocks, and is a polynomial of degree at most seven.
Here the affine \(L\) is fixed at \(a,b\) by
\(L(a)=F(a)/H(a), L(b)=F(b)/H(b)\) because both clean reads
vanish; the denominators are live. In particular
\(F-HL+UQ_4=R_6 L'\) where \(R_6\) is the monic
six-ghost hull and \(L'\) is affine, possibly zero.

The actual grade-six decomposition applied to the monic
six-clean hull \(S_6\) gives
\(S_6-UQ_3=\omega R_6\), \(\deg Q_3\le3\).
Indeed its degree-at-most-five polynomial part vanishes at
six clean sites, and then its ghost restriction is \(UQ_3\).
The scalar \(\omega\) is nonzero: otherwise the nonconstant
\(U\) would divide \(S_6\) despite being live on all its
roots. Put \(D=X(X-a)(X-b)\) and \(R_f=-R(1-X)\), so
\(S_6=D R_f\). Because \(U\) is live at \(0,a,b\), \(D\)
is a unit in the cubic algebra modulo \(U\).
Define
\[
 P=H(a)H(b)(a-b)F
    -H\{F(a)H(b)(X-b)-F(b)H(a)(X-a)\}.
\]
It is exactly divisible by \(D\). Multiplying the
\(F-HL\) relation by the displayed scalar and cancelling
\(D\) in the cubic algebra shows that \(P/D\) is in
the span of \(R_f,XR_f\) in that algebra. Hence
\[
 S=\det\big(R_f,XR_f,P/D\big)\bmod U=0.                       \tag{3}
\]
The determinant here takes three coordinates of each cubic
remainder. The program uses ordinary synthetic division for
the exact factors of \(D\) and pseudo-remainders against the
live cubic leader. No irreducibility of \(U\), nonzero
affine coefficient, or noncontact of actual ghost clocks
with ordinary clocks was used. Neither an adjacency formula
for \(\beta=0\) nor a conjectural extra moment is needed.

## 4. Exact remaining profile projections

The original affine-old-cubic census gives either a
monomial \(m\) or \(m=Y^2+rY+s\) with \(s\ne0\), after
common rescaling. The monomial \(m=Y\) is impossible by
the first-gap quartic (its zero-clock read has live numerator
\(-3c_0^2/10\)). The other monomials force respectively
\(c_2=0\) for \(m=1\) or \(c_1=0\) for \(m=Y^2\).
For a mixed profile \(r=0\), the old census forces the
affine slope \(-1\), impossible by the second live ghost
debit. With \(r\ne0\) but \(c_2s=c_0\), it gives the
finite ordinary relation and reconstruction
\[
 12c_0^2+8c_0c_1c_2-6c_0c_2^3+c_1^2c_2^2=0,\quad
 s=c_0/c_2,\quad r=(2c_0+c_1c_2)/c_2^2.
\]
All three finite cases are tested here anew for **cubic**
carriers using (2). They do not rely on the earlier
quadratic-only exclusion.

Otherwise \(rs(c_2s-c_0)\ne0\). Use the exact
[profile-factor ledger](../dirk11-thirteen-invisible-six-alpha-two-quadratic/README.md#2-exhaustive-regular-and-singular-old-profiles)
for the literal equations \(D(r,s)=0\) and
\(A_1(s)r+A_0(s)=0\). This part of that ledger is
degree-independent. On a live \(A_1\) the \(F_1\)
root forces slope \(-1\), and the \(F_2\) root forces
\(m\mid R\). Thus only \(F_n\) remains and, if its
denominators are live, \(r=r_n=6c_2s/(c_1+6s)\).
On \(A_1=0\), use the forbidden known roots on
\(F_1,F_2\) and Vieta's alternate root. On \(F_n\)
with live denominators, the known root \(r_n\) is
covered by the first calculation without any assumption on
\(A_1\), and again take the alternate root. Overlap of
\(F_i\) does not remove an actual branch. The lost
denominator \(c_1+6s=0\) forces \(c_2=0\) by \(F_n\)
and gives the two-root monic equation
\[
 s=-c_1/6,\qquad r^2+(4s^2/c_0)r-3s=0.
\]

For the four nondegenerate cases, **clock.py** builds the
rank-12 monic tower over \(\mathbb Q[V]\).
For clarity, \(J_4,J_5\) are the same as in the earlier
Jacobi pencil. Scale clocks by \(L=132J_4(V)\), so
\(\widehat B=LB\) satisfies the scaled ordinary quartic;
\(\widehat R\) is the corresponding monic cubic cofactor.
Then adjoin \(\sigma=L_3L^2s\) monically, where \(L_3\)
is the leader of the chosen profile cubic in the scaled
ordinary parameters. Profiles with \(L_3=0\) have
already been sent to a finite chart. The constructed
\(m^\#\) coefficients
\((\sigma t_1,L_3t_0,L_3t_1)\) give the same polynomial up
to live scale as the old \(m\) in the scaled clock.
Multiplication by the adjugate of \(m^\#\) gives
\(M,W_0,Q_0\) in one common numerator gauge. The scaling
changes \(J_4,L_0,L_1\) by powers \(L^4,L^4,L^5\),
respectively, besides substituting \(Y=\widehat Y/L\);
all determinant equations are homogeneous under these
rescalings. All removed nonconstant scalar coefficient
contents are verified to have support only
\(V(V-1)J_4(V)\), which is live.

For the \(r_n\) tower, the exact norms of (2) and (3)
have degrees **2344** and **2940** over \(\mathbb Q[V]\),
with joint gcd degree **1888**. Its factor inventory includes
only the three listed finite supports below and
\(J_4^{157}, E_-^3,E_+^6,E_{\rm rep}^3\), up to a
nonzero scalar. The exact equalities
\[
 2(V-1)E_-=J_5-J_4,\quad 2VE_+=J_5+J_4,\quad
 2E_{\rm rep}=J_5'J_4-J_5J_4'
\]
discard these factors: respectively coprimality, a
forbidden endpoint root, a forbidden endpoint root, or a
repeated regular clock. On alternate towers the projection
of the extra equation \(A_1=0\) alone suffices. Its exact
norm degrees are **352**, **352**, and **768** as listed.
Their only omitted exact factors are \(J_4,E_+\) with
powers respectively \((28,30),(28,30),(54,24)\).

Here a finite factor is identified by degree and its
constant coefficient when necessary. The full polynomial
and its irreducibility are obtained by exact factorization
in the script. "Full" means no guard is needed.

| Tower | Remaining exact factor | Live guard | Exact cap | Residue degree |
|---|---|---|---:|---:|
| \(r_n\) | 60 | old \(m\)-norm | 11 | 1 |
| \(r_n\) | 12, constant 16227 | scaled \(c_1+6s\) | 11 | 12 |
| \(r_n\) | 12, constant 54123 | lower \(c_2\) | 9 | 4 |
| \(F_1\) alternate | 48 | Full | 12 | 1 |
| \(F_1\) alternate | 36 | old \(m\)-norm | 11 | 1 |
| \(F_2\) alternate | 36, constant −4682817 | old \(m\)-norm | 11 | 36 |
| \(F_2\) alternate | 36, constant 137146315515648 | Full | 12 | 1 |
| \(F_2\) alternate | 48 | Full | 12 | 2 |
| \(F_n\) alternate | 48, constant −14638292540815408663567 | Full | 12 | 1 |
| \(F_n\) alternate | 48, constant 162325396752128559 | old \(m\)-norm | 11 | 2 |
| \(F_n\) alternate | 48, constant 41521530286435 | Full | 12 | 1 |
| \(F_n\) alternate | 12 | lower \(c_2\) | 9 | 4 |

At an actual field evaluation of the monic tower, a zero
equation forces its specialized norm to be zero, since its
multiplication map is killed by the nonzero evaluation
functional. For each exact remaining irreducible factor
\(f\), work over \(K_f=\mathbb Q[V]/f\).
If a guard \(g\) is listed, the code checks that \(f\)
divides the exact projected norm of \(g\). This gives the
dimension upper bound 11 for its multiplication image. For
\(c_2\) it gives upper bound 3 at the lower quartic
layer and thus 9 after the degree-three extension. With
\(g=1\) the upper bound is 12. Over the chosen same-degree
reduction of \(f\) at 103 and one irreducible factor of
that reduction, nonzero minors show that the images of
\(gE,gS\) (and \(gA_1\) on alternate towers) already
reach this exact upper bound. To see the lift, if all minors
of that size over \(K_f\) were zero, polynomial
division by the monic \(f\) would give zero coefficients,
and thus zero reductions at the chosen prime. Our ring
calculations only invert rational constants whose
denominators are units in that reduction. Rank over
\(\mathbb F_{103}\) equals rank over the residue extension
times its degree. Thus the sum of the images equals
\(\operatorname{im}(g)\) **over the exact clock field**.
An actual evaluation killing the equations would kill
\(g=g\cdot1\), a contradiction. No tableau coefficient,
weight, or ghost clock is assumed integral at 103.

The four lower-degree cases are handled independently by
**finite.py**. For \(m=1,m=Y^2\), the mixed contact,
and the lost Fn denominator, the exact ordinary resultants
leave respectively degrees **12, 12, 48, 12**, apart from
powers of the forbidden \(J_4\). The source checks all
multiplicities and mixed pseudo-remainder content, and
recovers the fifth ordinary label from a linear
subresultant. Its pivot, Jacobi denominators, old norm and
any contact denominators are certified as units by
reduction. In the last case adjoining **both** possible
\(r\)'s by the monic quadratic gives dimension 24.
In each of the resulting dimensions **12,12,48,24**, (2)
alone is a unit modulo 103, so its exact multiplication
determinant cannot vanish. These arithmetic proofs do not
use assumptions about the signs of the clocks.

## Reproduction and native scope

Use Python 3 with python-flint 0.9.0 and SymPy:

    for t in regular F1 F2 Fn; do python3 clock.py "$t"; done
    python3 finite.py
    python3 ../dirk11-thirteen-invisible-six-alpha-two-debit/zero-cubic.py
    python3 ../dirk11-thirteen-invisible-six-alpha-two-quadratic/check-old-pivot.py

For isolated replay, the sibling-source scripts accepting it
can use **--research PATH**. No large stored resultant files
or external solver are needed. The companion
**DIRKOrderElevenInvisibleSixAlphaTwoLiveCubic** Lean module
checks the cleared determinant expansion and elimination,
nonzero leader, contact implication, and affine residual
scalar gates. The literal rooted transfer and the complete
arithmetic tower exclusions above are exact written/source
proofs; the Lean module does not claim a full tableau
nonexistence endpoint.
