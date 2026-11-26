# Independent audit: the eighteen-stage ERK order-twelve floor over paid fields

**Verdict.** Pass when the combined chart, the independently checked paid
fifth-degree stage floor, and the F283 pure quartic proof plus its erratum
are used together. This excludes an explicit order-twelve method with at
most seventeen stages over every field in which \(12!\) is a unit, hence
over every nonzero commutative unital ring with cleared rooted equations.
The prior characteristic-zero bound is unchanged. This is a mathematical
audit, not a new or widened Lean certificate.

Exact shared-note inputs (UTF-8 SHA-256):
- ORDER-TWELVE-GHOST-GATES.md:
  ec95677320dafb1a26e0d8b34c8c6b6e5524fdb152297eaa9f028b13f7723594.
- ORDER-TWELVE-CHAR283.md:
  43212254eed01759a4b0b5fd744a73fa15d3eabae792d7023be57441b62fcc5f.
- ORDER-TWELVE-CHAR283-ERRATUM.md:
  9825948771b1aec7f2180675acb43559102df53df714a795502585d80dcdc90f.
- ../proof-dependencies/pass0045_q6_even.md:
  7e16f6839ebbd9a8c8f8f5d9d26b40a0ff91c91ab2629359b4ffc6ffea301e73.
- ../characteristic-zero/erk_field_independent_surgery_one_head_and_p12_baselines_20261123.md:
  290cb74ddccb745ecfdfee327236bdcefb370c2d6f400089ececbd837a8fb052.
The independently established fifth-degree surplus has source SHA
04d079168bd240a544d036cc0331d3272ce52b61d21b7d0125eee273755b3b50.
No terminal execution, solver, Lean, repository action, or other chart
was used in this audit.

## Upstream equality chart and payment

Work first over a field with the indicated units. For a numerical pair
\((z,g)\) of degree at most \(j\), the test \(bC^kz=I(x^kg)\) is paid
when \(j+k\le11\). Strictness makes the first coordinate equal \(g(0)\);
a zero numerical pair through degree \(j\le6\) therefore has \(g=xG\).
Apply the \(j\) consecutive clock tests to get the size-\(j\) Gram
matrix for \(x\,dx\), with factorial cutoff \(2j\le12\). This yields
\(E_j=P_j(c)\oplus F_j\) in that range. The fixed weighted matrices in
this audit have weights \(1,x,x(1-x)\). For a matrix of size \(h\)
and weight \(x^\alpha(1-x)^\beta\), the paid Beta determinant uses
only factorials through \(\alpha+\beta+2h-1\). In particular all
size-five \(x(1-x)\) matrices are paid through eleven.

Set \(Y=I-C\) for backward rows. Integration by parts makes each
backward \(L_t\) annihilate \(E_j\) at \(t+j\le11\); the original
generators have order cost \(t\), and right multiplication by \(A,Y\)
increases it by one. Strict forward and backward rank growth are
algebraic: the partial inverse of a diagonal is its polynomial taking
zero to zero and inverting each nonzero value. Its product with the
strictly triangular matrix is nilpotent, also on a common invariant
quotient. Applying this to the quadratic residual excludes plateaus,
because the nonzero first moment cannot lie in the silent space.
The paid fifth-degree surplus gives \(\dim F_5\ge5\).
Consequently a putative \(s\le17\) has \(s=17,\dim F_5=5,\dim F_6=6\),
\(\dim E_6=13,\dim L_t=t-1\) for \(t=1,\ldots,5\), and
\(L_5=E_6^\perp\). In particular \(\ell_1=0\). Trimming a trailing
zero weight would contradict the preliminary floor, so \(b_s\ne0\).
The terminal clock is 1 by \(\ell_1=0\), and every \(L_t\) is zero
on that coordinate, since \(A e_s=0\) and \(Y_s=0\).
Therefore \(e_s\in E_6\).

The strong Hermite gain used here needs no field order. Chronologically
compress the span of the invariant subspace and the \(j+1\) scalar
columns; diagonal block functionals killing the invariant subspace
are one-dimensional when nonzero, because killing the generating
column on a single clock kills all its powers. They can be
normalized on that column. A last-supported relation among the
first \(\lfloor(j+1)/2\rfloor\) nonzero clocks would make its
primitive readout a sum of earlier clock functionals. Test the
derivative of \(x \prod (x-\xi)^2\), or of \(x^2\prod(x-\xi)^2\)
if the zero-clock functional is earlier. Its degree is at most \(j\);
it vanishes at the earlier clocks but its zero-origin primitive
is nonzero at the last contributing clock. This proves the gain
\(\lfloor(j+1)/2\rfloor\) at the next degree. For the backward use,
independence of the \(j+1\) weighted scalar columns modulo \(L_j\)
comes from the unweighted reflected Hilbert matrix at \(2j\le11\),
not a squared polynomial sign. Every inverse other than an
explicit nonzero field entry is in the paid cutoffs.

The product of \(e_s\) with \(F_5\) costs eleven, so
\(F_5\) vanishes at the terminal. Hermite rules out its clock
invariance, hence \(F_6=F_5+CF_5\) and also vanishes there.
The terminal polynomial profile has \(f(0)=0,f(1)=1\).
The tests \((1-x)x^j\), \(j=0,\ldots,4\), cost at most eleven
and give the degree-five orthogonal line for \(f/x\) under
\(x(1-x)\,dx\). The normalization is \(f=xD\) as in the source.
If \(F_6\) were invariant, the gain would put at least nine
directions in \(F_7\); at least eight would be last-zero.
Yet \(E_7\) has dimension at most fourteen, and \(P_6(c)\)
is disjoint from the last-zero \(F_7\): factor \(x(1-x)\)
and apply the size-five tests at degree \(7+4=11\).
This gives a contradiction. The rank-one escape decomposition
is algebraic via the decreasing filtration of vectors whose
successive \(C\)-powers stay in \(F_5\). Its invariant core
\(U\) and head \(w\) now give \(F_5,F_6\) as stated; Hermite
applied to \(U\) gives \(r\ge2\).
The space \(F_6+CF_6\) has dimension seven and is last-zero,
so it and \(P_6(c)\) saturate \(E_7\). The backward Hermite
gain disallows invariance of \(L_4,L_3\) and hence of
\(E_7,E_8\); their next grades therefore reach their exact ranks.

For the remaining E9 escape, the following reconstruction avoids
any exceptional-minor assumption. Reverse the coordinates and
transpose \(A\), making \(N\) strict lower; let \(Y\) be the
reflected diagonal and \(v\) the reversed weight column. Then
\(Nv=Yv\). If the dimension-one \(L_2\) were \(Y\)-invariant,
its generator \(d=NYv-Y^2v/2\) is supported at one nonzero
clock \(a\) (use the first nonzero coordinate of \(Yv\)).
Set \(h=Yv+2d/a\) and \(G=Nd/a\). The usual nilpotent
invariant quotient argument makes \(G\) independent of \(d\);
otherwise \(Yv\) would belong to \(L_2\) despite its mass.
The exact spans of \(L_3,L_4,L_5\) are then \(d\) together
with \(G,YG,Y^2G\) as appropriate, by backward Hermite at
degrees three and four. The \(d\) coefficients in the new
row relations are fixed by their first nonzero \(d\) row,
where \(h=G=0\).

The first two distinct nonzero \(h\) clocks \(t,u\) exist:
otherwise \(v\) has at most three active coordinates after
grouping by clock, impossible by the five-dimensional
quadrature Gram rank. Put
\[
 \phi(x)=x(2x-3t)/(4t),\qquad \theta=t/(3t-2u).
\]
In the first nonzero \(h\) row at \(t\), strictness gives
\(G=-t h/4\). Up to and including the first \(u\) row,
the predecessors contribute \(NYh=tNh\), giving \(G=\phi(Y)h\).
At \(u\), the possibility \(2u=3t\) would force \(G_u=0\)
but \(NG_u\ne0\), so \(\theta\) is defined. Matching at the
two rows gives the exact identities
\[
 Nh=Yh/2+2G,\quad NYh=Y^2h/3+(4t/3)G,\quad
 NG=\theta(Y-tI)G,\quad
 NY^2h=Y^3h/4+[t^2+\theta(u-t)(Y-tI)]G .
\]
If preceding nonzero \(h\) values are at \(t,u\), let \(S\)
be the incoming sum at \(u\) at a new row of clock \(x\).
The first two identities give
\(G=\phi(x)h-3(u-t)S/(2t)\).
After substituting this expression, the residual in the
fourth displayed identity minus \(t/2\) times the residual
in the third is \((3/4)(t-u)(x-u)S\).
So \(S=0\) if \(x\ne u\); the third identity then gives
\(x(x-t)(x-u)h=0\), and \(h\) is already zero at clock 0.
At a repeat of \(u\), \(N(Y-tI)G\in L_5\) has no \(d\)
component and is a quadratic in \(Y\) times \(G\); its
quadratic vanishes at \(t,u\) from the first such rows.
Hence \((u-t)\phi(u)S=0\) there as well. Induction confines
\(h\) to \(t,u\), hence \(v\) to \(0,a,t,u\). The scalar
moments through degree eight have a nonsingular size-five
Hilbert matrix, so four physical clock labels cannot suffice.
This is the paid backward E9 escape. It yields \(E_{10}=K^{17}\)
with the exact stated head powers. No unproved large rational
determinant enters these steps.

## Joint blocks, degree-five refund and remaining cases

The \(F_7\) scalar line, and the last-zero \(F_8\) scalar line,
follow from the indicated fixed moments. The latter has
\(x(1-x)D_4\) as its generator. Comparing consecutive shifts
modulo \((x-1)f\) leaves a nonzero \(D_3\) component in \(xD_4\):
its coefficient for monic Jacobi polynomials is
\(I(x(1-x)D_4^2)/I(x(1-x)D_3^2)\), a ratio of nonzero fixed
Gram norms with cutoff eleven. This proves leakage removal.
The given centered quadratics show that \(D\) is squarefree
and coprime to \(D_4\): the discriminant is 240, and their
linear elimination followed by substitution gives \(-8/7\).
The endpoints of \(D\) are nonzero.

For the mixed fit, first apply the multiplier to a core vector
supported at one clock. Its chain component vanishes at all
other effective clocks; their count exceeds its degree, so
the core is invariant under the multiplier. Finite joint
spectral projectors now give a complement on each \((c,v)\)
block. Subtracting the core makes \(vw=P(C)w\) literal;
comparing its consecutive powers makes \(\deg P\le3\).
If \(P=0\), then \(v=0\) on every effective head block and the
head polynomial of \(v\) vanishes at every effective clock.
Thus \(P\ne0\) for \(v\notin U\). Because \(C^2v\in F_5\),
its head coefficient \(R\) has degree at most \(r-3\).
On each matching head block with \(P(k)\ne0\), the terminal
is absent and the two quotient identities in the source
give \(f(k)R(k)+P(k)Q(k)=0\). If \(P(k)=0\), the first forces
\(R(k)=0\). At least \(r+5\) effective clocks and degree at
most \(r+3\) give the exact polynomial identity \(fR+PQ=0\).
The same holds in the clean cubic situation with \(R=1\).

A genuinely mismatching joint block has \(v_B=0,\ P(k)\ne0\),
and a nonzero class of its constant vector modulo \(U_B\).
Since \(E_{10}\) is the whole coordinate space, this quotient
is one-dimensional. Outside the terminal it forces \(f(k)=0\);
at the terminal it first distinguishes only the final coordinate.
At the first revealing prefix, separation gives a normalized
detector \(\lambda\) on that block. One core vector matches
all preceding entries, and multiplying it by a later clock
polynomial still gives a matching core vector. Strictness
and \(AU\subset F_6\) prove the needed primitive equations
because \(\lambda\) kills \(F_6\). The first three successive
mask contrasts have degree at most six, so nonzero scalar
profiles require actual detection. The first two are at
different nonterminal nonzero clocks: a terminal-only
detection would disappear after the next mask, contradicting
separation. The displayed low primitive tests have input
degree at most five. For \(P(0)=0\), start with mask 1;
the three affordable moments force \(P/x=0\) by a
size-three \(x\)-weighted matrix.

For a nonzero-at-origin cubic divisor of \(D\), the first two
moments at \(u\) and the third at \(a\) imply the two omitted-root
equations. The direct numerator in the erratum has centered
reduction \((407z-123)(1-t)\), forcing characteristic 283
since the integer norm is \(-174328=-2^3\cdot7\cdot11\cdot283\).
Then \(u,a\) are 106,178. Direct evaluation of the residual
cubic gives 233,259, both nonzero. The pure quartic with
\(P=xS\) uses masks \(1,x-u,(x-u)(x-a)\) of the same
affordable degrees, reducing to this cubic. The pure
quartic with \(P(0)\ne0\) is precisely the separately
audited physical branch at 106 or 178.

For the mixed quadratic, \(R\) is constant and \(P\) divides
\(D\). The paid first two moments uniquely give
\(P=x^2-6ux/5+3u^2/10\); the third factors as
\(y^2(y-1)^2(4y-3)/20\) after rescaling. Thus \(a=3u/4\).
The distinct five roots, their reflection, and the location
of the root \(1/2\) give exactly the cases in the note.
The exceptional possibilities require \(17\) and \(29\)
simultaneously, or have centered residues 15 in characteristic
19, 16 in characteristic 23, and 21 in characteristic 71.
The potential division by 13 or by 59 is avoided by its
defining linear equation in those characteristics.

In the remaining affine mixed case \(P=(x-\rho)S\),
\(R=k(x-\rho)\), with \(S\) a quadratic divisor of \(D\).
Write \(D=132(x-u)(x-a)(x-b)S\), with \(\rho\ne b,u,a\).
The third mask gives scalar profile \(F(x-\rho)\),
\(F=x(x-u)(x-a)S\), and only possible mismatch coordinates
at \(b\) and the terminal. It cannot be supported just
at the terminal modulo \(U\), because separation would
make that profile a multiple of \(f=132F(x-b)\).
At the newly detected \(b\), subtract the actual vector \(e_s/132\).
The scalar term drops from degree six to \((b-\rho)F\) of
degree five. In the numerical core/head term, \(fR+PQ=0\)
gives \(Q=-132k x(x-u)(x-a)(x-b)\); subtracting cancels
the fourth-degree part of \(-k x(x-u)(x-a)(x-\rho)\).
The remainder is an actual \(F_5\) element, not an assertion
derived from scalar degree alone. The corrected pair is
therefore truly degree five, justifying the paid primitive at
\(b\). This forces \(b\in\{106,178\}\) in characteristic 283.
At \(u\), the first two moments give \(M_2=\rho M_1\),
\(M_3=\rho^2 M_1\), with \(M_1\ne0\) by the same three-moment
matrix. Thus the omitted-root moment at \(u\) is nonzero,
and \(u\) is 69,142,215. The candidate pairs excluding AB
give the independently reproduced numerator arrays
\((219,44,176,276,168)\), \((27,170,185,125,11)\),
\((192,38,234,216,128)\), all nonzero. The numerator
\(6-20s+45d+15s^2-60sd+50d^2\) follows by expanding the three
displayed normalized moments; the rescaling factors cancel.

Finally the cheap degree-two multiplier test is paid with
the three masks at one nonzero clock. It gives \(F_2\subset U\)
and \(r\le4\). In dimension-four \(F_4\), the clock shift
shows \(F_4=U+wP_{r-2}\). Localized products of its elements
with the invariant core have all shifts in last-zero \(F_8\),
hence land in the core, as their head polynomial vanishes
at enough other nodes. Finite per-vector interpolation gives
the indicator masks: intersect an initial nonzero value
class with separating value classes, using \(e-ef\) for
a class of value zero. No generic element over an infinite
field is used. Clean \(r=4,3\) heads have respectively five
or three consecutive square shifts in \(F_8\), enforcing
the stated quadratic/cubic fits. If \(r=2,\dim F_4=3\),
\(F_3\subset U\) and Hermite gives \(\dim F_3=2,F_4=U\).
The three mask taps of each off-mask row lie on one fixed
annihilator line. At the first new nonzero off-mask clock
\(y\) after \(h\), the three moments eliminate this line and
earlier \(h\)-taps to give \(y^2(y-h)^2/4=0\), impossible;
the effective-node count provides at least four distinct
off-mask labels. In dimension four with nonzero leakage,
the degree-12 polynomial \(f^2-fQR_0-H_8Q^2\) is nonzero
by coprimality and degree. Its common-root multiplicities
account for at most two features each, with one spare at
zero. This bounds head features by eleven, masks by three,
and off-mask/off-head features by two, contradicting rank
seventeen. If \(Q=0\), the six roots of \(f\) give the same
feature bound with one nonzero head value at zero. If
\(H_8=0\), the seven head clocks force the exact quartic
factorization and the two already audited pure subcases.
All cases are dispatched without characteristic-zero or
sign assumptions on unknowns.

For a nonzero commutative unital ring, the cleared tall
order-twelve equation makes \(12!\) invertible. Reducing
at a maximal ideal preserves the physical number of stages
and every polynomial order equation, and gives a field of
the paid type. The field contradiction therefore proves the
stated ring floor.
