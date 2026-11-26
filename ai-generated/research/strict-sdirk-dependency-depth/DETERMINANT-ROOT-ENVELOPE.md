# Exact determinant-root factorization and middle clock recurrence

Source-only mathematical checkpoint. Let \(A=\gamma I+B\) be a
common-diagonal triangular RK tableau over a characteristic-zero
field, with \(s=p+1,\ p\ge8\) physical stages and rooted order through
\(p\). Here \(\gamma\ne0\), the actual full-chain product \(L\ne0\),
and the paid top \(B_0=\lambda_{p-1}\ne0\).
Consider the remaining scalar branch \(\Delta=0\) in the exact
centered three-hole rectangle. No value is assigned to an unpaid
tall coefficient or to the actual \(L\).
This proof gives a scalar root audit and a structural recurrence,
not a blanket exclusion of these diagonals.

## 1. Normalized paid scalar geometry at a root

Write \(M,K,R,S\) for
\(\lambda_{p-2},\lambda_{p-3},\lambda_{p-4},\lambda_{p-5}\).
The centered rectangle has paid scalar coefficients
\[
\begin{aligned}
 \kappa&=B_0+2\gamma M+\gamma^2K,
 &\eta_0&=M+2\gamma K+\gamma^2R,\\
 V_3&=B_0+3\gamma M+3\gamma^2K+\gamma^3 R,
 &V_4&=B_0+4\gamma M+6\gamma^2K+4\gamma^3R+\gamma^4S,\\
 D&=B_0K-M^2,\quad E=M\kappa-B_0\eta_0,\quad
 &F&=B_0V_4-\kappa^2,\\
 H&=M\kappa,\quad G=B_0(2V_3-V_4)-\kappa^2,
 &\Delta&=DF-E^2 .
\end{aligned}
\]
In particular
\[
 \Delta=\gamma^4 B_0\det H_3,\qquad
 H_3=(\lambda_{p-5+i+j})_{0\le i,j\le2}.
\]
All displayed coefficients are paid.

Use the normalized reverse functional
\(\mu(y^j)=\gamma^j\lambda_{p-1-j}/B_0\), so \(\mu_0=1\).
Put \(a=\mu_1,\ b=\mu_2,\ d=b-a^2,\ u=a b-\mu_3,\
v=\mu_4-b^2\). Then \(d=\gamma^2 D/B_0^2\),
\(\gamma E/B_0^2=-2d+u\), and \(\Delta=0\) gives \(dv=u^2\).
Here \(d\ne0\): if \(D=0\), then \(\Delta=0\) gives \(E=0\),
hence \(B_0K=M^2\) and \(B_0R=MK\). If \(M=0\),
the paid recurrence at the top would give \(B_0=0\).
Otherwise \(R,K,M,B_0\) are geometric with nonzero common ratio
\(r_0=B_0/M\); comparing two successive scalar recurrence rows
gives \((r_0+\gamma)^2=0\), then \(\gamma=0\) on substitution.
Both alternatives contradict the stated chart.

Define the preferred physical step
\[
         \delta=-E/D,\qquad r=u/d=2-\delta/\gamma,\quad
         q(y)=y^2+r y-q_0,\qquad q_0=b+r a .
\]
Directly from these definitions \(q\) is orthogonal to \(1,y,y^2\)
under the moment functional \(\mu\). The leading \(2\)-by-\(2\)
moment determinant \(d\ne0\), so this is the unique monic
quadratic in the kernel of the order-three moment matrix.

### Paid Pearson identity and automatic scalar compatibility

Put \(\xi=1/\gamma\). The paid reverse recurrence is
\[
  (p-k)\mu_k=(\xi-2(p-1-k))\mu_{k+1}-(p-2-k)\mu_{k+2}.
 \tag{1}
\]
Equivalently, for a polynomial \(P\) of degree at most \(p-3\),
\[
                 \mu(A_0P-y(1+y)^2 P')=0,\qquad
                 A_0=p-(\xi-2(p-1))y+(p-2)y^2 .
 \tag{2}
\]
This is (1) on monomials, not a positivity assumption.
Let \(k_0=\mu((1+y)^2),\,l_0=\mu(y(1+y)^2),\,
m_0^\ast=\mu(y^2(1+y)^2)\).
Using \(P=q\) in (2) and the kernel gives
\(2m_0^\ast+r l_0=0\).
Using the kernel on \((1+y)^2\) gives
\(m_0^\ast+r l_0=q_0 k_0\). Thus \(m_0^\ast=-q_0 k_0\).
The normalized rectangle constants satisfy
\[
 \kappa/B_0=k_0,\qquad \gamma H/B_0^2=a k_0,\qquad
 G/B_0^2=k_0-m_0^\ast-k_0^2 .
\]
Because \(1-k_0+(\delta/\gamma)a=-q_0\),
these identities prove the *automatic* scalar compatibility
\[
                          DG=HE.                             \tag{3}
\]
This uses no shape of the actual clocks.

There is also an exact terminal anchoring identity.
Put \(n=p-2=s-3\) and \(z=\xi-2\).
The two top scalar recurrence rows give
\(n k_0=z a-2\) and \((n-1)l_0=z b-2a\).
Writing \(e_0=a k_0-l_0=\gamma E/B_0^2\)
and \(h_0=a k_0=\gamma H/B_0^2\) yields
\((n-1)e_0+h_0=-z d\). Hence
\[
                     H+(p-3)E=(2\gamma-1)D .                \tag{4}
\]

An optional scalar filter where \(\kappa=0\) is particularly
small: it forces \(\gamma^{-1}=2(p-2)\) and \(\delta=2\gamma\).
Indeed \(\kappa=0\) implies \(l_0\ne0\), since
\(\kappa=V_3=0\) is forbidden by the simple reciprocal
\(L_{p-3}^{(3)}\) root calculation in the prior rectangle
proof, and \(V_3/B_0=k_0+l_0\).
The two kernel/Pearson equations above then give \(r=0\).
Now \(\mu_3=ab,\ k_0=1+2a+b=0,\ l_0=2d\).
The scalar identities \(za=2\), \((n-1)l_0=zb-2a\)
and \(d\ne0\) give \(a=1/(n-1)\), \(\xi=2n\).
This is a necessary rational candidate, not an exclusion
or occurrence theorem for this subbranch.

## 2. A multiplicity audit, without assumptions on determinant roots

For a geometric mode \(r_0^k\), the residual of (1) is
\(r_0^k A_k(r_0)\), where
\(A_k(r_0)=A_0(r_0)-k(1+r_0)^2\), and \(A_k(-1)=\xi\).
For a repeated mode \((A+B k) r_0^k\) the residual is
\[
 r_0^k\big[(A+Bk) A_k(r_0)+B r_0\,\partial_{r_0}A_k(r_0)\big].
\]
If \(r_0\ne0,-1\), its degree-two and then degree-one
coefficients cannot all vanish unless \(A=B=0\);
at \(r_0=-1\) use \(A_k(-1)=\xi\ne0\) and
\(\partial_{r_0}A_k(-1)=2-\xi\) in the same way.
Distinct polynomial-exponential modes are independent:
a suitable power of shift minus the other root kills
it and is invertible on the first polynomial mode.
The homogeneous recurrence order for such a sum is
at most the sum of one plus each polynomial degree,
so that many consecutive initial zeros kill it.

The kernel implies a fixed monic quadratic recurrence
for the moments through \(\mu_4\).
Its two roots over an algebraic closure are distinct and
neither is \(0\) or \(-1\).
Indeed a repeated nonzero root would have residual of
degree at most two times its geometric mode and is
killed by the three paid rows \(k=0,1,2\).
A zero root leaves at most one geometric mode from \(k=1\)
on, killed by rows \(1,2\). If both roots are zero, then \(\mu_2=\mu_3=0\), and row \(1\) first forces \(\mu_1=0\). In either case row zero then cannot
have \(\mu_0=1\). If one of two distinct nonzero roots
were \(-1\), its residual is constant-amplitude
alternating, and that of the other root affine times
its geometric mode. The total recurrence order is
at most three, again contradicted by rows \(0,1,2\).
This is a theorem about the *kernel quadratic*, not a
hypothesis on roots of the diagonal determinant.
Moreover
\[
                           \mu(q y^3)\ne0.                    \tag{5}
\]
If it were zero, the same fixed quadratic would hold
through \(\mu_5\). The two distinct nonzero modes then
have residual of order at most four, killed by paid
rows \(0,1,2,3\), contradicting \(\mu_0=1\).

At any nonzero determinant root in this paid-top-nonzero
chart, the determinant itself is simple, as a consequence.
Let \(H_\mu=(\mu_{i+j})_{i,j=0}^2\).
Its adjugate at the root is \(d\,\mathbf q\mathbf q^T\),
where \(\mathbf q=(-q_0,r,1)^T\): rank is two and the
last diagonal cofactor is \(d\).
When taking the scalar derivative in \(\gamma\), freeze
the coefficients of \(q\) at the root. From
\(\lambda_j'=-j\lambda_{j-1}\), the derivative of the
normalized functional at a fixed polynomial is
\[
 \gamma\partial_\gamma\mu(P)
    =\mu(yP')-(p-1)\mu(yP)+\mu(y^2P')+(p-1)a\mu(P).
\]
Use \(P=q^2\). The kernel makes \(\mu(P)=\mu(yP')=0\);
also \(\mu(yP)=\mu(qy^3)\), and
\(\mu(y^2P')=4\mu(qy^3)\).
Thus
\[
     \gamma\,(\det H_\mu)'=d(5-p)\mu(q y^3)\ne0
 \tag{6}
\]
by (5) and \(p>5\).
Since \(\det H_\mu=\gamma^6 B_0^{-3}\det H_3\),
the root of the original \(\det H_3\) is simple too.

For completeness, the pure scalar polynomial
\(\det H_3(\gamma)\) has exact degree \(3(p-5)\) for
\(p\ge6\) and no additional roots at \(\gamma=0\) or
\(B_0=0\). To see the degree, write \(h=p-5\),
\(\lambda_j=(-\gamma)^j\widetilde\lambda_j(1/\gamma)\) with
\(\widetilde\lambda_j(\xi)=
\sum_u\binom ju (-\xi)^u/(u+1)!\).
Factor \((-\gamma)^{3h+6}\) from the determinant.
Apply unipotent forward differences to the rows and
columns. Its \((i,j)\) normalized entry becomes
\[
 \Delta_{\rm diff}^{\,i+j}\widetilde\lambda_h(\xi)
    =(-\xi)^{i+j}\sum_u\binom hu
                                  \frac{(-\xi)^u}{(u+i+j+1)!}.
\]
Thus the determinant has a factor \(\xi^6\) with
remaining value at \(\xi=0\) the nonzero reciprocal
factorial determinant \((1/(i+j+1)!)\). This gives the
exact degree. At \(\gamma=0\) the original reciprocal
factorial matrix likewise has nonzero determinant by
row scaling to evaluations of \(x(x-1),x,1\).
At \(B_0=0\) and \(\gamma\ne0\), \(M\ne0\);
the earlier paid cubic calculation gives
\(\gamma^3\det H_3/M^3=-C_{p-1}((1/\gamma-2)/(p-2))
/((p-3)(p-4))\ne0\).
Consequently the polynomial \(\det H_3\) is actually
squarefree in this range. The structural proof below
does not use this as a premise, and this scalar audit
does not settle which roots can support a tableau.

## 3. Exact triangular factorization at the root

Use shifted actual clocks \(x_i=c_i-\gamma\),
adjacent gaps \(g_i=x_{i+1}-x_i\), accumulated actual
one-hole weights \(U_i\) from the first \(i\) stages,
and
\[
 \sigma_i=g_iU_i/L,\qquad
 \tau_i=g_i(B_0-U_i)/L,\qquad A'_i=B_0+(i-1)\kappa .
\]
These are exactly the quantities of the centered
three-hole rectangle, so
\(\sigma_i+\tau_i=B_0g_i/L\).
For \(1\le i\le j\le n=s-3\), put the following. Also use the same clock formula for \(a_{n+1}^\circ\) when the recurrence reaches that last index.
\[
 \begin{aligned}
    a_i^\circ&=x_i-(i-1)\delta,&
    b_i^\circ&=\sigma_i-(A'_i-Mx_i)/B_0,\\
    r_j^\circ&=x_{j+3}-\delta(j-1)+H/D,&
    t_j^\circ&=\tau_{j+2}+(A'_{j+1}-Mx_{j+3})/B_0 .
 \end{aligned}
\]
By \(\Delta=0,\ F=E^2/D\) and (3), the exact centered
rectangle specializes to
\[
             \boxed{\quad
                D a_i^\circ r_j^\circ=B_0^2 b_i^\circ t_j^\circ .
                  \quad}                                    \tag{7}
\]
For instance its paid left side before specialization
was \((D x_i+(i-1)E)x_{j+3}+
(E x_i+(i-1)F)(j-1)+H x_i+(i-1)G\); these scalar
compatibilities factor it exactly.
The right side of (7) is its actual centered product.
Using (4), the right clock reference is
\[
       r_j^\circ=c_{j+3}+\gamma-1+(n-j)\delta .
\]
It is anchored at \(1-\gamma\) at the last stage when
the defect vanishes, not asserted equal to that clock
without the defect test.

There are at most two source-span transitions.
Let \(i_0\) be the first nonzero source pair
\((a_i^\circ,b_i^\circ)\) in \(2,\ldots,n\), or the
sentinel \(n+1\) if none. Let \(i_1>i_0\) be the
first source independent of the source at \(i_0\)
in this range, or \(n+1\) if none.
The first stage already has \(x_1=0,\sigma_1=1\),
so its two defects are zero.

* Before \(i_0\), both source defects vanish. The
  literal prefix through \(i_0-1\) is arithmetic
  of step \(\delta\) and its cut weight \(\sigma_i\)
  is affine. Its normalized singleton weights are
  constant strictly inside that prefix when the step
  is nonzero. If the prefix has length at least two,
  its step is \(x_2=B_{21}\ne0\).
* After a finite \(i_1\), both right defects vanish
  for all \(j\ge i_1\), because (7) pairs each with
  two independent sources. Thus the literal
  tail \(i_1+3,\ldots,s\) is arithmetic with step
  \(\delta\) and endpoint \(c_s=1-\gamma\).
  The vanishing right cut defect makes \(\tau_{j+2}\)
  affine, so if the step is nonzero the normalized
  interior singleton weights are constant as well.
* In between, the sources lie on the line of the
  first nonzero pair, and all subsequent target pairs
  lie on its line of annihilators in (7).
  The following clock recurrence uses only their overlap.

## 4. Exact middle recurrence and a bounded seed exception

If both components of the first nonzero source are
nonzero, its line is \(b_i^\circ=\beta a_i^\circ\)
for \(i_0\le i<i_1\), with \(\beta\ne0\).
All targets with \(j\ge i_0\) obey
\(t_j^\circ=\zeta r_j^\circ\) where
\(\beta\zeta=D/B_0^2\).
Define the scalar containing the actual, unassigned
full product:
\[
                         V=B_0/L-M/B_0 .
\]
At each overlapping physical cut \(i_0+2\le k\le i_1-1\),
add the left defect at \(i=k\) and right defect at
\(j=k-2\). Exactly,
\[
 b_k^\circ+t_{k-2}^\circ
            = V(x_{k+1}-x_k)-\kappa/B_0,\qquad
 r_{k-2}^\circ=a_{k+1}^\circ+3\delta+H/D.
\]
Therefore
\[
 (V-\zeta)a_{k+1}^\circ-(V+\beta)a_k^\circ
                =\kappa/B_0-V\delta+\zeta(3\delta+H/D).
 \tag{8}
\]
This is a constant first-order affine recurrence in the
clock defects, derived before any division by a gap.
With a nonzero leading coefficient it has a constant
plus one geometric mode, or is affine in the index for
ratio one. Hence the actual clock sequence in that
overlap is arithmetic plus at most one geometric mode.
If just one coefficient of (8) vanishes it instead fixes
the clock defect on the corresponding segment to a
constant. No such solution is declared realizable by
all the remaining RK conditions.

If both left coefficients vanish and the overlap
contains a cut, then \(V=\zeta=-\beta\), so \(D=-B_0^2V^2\).
Consistency gives the exact quadratic and linear
conditions on the actual \(L\):
\[
 \begin{aligned}
      &(B_0^2-M L)^2+D L^2=0,\\
      &\kappa L+(B_0^2-M L)(2\delta+H/D)=0 .
 \end{aligned}                                               \tag{9}
\]
The first polynomial is nonzero (constant term \(B_0^4\)),
so this is at most a quadratic seed exception at each
fixed scalar root, not an unpaid tall assignment.
In fact the consistent exception determines at most one
\(L\): \(V\ne0\) since \(D\ne0\), and if either
\(\kappa\) or \(2\delta+H/D\) vanished the other would
as well by the linear consistency. Both zero are
impossible: then \(H=0,\delta=0,E=0,\eta_0=0\),
and \(\kappa=V_3=0\) contradict the simple reciprocal
Laguerre-root argument. Thus the constant term
\(B_0^2(2\delta+H/D)\) of the linear equation is
nonzero in the consistent exception, and it forces
a unique actual \(L\). A necessary purely paid
scalar filter for that seed is
\(D\kappa^2+(H-2E)^2=0\), by squaring the consistency
and using \(D=-B_0^2V^2\).

For clarity the two axis cases are also determined,
not secretly divided by in (8).
If the first nonzero source has \(b^\circ=0\),
the right clock defect vanishes for every \(j\ge i_0\).
In the part of that arithmetic tail overlapping the
left axis phase, the left cut constraint makes the
singleton weights constant: a joint run through
\(i_0+3,\ldots,i_1\) when these indices are in range.
If instead the first has \(a^\circ=0\), the prefix clock
reference remains valid through \(i_1-1\); the right
cut defect vanishes for \(j\ge i_0\).
Their overlap is a joint run through
\(i_0+2,\ldots,i_1-1\). Empty intervals carry no claim.
With \(\delta=0\) these are literal constant-clock
runs rather than divisions by a zero step.

## 5. Shorter arithmetic restrictions at the preferred step

At this root the kernel quadratic is exactly
\(q=F_1-\mu(F_1)\) for the local gap polynomial
\(F_1=(1+y)^2-(\delta/\gamma)y\).
On a nonzero-step joint \(\delta\)-run, the local
evaluation-plus-tangent rule applies.
Length six pays \(F_1^2\); since \(\mu(q^2)=0\),
its covariance is zero and
\(\chi(F_1)=\mu(F_1)\) for this local character.
Thus (paid grade permitting)
\(\mu(qP)=0\) with additional gap polynomial \(P\):
both character and tangent on the first factor vanish.
If \(\delta/\gamma\ne2/3\), \(P=F_2\) has a nonzero
cubic coefficient. Length seven pays \(F_1F_2\),
contradicting (5) by the already known lower orthogonality.
If \(\delta/\gamma=2/3\), length eight pays
\(F_1F_3\) and \(F_1^3\). Subtract the monic quartic
\(F_1^2\) with appropriate coefficient from \(F_3\).
Its odd cubic coefficient in the shifted variable
\(y+1-(\delta/\gamma)/2\) is \(4/81\), so the result
is cubic and again contradicts (5).
Hence each root-specific joint \(\delta\)-run has at
most seven stages (six off that exceptional step).
For \(\delta=0\), the earlier constant-clock result
gives at most four.

As a uniform structural corollary, for \(p\ge27\)
a surviving chart has \(i_0\le8\), since its initial
joint prefix cannot be longer, and \(i_1\ge n-6\)
(or the sentinel) from the same terminal bound.
Thus the possible axis overlaps have length at least p-18,
so either axis would already contradict the
root-specific run obstruction above.
In the mixed phase the overlap covers at least
\(p-17\) consecutive clocks. If (8) has just one
nonzero coefficient, a constant defect on all but
one boundary clock gives a forbidden preferred-step
joint run (or a constant run). If both nonzero
coefficients give ratio one or a zero geometric
amplitude, the overlap is arithmetic and joint
by the affine cut formulas; length at least ten
is excluded by the general local tangent result,
or by the constant-run result if its actual step
vanishes. Thus at these orders a surviving
mixed phase has either the exceptional seed (9)
or a genuine arithmetic-plus-geometric block with
nonzero ratio different from one and nonzero
geometric amplitude. This is a structural
constraint, not a stage-count endpoint.

The preceding proof uses the exact centered rectangle
(NONVANISHING-CENTERED-RECTANGLE.md, SHA-256
c8129f8ada38fe1373c16641dd86d74a5ebde0668efa0695dd70572f41bf4837);
the local tangent law
(NONVANISHING-LOCAL-TANGENT.md, SHA-256
8a45a0900b27bd3d9d8ffc8ddc8dacd2001c7ea7a2025e5f9cec6722f48e78);
and, only for the pure scalar statement at \(B_0=0\),
the paid cubic exclusion in the earlier vanishing-top proof.

At orders 18–20 the guaranteed middle overlap can be short or empty. The long-overlap conclusion for p≥27 is separate and provides no exclusion at those orders.
