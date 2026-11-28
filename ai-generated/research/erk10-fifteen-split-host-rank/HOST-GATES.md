# Literal early chronology and the two old hosts

These gates use the [actual size-four input plane](README.md#consequences-and-remaining-work),
in addition to the width-eleven raw word budget.
They hold in the surviving rational split-evaluation
architecture. The integral identities themselves work
over fields with \(10!\ne0\).

## The primitive on the host is nonzero

Write \(P=X(X-r)(X-t_0)\), where \(r\) is the old
host (\(p\) or \(q\)). Then \(P\in U_0\) and
\(T(P)=-JP(r)\boldsymbol d\).
If \(JP(r)=r^3(2t_0-r)/12=0\), then \(t_0=r/2\)
and \(JP(X)=X^2(X-r)^2/4\). At the first distinct
nonzero forward raw clock \(h\ne r\), all earlier
clocks are \(0\) or \(r\), and hence have \(P=0\).
Its literal residual is \(-JP(h)\ne0\), contradicting
\(T(P)=0\). Thus \(JP(r)\ne0\). In particular
\((BE-EJ)P=\ell(JP)\boldsymbol\delta\ne0\) on the
**original** ten-high block, where
\(\ell=\kappa E_r\) and \(\kappa\ne0\). Free old
contact in the \(p\)-case cannot make the original
cubic gate exact while retaining a genuine tilt.

## The host is followed immediately by another nonzero clock

The space \(U_0\cap X\mathcal P_1\) contains a quadratic
or linear model \(F_2\) with \(F_2(r)\ne0\). Otherwise,
its nonzero quadratic-or-linear member and \(P\) give
two independent models in \(U_0\cap\ker E_r\).
This would make \(U_0=\ker E_r\) on \(X\mathcal P_2\),
impossible by independence of the three evaluations at
\(r,s,k_o\) (distinct and nonzero).

Before the first nonzero \(h\ne r\), all preceding
raw clocks are \(0\) or \(r\). The \(P\)-read and
\(JP(r)\ne0\) therefore give \(d_i=1\) at every \(r\)
copy and \(d_i=0\) at every high zero in this prefix.
Now apply \(T(F_2)=-J_r(F_2)\boldsymbol d\): the total
tap to the earlier \(r\)-copies in each row of this
prefix vanishes, since the terms \(J_{x_i}F_2\) and
\(d_i J_r F_2\) cancel and \(F_2(r)\ne0\).

Such a leading repeat or zero is redundant for the
raw budget. Indeed the restricted prefix values of
any positive input or its clock marks are constant
at repeated \(r\) and zero at high zero; whenever a
primitive acts, all prefix values become zero, by
the total-tap equation. This remains true with all
other outer primitives and marks. Retarget later taps
of a deleted \(r\)-copy into the first host and add
its score there. A deleted leading high zero supplies
zero to all these words, and its score can move to
the opening origin for the scalar constant. This
preserves strict causality, the assigned surviving
clock diagonal, all exact short words and all scalar
moments. Thus any such deletion would contradict
the [rational pure width-ten theorem](../erk10-five-opening-plateau-endpoint/README.md).
Consequently the first two physical raw rows are
exactly \(r,h\), distinct and nonzero. The score of
the unscored host was not used to infer redundancy.

The second physical row has just one available
raw tap, and its actual formulas are
\[
 d_h=JP(h)/JP(r),\qquad
 B_{h,r}=\{J_h(F_2)-d_hJ_r(F_2)\}/F_2(r).
\]
This statement for the \(p\)-host refers to the erased
raw block, not elimination of the old physical
\(q\)-contact from the original tableau.

## Fixed q and free p give different literal probes

In the fixed-contact \(q\)-branch,
\(r=q=3ps/(2p-s)\) and
\(\alpha=P(p)/P(s)=p^2(3s-2p)/s^3\). Exactly
\[
 F=X(X-2r/3)\in U_0,\quad J_r(F)=0,\quad
 B_{h,r}=h^2(h-r)/r^2\ne0 .
\]
Indeed \(F(p)-\alpha F(s)=
-2p(p-s)(2pr-3ps-rs)/(3s^2)=0\).
In particular \(BEF=EJF\) at every raw row.
The free \(p\)-branch has \(r=p=3s/2\) and
\(k_o=q\). The only possible nonzero degree-at-most-two
positive model in \(\ker J_r\) is a multiple of that
same \(F\). But \(F(s)=0,F(q)\ne0\), so \(F\notin U_0\).
Thus the one-dimensional kernel of \(J_r\) in
\(U_0\) is genuinely cubic here. No corresponding
nonzero-tap assertion is made for this free branch.

## The third physical row and a rank-two prefix

The prefixes below mean the first chronological raw
forward rows. If the third clock is \(0,r,h\) and
the projection of \(V\) to the first three physical
rows has rank two, it is a redundant third row.
On the four models \(X,\ldots,X^4\), the first two
physical rows of \(T\) are \(-J_r\) and \(B_{h,r}E_r-J_h\).
The third is \(S E_r+T_1 E_h-J_x\). Independence of
\(J_r,J_h,E_r,E_h\) forces this read to be exactly
zero (for \(x=0\)) or exactly the earlier read of
the repeated clock. For a repeated row this equality
includes the tap to the intervening row: its
\(E_h\) coefficient must be zero; the raw tap to
\(r\) is zero or precisely \(B_{h,r}\), respectively.
Thus their positive word values agree not just on
polynomials but for all clock marks and primitives,
by induction. Delete the zero or duplicate as
above, contradicting the pure width-ten exclusion.
This argument applies to both old hosts.

If the third clock \(z\ne0,r,h\) and the first-three
projection of \(V\) has rank two, it must be
multicolor there: otherwise the single-color host
projection leaves two independent distinct-label
forward residuals in a line. Apply the
[rank-two prefix calculation](README.md#dimension-two-cannot-contain-a-multicolor-host-vector)
through the third debut (not the fourth) to that
projection, gauging the first column only as in that
calculation. The gauge does not affect the \(P\)-read,
because \(P(r)=0\). Normalize \(r=1\), put \(t=h/r\)
and \(\tau=t_0/r\), and compare the required
\(d_h=JP(h)/JP(r)\) to the prefix formula:
\[
 \frac{t^2(3t^2-4(1+\tau)t+6\tau)}{2\tau-1}
                  =-\frac{t^3(t-2)}{2t-1}.
\]
The cleared difference after cancelling \(t^2\) is
\(-6(\tau-t)(t-1)^2\). Both denominators are
nonzero on the guarded branch. Hence **the second
physical clock is the other root, \(h=t_0\)**.
This is a necessary branch, not a contradiction:
the third dirt value from the rank-two formulas
then matches \(JP(z)/JP(r)\) as well. In all other
cases the first three rows already detect all
three dimensions of \(V\).
