# Reoptimized rational point-merge control at thirteen physical ERK rows

A genuine change to the [rational fourteen-stage order-nine witness](../erk9-fourteen-rational-triple/README.md) makes one high row **literally identical** to an old row. It gives a rational **thirteen-stage method of exact order eight**, not order nine. Its scalar quadrature remains exact through degree eight, so the failure at order nine is a rooted effect rather than scalar underpayment. All 200 rooted tests through eight pass; 117 of the 286 size-nine tests fail, including the ninth tall tree with normalized defect \(-1731249/24500000\). This lower-order construction is a control, not an improvement over the eleven-stage ERK8 optimum.

The reverse proof below explains why even reoptimizing the high taps within this particular point-merged architecture cannot make order nine. It does **not** assume an individual \(D(1)\) identity or a fixed high numerical matrix. It does not exclude arbitrary rational thirteen-stage tableaux, and the rational ERK9 interval remains **13–14**.

## Actual reoptimized prefix, right before the physical merger

Keep the rational high scalar nodes and the demonstrated reverse high block of the fourteen-stage source. Replace the actual old prefix by the six canonical clocks \(0,1/10,16/75,8/25,7/10,4/5\), with new \(p=8/25,\ q=7/10,\ r=4/5\). Put the free old donor tap \(f=512/1995\), so the literal \(r\) row uses only \(0,p,q\) and pays all moments through \(X^3\) (the coefficient onto the rough \(16/75\) stage is exactly zero). In particular that row is literally \(J_r\Pi\), not just equal through a few tree sizes, and the true size-five source space is \(H_5=X(X-r)\mathcal P_2\).

Rebuild the actual high-to-old cross rows \((EJ-BE)\Pi\) with this new prefix. The high row at \(x=4/5\) has no earlier high tap in the original signed-triple tableau; its reverse column receives none either. Thus the rebuilt high row is literally the actual old \(r\) row. Combine its weight and every later tap into the old \(r\) row and remove the duplicate. This leaves thirteen distinct strict rows, keeps all scalar moments, and generates the exact rational file in this directory. The independent replay checks all rooted conditions to size nine and counts the failures.

## Why retuning this merge does not reach order nine

The scope is the literal canonical cubic point-merge architecture used for the control: the same type of six opening rows with a point \(r\) having \(A_r=J_r\Pi\), one high row that duplicates it exactly, and seven further high rows. The six high scalar sites before merging are endpoint \(1\), the duplicate anchor \(r\), one interior triple, and three interior singleton sites. All five interiors are distinct from each other and \(0,1\); the last forward row is the endpoint \(1\). Only the old origin is scored before transferring the duplicate weight. All physical shares in the triple and all contributing group masses are nonzero; they may have arbitrary signs. No restriction on which proper nonanchor groups appear first in reverse is needed, and the high strict matrix is arbitrary subject to the anchor duplicate row and the literal cubic cross block.

Re-expand the duplicate for the argument and take the raw transpose \(T\) after physical reversal, high weight column \(\mathbf w\), and \(Y=\operatorname{diag}(1-x_i)\). The raw \(T\) **column** of the anchor is zero since its forward \(B\) row is zero. Thus the anchor never acts as a scalar or defect donor in the reverse moment equations, even if its chronological location changes. Define
\[
\begin{aligned}
 \mathbf U&=T(Y\mathbf w)-Y^2\mathbf w/2,&
 \mathbf G&=T(Y^2\mathbf w)-Y^3\mathbf w/3,\\
 \mathbf H&=T\mathbf U,&
 \mathbf K&=T(Y^3\mathbf w)-Y^4\mathbf w/4,\qquad
 \mathbf V=\mathbf G/2+\mathbf H .
\end{aligned}
\]
These definitions do not require \(T\mathbf w=Y\mathbf w\).

For true order nine, use the [anchored contrast identity](../erk149-two-pair-point-collision/README.md): actual fresh drives in a unary or clock word vanish at \(0,r\). They have degree bounded by the current tree grade. At a direct source the actual contrast is its scalar drive evaluated at the high nodes. Direct sources through sizes six, seven, and eight contain \(X(X-r)\mathcal P_3\), \(X(X-r)\mathcal P_4\), and \(X(X-r)\mathcal P_5\), respectively: the three size-five directions plus the higher direct bushes. On the four proper nonanchor interiors each of these spaces separates all four locations. Errors from a reverse word with a primitive vanish at the actual endpoint \(y=0\).

Consequently, starting at reverse word length one, **every** word error of length at most three is forced to have zero grouped value at each of the four proper interior sites. The proof is induction on word length. The empty comparison uses exact scalar quadrature; once shorter errors are grouped only at \(r\), they kill every subsequent fresh drive. Thus one isolates the current word error on its direct size-\(\le9-\ell\) sources at length \(\ell\). For \(\ell=1,2,3\) these sources separate the four proper sites. In particular \(T\mathbf w-Y\mathbf w\) need not vanish individually, but it has the required grouped vanishing off the anchor. The words \(TY,\ TY^2,\ T^2Y\) on \(\mathbf w\) give grouped \(\mathbf U,\mathbf G,\mathbf H\) zero there, using
\[
 T^2Y\mathbf w=Y^3\mathbf w/6+\mathbf G/2+\mathbf H.
\]
A letter \(Y=I-C\) is the difference of identity and a true root clock mark, so these are paid by actual root words with the same size budget.

At length four the sources are \(H_5\), which has rank three on the four proper sites. The word \(TY^3\) gives \(\mathbf K\), and \(T^3Y\) gives \(\mathbf K/6+T\mathbf V\) as the error. Hence the two proper grouped columns \(\mathbf K,T\mathbf V\) are in a common annihilator of dimension at most one. This argument uses real root conditions, not an imposed co-order family.

Let \(a\) be the reversed \(y\) clock of the triple. The first proper complete contributing group cannot be the triple: its exact first two scalar reverse moments would have support at only the one earlier nonzero site \(a\) and target \(a\), whereas those moments require a target \(3a/2\). The first proper complete group must be a singleton \(t\). It must use both first triple donors, since the first has nonzero \(U_1=-w_1a^2/2\) and \(\mathbf H\) must be zero at the singleton. Thus \(t=3a/2\); before it the only effective weighted scalar donor apart from endpoint is \(a\). On those first two triple donors,
\[
                 V_i=-w_i a^3/6 ,
\]
because the actual tap part of \(\mathbf G/2\) at the second cancels \(T\mathbf U\). This uses no full \(D(1)\) assumption. At the first and second proper complete target, only these first two triple donors can be read by the comparing rows: the third triple row is itself a completion and cannot be its own donor. A prematurely occurring anchor still cannot be used, since its \(T\) column is zero. The singleton \(t\) has \(V=0\).

Normalize each completed group by its nonzero total weight, and let \(\mu_a\) be its real scalar tap total at the early triple clock. At both completions \(T\mathbf V/(-a^3/6)\) is \(\mu_a\). At the first completion \(K(t)/\mu_a(t)=-a^3/8\). The second proper target \(s\ne t\), using only \(0,a,t\) as earlier scalar support, must therefore satisfy
\[
               K(s)+(a^3/8)\mu_a(s)=0
\]
by the rank-one cap. The actual first two moments instead give the [checked exact remainder](../erk149-two-pair-zero-shares/README.md)
\[
           K(s)+(a^3/8)\mu_a(s)
                              =-s^2(2s-3a)^2/16\ne0.
\]
This excludes order nine in the stated point-merged shape, while the literal rebuilt test reaches order eight. A nonpoint merge, independent shape with another protected clock, or earlier stage leakage is not covered.

## Reproduction

From ai-generated:

    src=research/erk9-fourteen-rational-triple/tableau.json
    root=research/erk13-rational-point-merge-control
    python3 -B "$root/rebuild.py" "$src"
    (cd "$root" && sha256sum -c sources.sha256)

The exact replay and fixture are self-contained given the published source JSON. The scalar one-site and second-completion identity already have Lean field proofs in the linked raw transpose module; neither the complete control nor the full point-merge exclusion is claimed to be newly formalized here.
