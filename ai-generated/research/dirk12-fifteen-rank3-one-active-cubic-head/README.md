# DIRK12/15: the first nonlocal weighted grade-four head when the cubic is localized

This is an exact restriction on the ordinary real fifteen-stage order-twelve \(C(2), f_5=3\) equality face with **exactly one active cubic-dirty label**. It does not exclude that face, even on the reverse-rank-five branch. No individual weight sign, no full reverse rooted order, and no deweighting of a zero-weight row are used.

Read the actual reversed physical stage order with reflected numerical clock \(\mathbf y=\mathbf 1-\mathbf c\) and its true lower triangular \(N=A^{\mathsf T}\) in this ordering. Put \(\mathbf W(P)=\mathbf b\odot P(\mathbf y)\) and let \(J\) be the primitive based at \(0\) in this reflected clock. The equality frame gives the two genuine leading primitive equalities
\[
          N\mathbf W(1)=\mathbf W(X),\qquad
          N\mathbf W(X)=\mathbf W(X^2)/2.
\]
The genuine nonzero reflected cubic is \(\mathbf G=N\mathbf W(X^2)-\mathbf W(X^3)/3\). The paid product of the forward cubic with \(T_8\) makes the nonzero weighted forward cubic proportional to \(\mathbf G\), since \(\mathcal B_3=\operatorname{Ann}T_8\) is a line. Thus \(\mathbf G\) is supported at exactly one numerical clock and is zero at every zero-weight coordinate, including any out-of-class ghost.

The first nonzero reflected clock \(d\) with a live physical row must be that unique supported clock, and \(d\ne0\). Indeed, before its first live occurrence, all live rows have clock zero. At that row the second leading equality forces the literal chronological diagonal \(d/2\), and the cubic read is \(b_i d^3/6\ne0\). There is a live nonzero clock different from \(d\), by the scalar quadrature count. Write \(v\) for the first such clock in physical reverse order and \(i_v\) for that actual row.

## A genuine head with an exactly known first support row

For each row before \(i_v\), only live source clocks \(0,d\) can contribute to \(N\mathbf W(P)\). The second leading equality fixes the aggregate weighted tap at \(d\) to be \(b_i y_i^2/(2d)\), including when the target row has zero weight. It follows that any live row of clock \(d\) before \(i_v\) has the same cubic amplitude \(G_i/b_i=d^3/6\), and the other earlier rows have \(G_i=0\). Therefore the true grade-four head
\[
                          \mathbf H=N\mathbf G-\frac d2\,\mathbf G
\]
is zero at **every physical row** before \(i_v\): a weighted target at \(d\) has \(N\mathbf G=(d/2)\mathbf G\) there, and targets of zero weight or clock \(0\) have both values zero. This uses the true aggregate taps, not deletion of any zero row.

At the row \(i_v\), put \(T_d=\sum_{j:y_j=d}N_{i_vj}b_j\) and define \(T_v\) in the same way (there has not been any earlier live row at \(v\)). The true leading linear and quadratic primitive identities there, using \(G_{i_v}=0\), give
\[
        T_d d+T_v v=b_{i_v}v^2/2,\qquad
        T_d d^2+T_v v^2=b_{i_v}v^3/3,
        \qquad T_d=\frac{b_{i_v}v^3}{6d(v-d)} .
\]
It follows that
\[
                       \frac{H_{i_v}}{b_{i_v}}=
                       \frac{d^2v^3}{36(v-d)}\ne0 .
\]
Thus \(\mathcal B_4=\langle\mathbf G,\mathbf H\rangle\). This also shows that \(\mathcal B_4\) is not simply the node-local cubic flag continued without a nonlocal primitive.

## The whole quartic primitive error is fixed in this basis

For the genuine weighted quartic error \(\mathbf E=N\mathbf W(X^3)-\mathbf W(X^4)/4\), the row of the first live \(d\) directly reads \(E_i/b_i=d^4/4\), so its coefficient of \(\mathbf G\) is \(3d/2\). At \(i_v\) the actual row reads zero on the nodal polynomial \(P=X(X-d)(X-v)\). The primitive is exact there on degrees through two, so \(E_{i_v}/b_{i_v}=-JP(v)=v^3(v-2d)/12\). These two genuine basis coordinates give the **global** weighted grade-four relation
\[
                      \mathbf E=\frac{3d}{2}\mathbf G+
                      \frac{3(v-d)(v-2d)}{d^2}\,\mathbf H.
\]
In particular the second head need not be obtained from the scalar quartic error alone when \(v=2d\); \(N\mathbf G\) still gives it with a nonzero first read.

The known outgoing weighted two-detector bound from an invariant grade-four space implies \(\mathcal B_4\) is not invariant under the clock (the actual next gain is one). Consequently \(\mathcal B_5=\langle\mathbf G,\mathbf H,Y\mathbf H\rangle\), where \(Y=\operatorname{diag}(\mathbf y)\).

Let \(u\) be the next live nonzero distinct clock after \(v\), different from \(d,v\). If all actual active cubic amplitudes at \(d\) **prior to its first live row** are still equal to \(d^3/6\), then the head does not vanish at this row \(i_u\). Indeed \(H_{i_u}=0\) would force the aggregate weighted tap to \(d\) there to be zero, because \(\mathbf G\) is that nonzero amplitude times the previous weights on its support. The true grade-five flag would vanish at \(i_u\) since \(G_{i_u}=H_{i_u}=0\), making the primitive exact on scalar inputs through degree four, now on only the live source clocks \(0,v,u\). The two tests \(X(X-v)(X-u)\) and its clock lift would give
\[
                   \int_0^u X(X-u)(X-v)X^j\,dX=0,\qquad j=0,1,
\]
which is impossible for nonzero \(u\) by the definite affine Gram after scaling to \([0,1]\). In applying the uniform-amplitude premise here, require it on **all previous live rows at clock \(d\)**, not just on previous rows where \(G_i\ne0\); later clean rows at that repeated numerical clock could otherwise still supply scalar taps. This premise is automatic through the first \(v\) but is an extra condition through \(u\).

The final grade-six extra head on the reverse-rank-five face is not resolved by this two-debut computation. The one-active-label and weighted-invisible branches remain open, as does the real stage interval **15–16**.
