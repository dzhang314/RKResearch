# Exact cancellation proof for the seven-site control

## Scaled prefix and literal primitive defect

The [rational nine-row prefix and decoder](prefix.json) are the existing nine-row readout of the [universal sixteen-stage order-nine splice](../../../research/erk-nine-moment-splice/README.md). Denote its explicit matrix by \(A_0\), and its degree-four decoder by \(\Pi_1\). The four old readouts at \(1\) are the literal origin and endpoint values and the two old output moments; the ninth row is the literal half-port. The rational replay checks, on actual rooted derivative vectors, all statements about the prefix used here.

Scale \(A_0\) by the nonzero parameter \(\xi\), and in degree \(j\) scale the decoder coefficient by \(\xi^{-j}\), giving \(\Pi_\xi\). Rooted homogeneity gives the following facts for
\[
     \rho_t=g_t-\Pi_\xi\boldsymbol\Phi_t^{\rm old},
     \qquad  g_t(X)=\frac{|t|}{t!}X^{|t|-1}.
\]
It vanishes identically at sizes through five. It vanishes at \(\xi\) at sizes six and seven. At size six it belongs to
\[
  \mathcal H_6
   =D(X)\langle 1,X(X-\xi)\rangle,\qquad
        D(X)=X(X-\xi)(X-\xi/2).
\]
In particular \(J\rho_t(\xi)=0\) for size six, where \(J\) integrates from zero: both spanning polynomials are odd about \(\xi/2\). The decoder evaluates exactly on the old literal rows \(0,\xi,\xi/2\) for **arbitrary** prefix vectors, and its primitive at these three clocks equals their whole literal incoming row. These are finite rational row identities at \(\xi=1\), transported by the displayed scaling; they are not merely nominal polynomial moments. The rational prefix certificate checks all reviewed tree vectors through the stated sizes.

Use the eight virtual high physical labels in reverse order
\[
  \boldsymbol x=(1,\xi_{\rm donor},v,w,z,\xi/2,\xi_{\rm old},0).
\]
Here both marked \(\xi\)'s denote that same scalar clock. The high output masses below are all nonzero. The weighted transpose of an explicit reverse array \(L\), after reversing the labels, is the high strict block \(B\): in common, unpermuted labels its entries are \(B_{ij}=w_j L_{ji}/w_i\). Forward rows use the literal cross part \((EJ-BE)\Pi_\xi\), where \(E\) evaluates on the forward high labels, and \(Jf=\int_0^X f\). Hence the primitive error from an actual size-\(n\) source \(t\) is exactly
\[
 B\,(\boldsymbol\Phi_t^{\rm high}-Eg_t)
       +(BE-EJ)\rho_t .
\]
In particular the inhomogeneous source is zero through size five.

## Degree-nine positive quadrature and the one algebraic equation

Start from the seven distinct scalar sites \(0,1,\xi,\xi/2,v,w,z\); give each its unique interpolatory mass \(\bar w_i\). For each \(\xi\), choose \(v,w,z\) as the three cubic roots of \(R_\xi\) whose coefficients are explicit rational functions in fixed.py. The three exact orthogonality identities
\[
 \int_0^1 X^k (X-1)D(X) R_\xi(X)\,dX=0,\qquad 0\le k\le2
\]
are checked as rational polynomial identities by clearing the one shown coefficient denominator. Division by the monic seven-node hull proves scalar precision nine. In the chosen branch, the cubic has three distinct real roots strictly between 0 and 1, all distinct from the fixed sites. The exact root bracket in the replay proves all seven masses positive. Split the mass at \(\xi\) equally between its two high labels; write \(\mathbf w\) for the eight physical weights in reverse chronology.

Write \(y_i=1-x_i\), \(r=1-\xi,\ V=1-v,\ U=1-w\) and \(Z_i=x_i(x_i-\xi)\). Let \(K_i=\bar w_iD(x_i)\) on the three clocks \(v,w,z\). These numbers may be computed without using the root weights explicitly: apply the formal integral against \(D(X)\) to the four degree-three Lagrange cardinals on \(1,v,w,z\). Exactness of the seven-site scalar rule and \(D(0)=D(\xi)=D(\xi/2)=0\) give precisely \(K_i\).

Choose the isolating mesh with \(\xi=0.49458772634688659450954\ldots\),
\(v=0.07117297253386344833372\ldots\),
\(w=0.92353731030817331137495\ldots\), and \(z=0.74311623316132304391339\ldots\), by imposing the one extra equation
\[
       K_v(Z_z-Z_v)V^3
       -K_w(Z_w-Z_z)U^2(3V-2U)=0.                     \tag{1}
\]
All denominators used below are bounded away from zero on the isolating box. The directed rational checker proves opposite signs of the left side at the two rational endpoints of the \(\xi\) interval, and a nonzero derivative on the whole interval along the same three distinct simple cubic root branches. Thus it has a unique zero there. Its real coordinates are algebraic: the zero is a root of the nonzero constant coefficient of a polynomial over \(\mathbb Q[X]\) satisfied by the algebraic function of \(\xi\) in (1). Indeed its irreducible polynomial over \(\mathbb Q(\xi)\) has nonzero constant coefficient because the function is not identically zero, and one may clear denominators and use continuity. The other coordinates are roots of the resulting cubic over this algebraic field.

## Assign the actual reverse array

Impose \(L\mathbf1=\mathbf y\) and define the three actual defects by
\[
 \mathbf u=L\mathbf y-\mathbf y^{\odot2}/2,\qquad
 \mathbf g=L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad
 \mathbf h=L\mathbf u.
\]
Set \(u_{\xi_{\rm donor}}=u_*=-r^2/2\), \(u_{\xi_{\rm old}}=-u_*\), and all other \(u_i=0\). The first reverse row at 1 is zero. The second, at \(\xi_{\rm donor}\), reads the first alone with coefficient \(r\). Thus both the row sum and its stated \(\mathbf u\) value are actual. The next row at \(v\) reads the first two; its coefficient on \(\xi_{\rm donor}\) is \(V^2/(2r)\), with row sum \(V\). This gives
\[
 h_v=-rV^2/4,\quad g_v=rV^2/2-V^3/3,\quad
 \gamma=g_v/h_v=-2+4V/(3r).
\]
Choose \(h_w,h_z\) to satisfy the two true moment cancellations
\[
   K_vh_v+K_wh_w+K_zh_z=0,\qquad
   K_vZ_vh_v+K_wZ_wh_w+K_zZ_zh_z=0.
\]
The \(Z_i\) are distinct in the verified branch. Set \(g_w=\gamma h_w,\ g_z=\gamma h_z\). At \(w\) there are only the first three donors. Its \(h_w\) determines the tap \(h_w/u_*\) on \(\xi_{\rm donor}\); then its \(\mathbf y\) moment and row sum determine the other two taps. The resulting
\[
  g_w=VU^2/2-U^3/3 + h_w\,r(r-V)/u_*
\]
equals \(\gamma h_w\) exactly because (1) is \(h_w/h_v=(U/V)^2(3-2U/V)\). At \(z\) and the later labels there are four donors \(1,\xi_{\rm donor},v,w\). Their four vectors \(\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u\) are independent there (isolate the nonzero \(u_*\), then interpolate at the distinct \(0,V,U\)). The four prescribed actions therefore solve the literal row. At \(z\) take the calibrated \(g_z,h_z\); at all labels after \(z\) take both zero, using the already prescribed \(\mathbf u\) values. All incoming rows are strict. It follows that \(\mathbf u\) is supported only at the same-clock \(\xi\) pair and has zero aggregate, and that
\(\langle\mathbf g,E f\rangle_{\mathbf w}=\langle\mathbf h,E f\rangle_{\mathbf w}=0\) for \(f\in\mathcal H_6\). Any \(\mathbf g\) value on the first \(\xi\) is allowed, since that entire source space vanishes there.

## Every actual rooted equation through nine

Any first primitive error has source size at least six and enters above one edge. Two such errors cannot meet in a rooted tree of size at most nine. Expanding the actual Butcher product, each error is a linear combination of single inhomogeneous primitive seeds \((BE-EJ)\rho_t\) followed by words of length at most \(8-|t|\) in \(B\) and multiplication by the clock. This is precisely the reviewed paid-defect bridge, with cutoff five and seven eligible word patterns. Moving a word to the weighted reverse side gives an actual row \(\mathbf a\) (applied to \(\mathbf1\)) and its scalar model \(f\). For a source \(\rho\) the corresponding scalar payment is
\[
 \langle L\mathbf a-EJ^* f,E\rho\rangle_{\mathbf w}
       -\langle\mathbf a-E f,EJ\rho\rangle_{\mathbf w},
        \qquad J^* f(X)=\int_X^1 f ,
\]
by exact quadrature and formal integration by parts. Polynomial degrees are within the paid scalar rule.

For the empty word, \(L\mathbf1=\mathbf y\) gives zero. For the two one-letter words, \(\mathbf a=E X\) or \(E(1-X)\), and the only discrepancy is \(\pm\mathbf u\), which has zero aggregate. For the four two-letter words, size six is the only eligible source. The first discrepancy in the displayed payment belongs to the span of \(\mathbf u,\mathbf g,\mathbf h\), by expanding \(X=1-y\); the second belongs to the span of \(\mathbf u\). For instance after two reverse primitive letters \(\mathbf a=\mathbf y^{\odot2}/2+\mathbf u\); its two discrepancies are \(\mathbf g/2+\mathbf h\) and \(\mathbf u\). The other three words yield \(\mathbf g-2\mathbf u\), \(\mathbf u-\mathbf g\), or \(\mathbf u-\mathbf g/2-\mathbf h\) for the first discrepancy, and \(0,0,-\mathbf u\) for the second. All are paid by the moment identities above and the anchored size-six source space. Consequently every actual rooted error vanishes through order nine.

## Three physical merges and a strict next-order witness

In forward chronology the first three virtual high rows have clocks \(0,\xi_{\rm old},\xi/2\). Their high block rows are zero, because in reverse chronology they are never donors. Their prefix rows are exactly \(J_0\Pi_\xi,J_\xi\Pi_\xi,J_{\xi/2}\Pi_\xi\), equal to the literal prefix incoming rows with one-based indices \(1,8,9\). In that order redirect **every** subsequent tap on each of the three virtual rows into its indicated earlier physical row and transfer its weight. They contract 17 virtual to 14 physical rows, preserving every rooted scalar output and strictness. At other old rows, including past clock-\(\xi\) stages 5 and 7, weights start and remain zero; they never enter an inverse. The moved weight only goes to stage 8 at the old \(\xi\), and stages 1 and 9 get the origin and half-port masses. The new \(\xi_{\rm donor}\) is a distinct literal row, and retains its own half share. Every remaining whole row is pairwise distinct by a directed replay. The cleared tenth tall defect is rigorously inside \((-4,-3)\), hence order is exactly nine.
