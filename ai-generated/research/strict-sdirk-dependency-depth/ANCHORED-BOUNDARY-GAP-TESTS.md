# A separate boundary-product obstruction for even shorter anchored runs

Source-only mathematical companion. This is a structural result only;
no lower all-chart threshold is claimed from it. Work in the cyclic
nonzero-diagonal degenerate rectangle chart at \(s=p\ge8\), with
the actual nonzero step \(\delta=-E/D\), \(t=\delta/\gamma\), and both
literal arithmetic endpoint runs given by the factorized rectangle.
If all prefix slopes coincide the long-prefix result applies separately;
here use the two-run case.

## 1. The last clock is complementary

The literal first clock is \(c_1=\gamma\). The tail equation
\(x_s=\delta(s-3)-H/D\), where \(x_s=c_s-\gamma\),
also forces \(c_s=1-\gamma\).
Here is a scalar check. Let \(n=s-2,\ z=\gamma^{-1}-2\)
and use \(m_k\) for the normalized reverse tall moments.
The scalar recurrence gives
\[
  n k_0=z m_1-2,\qquad (n-1)l_0=z m_2-2m_1,
  \quad k_0=1+2m_1+m_2,\quad l_0=m_1+2m_2+m_3 .
\]
In normalized units \(e_0=m_1k_0-l_0=\gamma E/L^2\),
\(d_0=m_2-m_1^2=\gamma^2D/L^2\), and
\(h_0=m_1 k_0=\gamma H/L^2\).
The displayed scalar equations yield
\((n-1)e_0+h_0=-z d_0\) by substitution.
Since \(e_0/d_0=-t\), this means
\(H/(\gamma D)=(n-1)t-z\).
Dividing the tail equation by \(\gamma\) gives \(x_s/\gamma=z\),
which is the asserted complementary last clock.

## 2. Both endpoint omissions can be isolated without global clocks

Suppose the leading prefix and trailing suffix arithmetic runs have at
least \(j+1\) and \(k+1\) clocks respectively. Take paths omitting \(h=j+k\)
stages, retaining \(m=s-h\ge1\).
At the first occupied stage use the mark
\(\prod_{i=0}^{j-1}(C-\gamma-i\delta)\) and at the last use
\(\prod_{i=0}^{k-1}(1-\gamma-C-i\delta)\).
If fewer than \(j\) holes are leading, the first mark is zero
by its local run; if fewer than \(k\) are trailing, the last
mark is zero by its local run. Any endpoint overrun therefore
forces a zero at the other endpoint. The unique possible
surviving allocation has exactly \(j\) leading and \(k\)
trailing holes and no internal ones. Its weight factors into
the two normalized actual boundary intervals times \(L\);
leading and trailing edge replacements remain disjoint even
if a retained endpoint is shared. This uses no clocks in
either unresolved middle row.

For the formal model define \(H_j(y)\) by
\[
 \prod_{i=0}^{j-1}(X-\gamma-i\delta)1
           =j!T^jH_j(\gamma/T)1,\qquad T=J-\gamma I .
\]
Here ordinary powers of the variable on the left are represented
by \(X^a1=a!J^a1\). The raw single leading mark divided by \(Lj!\) gives \(\mu(H_j)\). Dividing it instead by \(L\delta^j j!\) gives the actual normalized interval weight \(\delta^{-j}\mu(H_j)\).
The trailing model is its exact reflected adjoint.
Indeed the formal polynomial pairing is \(\ell(fg)\);
\(J^\ast f(x)=\int_x^1 f(u)\,du\) by the double-integral identity,
and reflection \(f(x)\longmapsto f(1-x)\) conjugates \(J\) to
\(J^\ast\). The reflected leading mark is precisely the
trailing one since \(c_s=1-\gamma\). Thus the trailing mark
polynomial applied to 1 is \(k! (T^\ast)^k
H_k(\gamma/T^\ast)1\), with the expression understood after
clearing powers. Move this polynomial operator by adjoint
onto \(T^{m-1}\) and the leading model. The product is
\(j!k!T^{s-1}H_j(\gamma/T)H_k(\gamma/T)\), since
\(j+k+(m-1)=s-1\). This argument is algebraic over characteristic
zero and requires no order on the field. By the actual
factorization and separate single calibrations,
\[
                    \mu(H_jH_k)=\mu(H_j)\mu(H_k)
\]
is paid exactly at \(p=s\). The relevant formulas by
expansion are \(H_2=(1+F_1)/2\) and
\(H_3=(1+3F_1+2F_2)/6\), with the same internal-gap
polynomials as the companion proof.

## 3. Consequences in the chart

Let \(q=F_1-\mu(F_1)\), so the degenerate chart has
\(\mu(qP)=0\) for \(\deg P\le2\), and
\({\cal D}=\mu(y^2)-\mu(y)^2\ne0\).
If \(t\ne2/3\), \(H_3\) has nonzero cubic coefficient.
A pair of anchored end runs of lengths at least 4 and 3
(in either order) pays the boundary \((3,2)\) test,
which is \(\mu(qH_3)=0\) since \(H_2=(1+F_1)/2\).
This supplies \(\mu(q y^3)=0\), contradicting the
same fixed reverse quadratic recurrence as in the main proof.

If \(t=2/3\), both \(H_3\) and \(F_2\) have degree two,
and \(F_2-\tfrac{13}{9}F_1=-\tfrac49+\tfrac{2}{27}y\).
Hence \(H_3-\mu(H_3)\) is a linear combination of \(q\) and
\(y-\mu(y)\) with nonzero coefficient of the latter.
Its squared moment equals that nonzero coefficient squared
times \({\cal D}\), by the radical identities for \(q\).
If both end runs have length at least four, the boundary
\((3,3)\) test instead makes this squared moment zero,
a contradiction. This handles two shorter anchored runs
even at the exceptional slope. It does not cover every other
short-run shape and is not a stage-count endpoint by itself.
