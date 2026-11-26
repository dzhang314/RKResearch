# The five-stage residual proof at every order

The order-five residual proof extends to show that an explicit method
of order \(p\ge5\) has at least \(p+1\) stages. This is a short proof
of an established bound. It applies to the factorial-cleared
rooted order conditions over any nonzero commutative unital ring.

Suppose a method of order \(p\) has at most \(p\) stages. Its tall
tree of size \(p\) requires a strict path of length \(p-1\), so it has
exactly \(p\) stages. The sole such path has product
\(b_p a_{p,p-1}\cdots a_{21}\). The cleared equation makes \(p!\)
and all factors of the product units.

Set
\[
 k\coloneqq p-5,\qquad
 L(\mathbf v)\coloneqq\mathbf b\cdot A^k\mathbf v,\qquad
 \ell_k(f)\coloneqq\int_0^1\frac{(1-x)^k}{k!}f(x)\,dx .
\]
The functional \(L\) ignores stages after 5. Its fifth coefficient
is the product of the last weight and the adjacent entries from
stage \(p\) back to stage 5; this product is a unit, including when
\(k=0\). Adding \(k\) unary roots to a tree of size at most five
gives a tree of size at most \(p\). Thus on a stage expression of
tree size at most five, \(L\) agrees with \(\ell_k\) on the formal
stage polynomial. This follows from \(k\) applications of
\(If(x)\coloneqq\int_0^x f(z)\,dz\), since
\(\int_0^1 I^k f=\ell_k(f)\). All these integrations are formal and
only use divisors of \(p!\).

Write \(C\coloneqq\operatorname{diag}(\mathbf c)\) and
\[
 \mathbf Q([\bullet])\coloneqq2A\mathbf c-\mathbf c^{\odot2}.
\]
The three vectors \(\mathbf c,\mathbf c^{\odot2},\mathbf Q([\bullet])\)
have zero first entry. The second entry of \(\mathbf Q([\bullet])\)
is the unit \(-c_2^2=-a_{21}^2\). The functionals
\[
 L_0(\mathbf v)\coloneqq L(A\mathbf v),\qquad
 L_1(\mathbf v)\coloneqq L(AC\mathbf v)
\]
depend only on stages 1–4 and both annihilate
\(\mathbf Q([\bullet])\), whose formal polynomial is zero. Their
matrix on the first two vectors is
\[
 \begin{pmatrix}
  1/(p-2)! & 2/(p-1)!\\
  2/(p-1)! & 6/p!
 \end{pmatrix}.
\]
Here \(\ell_k(x^j)=j!/(j+k+1)!\). The determinant
\(2(p-3)/((p-1)!\,p!)\) is a unit. Consequently the three vectors
form a basis upon restriction to stages \(2,3,4\): quotienting by
the third vector leaves a free module of rank two, and the
displayed determinant makes both composed square maps invertible.

Define
\[
\begin{aligned}
 D(\mathbf v)&\coloneqq L(A\mathbf v)
                     -\frac{1}{k+1}L((I_s-C)\mathbf v),\\
 G(\mathbf v)&\coloneqq L(A^2\mathbf v)
                     -\frac{1}{k+2}L(A(I_s-C)\mathbf v),\\
 H(\mathbf v)&\coloneqq D((C-c_5 I_s)\mathbf v),
\end{aligned}
\]
where \(I_s\) is the identity matrix. Both \(G\) and \(H\) ignore
stages 5 and later. Both annihilate the three vectors: the formal
identities are
\[
 \ell_k(If)=\frac{\ell_k((1-x)f)}{k+1},\qquad
 \ell_k(I^2f)=\frac{\ell_k(I((1-x)f))}{k+2}.
\]
The basis therefore gives \(G(\mathbf e_4)=H(\mathbf e_4)=0\),
where \(\mathbf e_4\) is the fourth coordinate vector. The first
equation gives \(c_4=1\), as its left side is
\(-L(\mathbf e_5)a_{54}(1-c_4)/(k+2)\).
The second equation then gives \(c_5=1\), since its left side is now
\((1-c_5)L(\mathbf e_5)a_{54}\).

Strict triangularity makes the first three entries of \(A^2\mathbf c\)
zero. The next two entries are killed by \(I_s-C\), so
\(L((I_s-C)A^2\mathbf c)=0\). Its formal value is instead
\[
 \ell_k\!\left((1-x)\frac{x^3}{6}\right)=\frac{p-4}{p!},
\]
a unit. This is the contradiction.

At \(p=5\) the weight in \(\ell_k\) is constant and the matrices and
residuals are exactly those of the usual five-stage proof. The
unit argument is what permits the same calculation over rings with
zero divisors. This note does not add a Lean certificate.
