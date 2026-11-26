# Endpoint probes force rooted order at the strict minimum width profile

This note proves the endpoint-to-rooted implication used in the [strict layered stage minimum](STRICT-LAYER-OPTIMALITY.md).

## Exact statement and payment

Work over a nontrivial commutative ring R with identity in which 1,...,p are units, for p>=1. Let A have zero physical diagonal, and label the physical layers backwards from terminal by h=0,...,p-1. All nonzero entries of A come from layer h+1 into layer h; let B_h be this block for 0<=h<p-1. The output weights are supported in layer zero. Write c=A1, x_h for its restriction to layer h, and use the exact physical widths
```
n_h=ceil((p-h)/2),      g_h=floor((p-h)/2),
D_h=p-h-1=n_h+g_h-1.
```
In particular the earliest layer p-1 has one stage and actual clock zero: its row has no predecessor block and its physical diagonal is zero. Neither coefficients nor weights are assumed nonnegative. No ordering or field structure is required.

Suppose precisely the strict normalized endpoint identities hold:
```
b · ((1−c)^k ⊙ A^h c^a) / (k!a!) = 1/(h+k+a+1)!
             (h,k,a >= 0; h+k+a+1 <= p).
```
Then all literal rooted-tree conditions through order p hold. This is a strengthening of the no-residual assertion for a single mixed split. It does not apply as written to shifted diagonal, skipped blocks, or a wider physical profile.

All powers on stage vectors are componentwise. Let F_h=B_0...B_(h-1), F_0=I on the terminal layer. Put omega_h=b^T F_h, and let L_j on the terminal space be the row b^T diag((1-x_0)^j)/j!. Introduce polynomial functionals J and nu_h by
```
J(X^a)=X^(a+1)/(a+1),
nu_h(f)=I[(1-X)^h f(X)]/h!,      I(X^a)=1/(a+1).
```
These are formal integrations, used only with the indicated factorials in the paid range. The exact beta value nu_h(X^a)=a!/(h+a+1)! follows by the polynomial endpoint identity I(U')=U(1)-U(0), or direct binomial expansion. Taking k=0 in the endpoint premise gives the pure quadrature
```
omega_h f(x_h) = nu_h(f)          when deg(f)<=D_h.
```

## 1. Local analogue of C(n_h-1), forced rather than assumed

The n_h-by-n_h square with entries L_k F_h x_h^a/a!, k,a=0,...,n_h-1, is fully paid because h+2n_h-1<=p. It is the reciprocal-factorial Hankel matrix 1/(h+k+a+1)!. Multiplying row k by (h+k+n_h)! gives in column a a monic polynomial in k of degree n_h-a-1. Hence its determinant is a signed Vandermonde in 0,...,n_h-1 times paid factorial units, so it is a unit in R.

This square factors as the first n_h rows L_k F_h times the layer evaluation columns x_h^a/a!. Both factors are square of size n_h, and each is invertible over R because their determinant product is a unit. No distinct-clock premise is needed.

For h<p-1 and 0<=a<=n_h-2 compare the h+1 endpoint of normalized degree a with the h endpoint of normalized degree a+1 through all those first n_h taps:
```
L_k F_h B_h (x_(h+1)^a/a!) =
  1/(h+k+a+2)! =
L_k F_h (x_h^(a+1)/(a+1)!).
```
All are paid at worst h+(n_h-1)+(n_h-2)+2=h+2n_h-1. The rows just shown invertible therefore force B_h integrate all polynomials through degree n_h-2 pointwise:
```
B_h f(x_(h+1)) = (Jf)(x_h)      (deg f <= n_h-2).
```
Equivalently the local Butcher analogue is B_h x_(h+1)^(k-1)=x_h^k/k for k=1,...,n_h-1. If n_h=1 this range is empty.

## 2. Paid dual tilts recover interior transport

Let Y_h(j)=diag((1-x_h)^j). For j<=g_h, test the row L_j F_h on each of the n_h normalized evaluation columns. All tests are paid because h+j+a+1<=h+g_h+n_h=p. By endpoint exactness the answer is 1/(h+j+a+1)!, while beta quadrature on the same column gives
```
omega_h Y_h(j) x_h^a/a! = (h+j)!/[h! (h+j+a+1)!].
```
The evaluation matrix is invertible, so this identifies the whole row:
```
L_j F_h = [h!/(h+j)!] omega_h Y_h(j)        (0 <= j <= g_h).
```
Combining adjacent instances via F_(h+1)=F_h B_h yields the actual interior transport
```
omega_h Y_h(j) B_h = (h+1)/(h+j+1) omega_(h+1) Y_(h+1)(j)
                         (j <= min(g_h,g_(h+1))).
```
The same ratio is the formal identity
```
nu_h((1-X)^j J f) = (h+1)/(h+j+1) nu_(h+1)((1-X)^j f),
```
by beta on monomials or by formal integration by parts. In the uses below h+j+deg(f)+2<=p, so this costs no additional factorial. This row equality, not positivity of the weights, is what transports the single non-pointwise branch.

## 3. Stage grade and the one high-branch induction

For a rooted tree tau write |tau| for its number of vertices. The stage response Phi_h(tau) has stage grade d=|tau|-1: a leaf is 1, and lifting each child eta by B_h adds one to its grade, giving child-factor grade |eta|. Their componentwise product produces Phi_h(tau). Formally define f_leaf=1 and f_tau as the product, over its children eta, of J f_eta. Then f_tau is homogeneous of degree d (or zero in the ring). Its integral is the literal exact coefficient 1/Gamma(tau), with Gamma(leaf)=1 and Gamma(tau)=|tau| times the product of the children's Gamma. The scalar output readout adds the root order; it is not another stage grade. Products of stage forest factors use the summed grades.

First prove pointwise exactness for grade at most n_h-1 by descending induction on layers. At h=p-1 the only grade under the cutoff is 0, so the leaf case is exact at its actual zero clock. At another layer, every child factor of grade less than n_h comes from a child response of grade <=n_h-2. Since n_(h+1)>=n_h-1, the child response is pointwise exact by induction. The local integration from Section 1 then makes that child factor exact at x_h. Multiplying proves Phi_h(tau)=f_tau(x_h) whenever the total grade is <=n_h-1. Importantly the reasoning for an individual low child factor remains valid even when its siblings give a higher total grade.

Now prove the weighted strengthening, again from earliest layer upwards:
```
omega_h [P(x_h) odot Phi_h(tau)] = nu_h(P f_tau)
            when deg(P)+(|tau|-1) <= D_h.
```
At h=p-1, D_h=0. The test is constant, tau is a leaf, and both sides equal that constant times 1/p! by pure quadrature. If every child factor has grade less than n_h, each is already pointwise exact and pure quadrature pays the weighted result.

Otherwise there is **only one** child eta of factor grade m=|eta|>=n_h: the total grade d<=D_h<=2n_h-1 cannot contain two such children. All other factors are pointwise exact. Multiply their formal polynomial factors into P to obtain Q of degree at most deg(P)+d-m. The allowed budget gives
```
deg Q <= D_h-m <= D_h-n_h=g_h-1 <= g_(h+1).
```
It also gives deg Q<=g_h. Expand Q into powers (1-X)^j, j<=deg Q. For any such j the corresponding actual term is omega_h Y_h(j) B_h Phi_(h+1)(eta); by the paid row identity it equals
```
(h+1)/(h+j+1) omega_(h+1) Y_(h+1)(j) Phi_(h+1)(eta).
```
The child grade is m-1 and j+(m-1)<=D_h-1=D_(h+1), so the weighted induction hypothesis applies to this term. The formal ratio converts it back to nu_h((1-X)^j J f_eta). Sum the Q coefficients to obtain the claimed equality. This treats every graft of a high branch inside the budget: there cannot be a second unintegrated sibling, and the remaining tap never exceeds either paid tilt depth.

At h=0 with P=1, omega_0 is the output weight row and nu_0=I. The result is b · Phi_0(tau)=1/Gamma(tau) for every |tau|<=p, exactly literal rooted-tree order.

For example the genuinely mixed family b · A^h[c^j odot A(c^a)], with j>=1 and h+j+a+2<=p, is therefore exactly (j+a+1)!/[(a+1)(h+j+a+2)!]. Its interior shift is not an independent residual once the exact minimum widths and all endpoint identities are imposed.

## Composition boundary

The [endpoint construction](STRICT-ENDPOINT-COUPLING.md) supplies
these actual blocks over a finite real algebraic coefficient
field. The implication proved here is independent of that
construction and holds over the stated ring. No rational,
nonzero-diagonal, skipped-layer, or unstructured stage conclusion
is claimed here.
