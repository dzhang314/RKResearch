# Minimal strict adjacent layers can realize every endpoint beta moment over a real algebraic field

## Scope and choices

This note constructs the endpoint identities. The [separate rooted-tree implication](ENDPOINT-TO-ROOTED.md) turns them into full order at these exact widths. Fix p>=1, set the common diagonal gamma=0, and number layers backwards from the terminal output by h=0,...,p-1. Put
```
n_h = ceil((p-h)/2),     D_h = p-h-1.
```
These are the strict beta-Hankel minimum widths. We construct actual strictly triangular adjacent transitions from layer h+1 into layer h, with weights supported in layer zero and clocks equal to the actual row sums. The claim is exactly
```
b · ((1−c)^k ⊙ A^h c^a) / (k!a!) = 1/(h+k+a+1)!
                 whenever h+k+a+1 <= p.
```
No other tree condition, stability property, or rational attainability is asserted.

At layer h choose n_h distinct nodes x_(h,i) admitting quadrature through D_h for the rational functional
```
nu_h(f) = integral_0^1 (1-x)^h f(x)/h! dx.
```
For 0<=h<=p-2, the proposed nodes are the roots in (0,1) of the monic orthogonal polynomial of degree n_h for nu_h, i.e. shifted Jacobi nodes (Legendre at h=0). They are simple and real algebraic. Indeed, the orthogonality system has a nonsingular rational Gram matrix by positivity. If the orthogonal polynomial had fewer than n_h interior sign changes, multiplying by the product of those sign-changing linear factors would contradict its orthogonality and positivity of the weight. Its Lagrange weights give quadrature through degree 2n_h-1 by division by the orthogonal polynomial, and are positive by applying exactness to each squared Lagrange polynomial. In the earliest layer h=p-1, take the one node 0 instead: only degree zero is required there. Take b equal to the chosen quadrature weights at layer zero (for p=1 this is the single weight 1 at node 0). No other output weights are used. In fact the construction below works over any characteristic-zero field with the indicated distinct nodes and exact quadratures, provided terminal weights are nonzero.

## 1. Coordinate system and paid target prefixes

Let V_h be the invertible n_h-by-n_h evaluation matrix whose column a, 0<=a<n_h, is v_(h,a)=x_h^a/a! on the layer nodes. These are scaled Vandermonde matrices. On the terminal space use left coordinate functionals
```
L_k(y) = sum_i b_i (1-x_(0,i))^k y_i/k!,     0<=k<n_0.
```
They give an isomorphism by distinct terminal clocks and nonzero b weights. Later, F_h will denote the cumulative transition from the h-th layer to the terminal layer, with F_0 the identity. We first construct vectors
```
f_(h,a) = F_h v_(h,a),      0<=a<n_h,
```
in the terminal space. The paid requirement on f_(h,a) is the coordinate prefix
```
L_k(f_(h,a)) = 1/(h+k+a+1)!       for 0<=k<min(n_0,p-h-a).
```
That prefix always contains its first n_h entries, because p-h-(n_h-1)>=n_h. Hence the projection of the n_h vectors onto L_0,...,L_(n_h-1) is the square reciprocal-factorial Hankel matrix of rank n_h. To check this directly, multiply row k by (h+k+n_h)!; column a then consists of the values at k of a monic polynomial of degree n_h-a-1. The determinant is a signed Vandermonde times nonzero factorial factors. In particular all completed vectors at layer h will be independent.

## 2. Build nested cumulative images, then the actual transitions

Set f_(0,a)=v_(0,a). Its prescribed prefixes follow from terminal quadrature and the ordinary beta moments. Given the h-th vectors, copy
```
f_(h+1,a)=f_(h,a+1)
```
wherever a+1<n_h. These prescriptions have identical indices h+1+a=h+(a+1) and the same paid prefix length. If n_(h+1)=n_h-1, every new vector has been specified. On a width plateau n_(h+1)=n_h=n, one last vector remains, at a=n-1. A plateau means p-h=2n, so this vector needs exactly n specified coordinates. Choose the unique vector in span(f_(h,0),...,f_(h,n-1)) with those coordinates, using the invertible first-n coordinate projection verified above. Thus each new family has the correct prefixes, is independent, and has image nested inside the previous family's span.

Now define F_h on the basis V_h by F_h v_(h,a)=f_(h,a). It is injective and F_0 is the identity. By nesting, there is a unique linear map B_h from layer h+1 into layer h with
```
F_(h+1)=F_h B_h.
```
Use exactly these B_h as the non-diagonal blocks of A, and no other blocks. Its h-step terminal transfer is F_h by induction. This is a single adjacent tableau, not an uncoupled family of joint moments.

The actual clocks equal the prescribed nodes. Whenever n_h>=2, f_(h+1,0)=f_(h,1), so
```
F_h B_h 1= F_(h+1)1 = F_h x_h.
```
Injectivity gives B_h1=x_h. If n_h=1 and a next layer exists, then h=p-2 and the unique node in layer h is its degree-one quadrature mean 1/(h+2). The last plateau's one vector is placed in the previous line using its first coordinate: its prescribed value changes from 1/(h+1)! to 1/(h+2)!, exactly the multiplier 1/(h+2). Thus the same row-sum equality holds. The earliest row has no incoming transition block and zero diagonal, so its actual c is 0, as chosen.

## 3. Extend from basis prefixes to every paid endpoint pair

Consider arbitrary polynomials f,g of degrees k,a with h+k+a+1<=p. Their actual joint endpoint functional is
```
sum_(i,j) b_i f(x_(0,i)) (F_h)_(i,j) g(x_(h,j)).
```
The target is I[f J^h g], with I the integral polynomial functional on [0,1] and J the polynomial integral from 0 to X. For f=(1-X)^k/k!, g=X^a/a!, it is the stated reciprocal factorial. The prefix construction already gives equality when k<n_0 and a<n_h, and hence by linearity for basis combinations still obeying the degree sum.

For the general pair divide f and g by the respective monic node polynomials of the terminal and h-th layers, keeping their lower-degree remainders f0,g0. Actual evaluation is unchanged. The target is also unchanged:
- (f-f0) J^h g vanishes at all terminal nodes and has degree <=k+h+a<=p-1. Its integral is zero by paid terminal quadrature.
- To remove g-g0 from I[f0 J^h g], expand f0 in powers (1-X)^j for j<=k. The exact adjoint beta identity is
```
I[(1-X)^j J^h u] = (j!h!/(h+j)!) nu_h((1-Y)^j u(Y)).
```
It follows termwise on monomials by beta evaluation, also at h=0. For u=g-g0 the integrand in nu_h vanishes at the h-th nodes and has degree <=j+a<=D_h, so this term too is zero.

Both remainders have degrees no larger than the original degrees. Thus their basis evaluation falls inside the previously paid prefix rectangle/triangle and gives the exact endpoint value. This proves every claimed probe using its actual tableau and actual c=A1. The companion proof shows why these endpoint conditions suffice for the branching trees as well.
