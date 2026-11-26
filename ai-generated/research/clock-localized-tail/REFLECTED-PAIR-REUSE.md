# Two actual reflected clocks can reuse old common-diagonal stages

The paired reverse-word construction distinguishes three things: a scalar owner row, an older reference (minus) row, and a reverse-fed plus row. An older reference need not be a scalar owner or have the same incoming coefficients as a pure owner. It only needs the same physical clock as its plus, with the paid short primitive factors. This distinction permits two literal stage reuses at a free common diagonal. No stronger donor decoder is assumed.

## 1. The exact chronology gate

Keep the reflected packing of the simultaneous paired tail, at target order \(p=m+r\) with \(r\le m\). In an active product at the root, a large child has size at least \(m\). Thus the total sizes of the other children are at most \(r-1\). A prefix stage at clock \(a\) can therefore serve as the minus reference for a plus at \(a\) whenever its shifted primitive coincides with the exact polynomial primitive for all children of size at most \(r-1\). It suffices for the prefix stage to have actual local derivative order at least \(r\). Copy its entire old strict row to the plus and add the usual zero-sum earlier contrast taps. No tap into a later row is allowed. The low sibling factors then coincide, and the contrast recurrence and source decoder are unchanged. This is rebasing a **pair** onto an older row, not merging two previously computed rooted columns merely because they agree at the clock. The pure scalar owner array and its interpolation are unchanged.

Use the known cached Laguerre donor at grade \(m-1\), and a cached reverse donor at grade \(r\), both with the same nonzero diagonal \(\gamma\). At any physical root of the level-\(k\) Laguerre clock polynomial, the cached row really has local derivative order at least \(k+1\). The full cached profile's error at size \(k+1\) is a multiple of that level's monic polynomial, hence vanishes at the chosen root; all lower sizes have no error. If the global cache is paid only through size \(k\) at its last level, the actual row at size \(k+1\) still equals this sample: the recursion at that row uses only child columns through size \(k\), including the child on its diagonal. No assertion of reconstructing the whole next polynomial is needed. Expanding the diagonal shift transports the same local conclusion to shifted columns and their primitives. This is the literal chronology used below.

At a normalized earlier Laguerre clock \(a\) from level \(k\ge r-1\), and a chosen normalized reverse clock \(b\), reflection makes the two physical labels coincide exactly when
\[
                \gamma a=1-\gamma b,
                \qquad\text{equivalently}\qquad \gamma=1/(a+b).
\]
For the actual selected rows, this is a necessary and sufficient clock condition for this way of reusing that older row; the short-primitive hypothesis and chronology are separate requirements. In particular a negative common diagonal cannot give this coincidence between the two Laguerre caches. The first reverse stage reflects to \(1-\gamma\), not the ordinary ERK endpoint 1.

## 2. Choose a reflected pair, and all remaining required clocks lie on one side

Assume \(r\ge2\) and \(m\ge r+1\). Let \(a\) and \(b\) be the largest roots of the ordinary normalized Laguerre polynomials of degrees \(r-1\) and \(r\), respectively. Choose both roots in both physical caches. Every relevant level has at least one allocated clock, so this costs no row and uses only the established freedom of choosing distinct roots at the level. All other reverse normalized clocks are less than \(a\): the last level has only its one selected root \(b\), the other roots at level \(r-1\) are less than \(a\), and maximal roots strictly increase with the degree by the three-term recurrence and positivity of its subdiagonal coefficient. Set
\[
                               \gamma\coloneqq\frac1{a+b}>0.
\]
The actual forward rows at \(\gamma a\) and \(\gamma b\) are both eligible at paid order \(r\). The reflected reverse plus clocks \(1-\gamma a\) and \(1-\gamma b\) are exactly these two rows in the opposite order. They require no scalar-grid pin and no new minus row. Every other required reflected position is strictly between \(1/2\) and 1, because its normalized reverse value is less than \(a<b\). Use ordinary separate scalar owners for the remaining mandatory clock positions. This does not move any of the scalar owners into the donor.

Write \(d\) for the number of distinct reflected reverse labels and \(d_0=d-2\) for the remaining pin count. Let \(\Omega\) be their monic nodal polynomial. If \(d_0>0\), its integral is nonzero. Indeed, for each pinned \(\xi>1/2\) and \(0<x<1/2\),
\[
                         |1-x-\xi|<|x-\xi|.
\]
Thus \(\Omega(x)+\Omega(1-x)\) has the fixed sign \((-1)^{d_0}\); integrate over the half interval. The empty hull has integral one. Consequently:

* With \(q=\max(p,d_0)\) owners one can always arrange precision \(p-1\) and fail the degree-\(p\) scalar moment. If \(d_0\le p\), choose \(p-d_0\) distinct free rational nodes so that the integral of their product with \(\Omega\) is nonzero. The integral is a nonzero polynomial in the trial nodes: making all trials equal to one large formal variable shows leading coefficient a nonzero multiple of \(\ell\Omega\). Distinctness and the required avoidance are open polynomial inequalities. The interpolation rule on the full \(p\)-node hull proves the claim. If \(d_0>p\), prescribe the first \(p\) moments and set the next moment to zero using any \(p+1\) of the pins; place zero aggregate mass at the others.
* If \(d_0\le p-2\), only \(q=p-1\) owners are needed for precision \(p-1\). First add \(q-d_0-1\) distinct rational pins in \((1/2,1)\), avoiding the existing ones, and call the resulting exact hull \(\Omega_1\). It has degree \(q-1\), with every root above \(1/2\). The final rational-over-the-pins site is \(z=\ell(X\Omega_1)/\ell\Omega_1\). It is below \(1/2\): after normalizing the left sign, pair \((X-1/2)\Omega_1\) across the two halves and use the strict preceding pointwise magnitude inequality. It is therefore distinct from all the other sites. The full monic hull \((X-z)\Omega_1\) has zero integral, which pays one more degree than the ordinary interpolatory range. Exact order in this second branch can be established by the tall witness below. No positivity of the output weights or of the signed rule itself is needed.

These choices involve only real algebraic numbers when the donors do. The scalar-grid width automatically stays at least \(m-1\), and all primitive adjoints retain the degree budget of the original paired word construction.

## 3. The degree-\(p\) shifted tall scalar cannot accidentally vanish at this diagonal when \(r(r-1)>p\)

Use the ordinary Laguerre irreducibility already established in `CAUSAL-RECEIVER-CUT-AND-MINIMAL-CACHE.md` (parameter zero only). The degrees of \(a,b\) are the coprime integers \(r-1,r\). Therefore \(\mathbf Q(a,b)\) has degree \(r(r-1)\): both degrees divide it and their product bounds it above. Its embeddings realize all pairs of conjugates of \(a,b\). The largest real sum among those pairs occurs exactly once, since both chosen roots are the unique largest conjugates and all conjugates are real. In characteristic zero every embedding of \(\mathbf Q(a+b)\) has the same number of extensions to \(\mathbf Q(a,b)\). Hence that number is one, and
\[
                              [\mathbf Q(a+b):\mathbf Q]=r(r-1).
\]
No irreducibility of a generalized Laguerre polynomial is being assumed.

The formal shifted tall scalar at the next size \(p+1\) is
\[
 \ell(J_\gamma^p1)=\sum_{j=0}^p\binom pj\frac{(-\gamma)^{p-j}}{(j+1)!}.
\]
On dividing by \(\gamma^p\), it is a nonzero rational polynomial of degree \(p\) in \(1/\gamma=a+b\), so it is nonzero when \(r(r-1)>p\). The physical strict part has depth at most \(p-1\) edges: the forward cache has at most \(m-2\), the base adds one, the entry into a plus adds one, and the reverse feedback adds at most \(r-1\). Any edge to an earlier minus, including an adopted prefix reference, cannot increase this bound. Thus the physical shifted tall scalar at size \(p+1\) is zero. The opposite diagonal-shift expansion would preserve it if the ordinary order were \(p+1\), a contradiction. This proves exact order for the \(q=p-1\) rule, without a hidden signed Gram determinant gate.

## 4. Actual counts and limitation

At the same forward grade and the same reverse grade the physical count is now
\[
                     \left\lfloor m^2/4\right\rfloor+L(r)+q,
                     \qquad L(r)=\left\lfloor(r+1)^2/4\right\rfloor.
\]
There are no extra reference rows. A coarse bound on the required pins is \(d_0\le L(r)-2\). At \(p=19\) take \(m=11,r=8\): the all-pins count is at most \(30+20+19=69\). At \(p=20\) take \(m=12,r=8\): the shorter rule is legal since \(d_0\le18\) and \(56>20\), so the count is at most \(36+20+19=75\). These improve the reflected-pack 70/77 at those orders, not the unrestricted real-algebraic table entries 54/59. The same proof applies to all degrees in the stated inequalities, rather than relying on evaluating the degree-19/20 hulls. The free diagonal lowers the reference/owner price and not the intrinsic full dense donor rank.
