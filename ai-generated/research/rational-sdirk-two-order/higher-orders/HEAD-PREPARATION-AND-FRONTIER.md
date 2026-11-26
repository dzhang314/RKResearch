# Higher local samples inside a paid Newton tail

This construction uses a chronological Newton tail only for the moment rows that the rooted proof actually needs. Its earlier rows can therefore supply preparation for one another, while remaining ordinary output rows. No old stage equation is edited. With old common diagonal \(\gamma\ne0\), every new physical stage retains the same diagonal.

## Freedom in the strict early block

Use the normalized elementary vectors and polynomial integrals of the exact-frontier lemma in the previous note. Fix a target order \(p\), an old order \(P\coloneqq p-2\), an old decoder through size \(q\ge\lfloor(p-1)/2\rfloor\), and put \(a\coloneqq p-q-1\). Choose \(k\ge a\) distinct actual output clocks for an exact scalar quadrature through degree \(p-1\), with nonzero weights. On the last \(a\) physical rows put the fixed and spare correction pivots. Write \(P_j\) for the monic polynomial vanishing on the last \(j\) clocks. Only the equations
\[
 L_{P_j}S=-\frac{L_{P_{j+1}}}{j+1}
                           \qquad (0\le j<a)
\]
are needed, with \(L_f\) the weighted clock row and \(S\) the strict part of the new block. In particular, the strict coefficients between pairs of the first \(k-a\) new rows can be chosen arbitrarily.

To verify this, solve one chronological column at a time. For a column before the last \(a\) rows, treat the already prescribed early taps as known. Its \(a\) remaining taps are the entries to the last \(a\) rows; the displayed \(a\) equations give an invertible weighted evaluation matrix of monic degrees \(0,\ldots,a-1\). For a column with only \(d<a\) later rows, solve the first \(d\) displayed equations from those \(d\) taps. For \(j\ge d\), \(P_j\) vanishes on all later rows and \(P_{j+1}\) vanishes on the column's site. Thus the other equations are already true. This proves the strict triangular solution without constraining the earlier chosen taps.

Each first-group row may be prescribed in full, including its old feed, provided it gives the correct local profile through size \(q+1\). To check compatibility on low inputs, let \(E\) denote evaluation at the new clocks, \(B\coloneqq\gamma\,\mathrm{Id}+S\) and \(\mathcal D_q\) the old decoder. The prescribed strict old feed agrees on old trees of size at most \(q\) with \((EJ-BE)\mathcal D_q\), because all earlier new stages which it uses already have exact low values. In particular a literal copy of an old stage exact through size \(q+1\), with no additional early taps, can occupy one of these slots and then be merged exactly. The old feed correction is supported on the last \(a\) rows; changing those rows does not change any earlier stage. It uses the same moment identities and the same largest-child proof as the exact-frontier lemma. The number of required fixed tail clocks is dictated by the actual old frontier tests, not by the possible stronger decoder in the protected group.

## A decoder assembled in the middle of the head

Suppose the old method has order \(P\). For a nominal polynomial of degree at most \(d-1\), the old observation rows reveal its moments through degree \(P-d\). Supplement these with actual pure stage samples through size \(d\) from the old rows and from already prescribed early receivers. The additional number sufficient, when all these sample times are negative and distinct, is
\[
                       \max(0,2d-P-1).
\]
The proof is the moment-and-evaluation argument: a kernel polynomial is divisible by the product of the sample factors. The degree of the quotient is at most \(P-d\), and its moment against the original polynomial is a definite integral of its square times that product. Interpolation alone applies when there are no moment rows. Individual cases below replace one negative sample by a proved nondegenerate solved clock.

Once a decoder \(\mathcal D_d\) exists on the old rows together with some already assigned head rows, a later protected receiver at any rational clock \(\xi\) may use the strict feed
\[
                     E_\xi(J-\gamma\,\mathrm{Id})\mathcal D_d
\]
on those earlier coordinates, with literal diagonal \(\gamma\) and other earlier taps zero. This is allowed by the freedom above. For each smaller child the existing decoder computes its exact polynomial; the own diagonal contributes the remaining exact \(\gamma\) times its value at \(\xi\). By induction on the tree size the new receiver is locally exact through \(d+1\). Its row does not depend on any subsequently adjustable pivot. Placing a few such layers in the chronological head buys genuinely higher samples without adding any physical stages outside the intended output tail.

## A genuinely scalar frontier payment

For odd old order \(P=2n-1\) with \(n\) odd, the next target is \(p=2n+1\). Through old tree size \(n+1\), the old relation polynomials are orthogonal to degrees \(0,\ldots,n-2\); they therefore lie in the span of the monic shifted Legendre polynomials of degrees \(n-1\) and \(n\). If there is one genuine locally size-\((n+1)\) old sample at \(1/2\), these relations also vanish there. The degree-\(n\) polynomial vanishes at \(1/2\) by odd reflection parity; the degree-\((n-1)\) one does not, since it is reflection-even and all its roots are simple. Thus a relation is a multiple of the degree-\(n\) polynomial. The frontier integral against \(X^{n-1}\) annihilates it. This pays one fewer fixed clock, using only the old decoder through \(n\), not through \(n+1\).

One more early pure size-\((n+1)\) sample at a negative clock completes the full degree-\((n+1)\) decoder in the head: the degree-\(n\) orthogonal polynomial cannot vanish at that exterior clock. Subsequent protected receivers may then be locally exact through \(n+2\). The order-eleven branch uses precisely this mechanism, starting with an already paid midpoint row and merging it with no preliminary zero-output stage.
