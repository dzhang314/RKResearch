# Smaller rational strict SDIRK witnesses and a rotating paid receiver

The two-order Newton theorem gives exact rational strict SDIRK at orders **eight in thirteen stages**, **nine in nineteen**, and **ten in twenty-one**. These replace the archived rational upper witnesses 15, 23, and 27 as bounds, not any of the smaller unrestricted real-algebraic entries. The exact witnesses retain the rational common diagonals \(1/4,1/7,1/8\) of the cited old seeds respectively. None of these new tableaux is claimed Lean-checked here.

The essential extension of the fixed-anchor argument is to impose early feed rows directly, before making the paid row correction. No inverse of a polynomial test matrix attached to the frozen rows is required.

## Reusing several already paid physical rows

In the notation of TWO-ORDER-NEWTON-TAIL.md, suppose the first \(t\) new clock sites \(\xi_1,\ldots,\xi_t\) are distinct clocks of old stages \(r_1,\ldots,r_t\) that are individually exact through size \(q+1\). Write \(\alpha_i\) for the actual strict predecessor row of old stage \(r_i\), with its diagonal \(\gamma\) removed. In the provisional feed, prescribe its first \(t\) rows instead as
\[
                    U_i=\alpha_i-\sum_{\ell<i}S_{i\ell}e_{r_\ell}^{\top}
                               \qquad(1\le i\le t).             \tag{1}
\]
On an old tree column of size at most \(q\) these rows are precisely the preliminary feed \((T_{\rm ev}J-BT_{\rm ev})\mathcal D\), by the exact old strict and evaluation functionals. All row-correction residuals still vanish on those low inputs. Use the last \(a=p-q-1\) distinct ladder rows for the correction right inverse; they avoid all the reserved early rows. After completing the Newton tail, merge the first \(t\) new rows sequentially into their old representatives. Once earlier ones are merged, (1) cancels their strict taps exactly, so the next row is a literal duplicate of its old representative. Move every incoming reference and its output weight into that earlier coordinate, then delete it. The elementary recursion shows no output is altered by these literal merges. Existing diagonal entries and old rows remain unchanged.

There is an additional useful reservation. If the old tableau admits a dense decoder through \(q+1\), one may use it in the preliminary feed. Its required low behavior through \(q\) is unaltered. Reserve any further nonmerged rows outside the pivot set so they retain that preliminary feed. They then become individually exact through \(q+2\): when a child has size at most \(q+1\), its data on *every* new row are already the exact evaluations by the low-order induction, and the old decoder now supplies the exact polynomial. This does not require the merged representatives to be individually exact through \(q+2\). It also does not impose any extra moment constraint on the pivot repair.

## Exact rational quadrature gates

Every column below specifies its chronological sites as follows. Put the listed initial sites first, then the single solved site \(z\), then the \(a\) ladder sites \(1-(2i-1)\gamma\) in order \(i=a,\ldots,1\). Let \(H\) be the monic product over all sites except \(z\), and take \(z=I(XH)/I(H)\). The full hull \(F=(X-z)H\) has degree \(p-1\) and \(I(F)=0\), so interpolatory weights integrate through degree \(p-1\). The rational values and respective signs in the table were checked directly by exact polynomial arithmetic using \(w_i=I(F/(X-\xi_i))/F'(\xi_i)\). None are zero. The next monomial necessarily fails by the displayed \(I(XF)\ne0\): \(XF\) has degree \(p\) and vanishes at every site.

| Target \(p\) | Old stages/order | \(\gamma\) | \(q\) | Initial sites | \(z\) | \(I(XF)\) | Weight signs | Reused, total |
|---:|:---:|:---:|---:|---|---|---|---|---|
| 8 | 7/6 | \(1/4\) | 3 | \(1/2,-1\) | \(1090/1081\) | \(-1245689/697374720\) | +++-+++ | 1, **13** |
| 9 | 11/7 | \(1/7\) | 4 | \(-1,-2,-3\) | \(302/255\) | \(-87763/12965400\) | -+-+++++ | 0, **19** |
| 10 | 15/8 | \(1/8\) | 4 | \(0,1/4,1/2\) | \(9075/9133\) | \(-2432737/1580146360320\) | +--+-++++ | 3, **21** |

Use these immutable old witnesses:

* Order six: the seven displayed literal rows and output weights in ai-generated/research/strict-sdirk-rational/order-six-seven-stage-rational-splice.md. Its fifth physical row, at \(1/2\), is individually exact through four. In addition to its row sum \(1/2\), its entries on the three old child columns \(A\mathbf c\), \(A\mathbf c^{\odot2}\), and \(A(A\mathbf c)\) are \(1/8,1/24,1/48\), respectively. This pays both size-three child shapes, hence every rooted stage derivative through size four at that row.
* Order seven: the checked rational literal in ai-generated/lean/RKCert/ReviewedNative/RationalStrictSDIRKElevenStageSevenUpper.lean, SHA-256 cb14583f04a53fe39c20f84c8b561942d81131e616269c04795bfdb448c60915. Its matrix and output scales are 11493557522580 and 17280. The ordinary order-seven theorem is already checked; no local-stage reuse is needed here.
* Order eight: the checked rational literal in ai-generated/lean/RKCert/ReviewedNative/RationalStrictSDIRKFifteenStageEightCore.lean, SHA-256 87e77e5ff39099a105ce098e5b817c70ce02ad1e8f585181556dab378310254b. Its matrix and output scales are 1540104384000 and 33075. The one-based rows \(8,7,13\) are the selected old representatives at \(0,1/4,1/2\). Rows \(7,8,9,10,11\) are individually exact through size five at distinct clocks \(1/4,0,1/8,3/4,1\), so interpolation supplies the old decoder through grade five. All these local payments, including row 13, were checked on the exact integer-scaled recurrence through size five; this is a finite local test, not an assumption from the output order. Use this stronger decoder in the preliminary feed for the order-ten extension, preserve the first three merge rows by (1), and reserve the fourth row (at \(z\)) away from the five correction pivots. After the three merges the row at \(z\) is individually exact through size six.

Thus each output order follows from the all-rooted Newton theorem with explicit rational nodes and preserved chronological coefficients. The \(I(XF)\) entries are independent exact next-bush witnesses. No measured kernel certification of these enlarged tableaux is implied.

## Self-sustaining even-order continuation

Let the known seed have order \(2m-2\), and suppose one actual stage at \(\alpha\) is individually exact through size \(m\), with \(\alpha\) not a root of the degree-\((m-1)\) shifted Legendre polynomial. Then it admits a dense decoder through size \(m\). To see this, take a linear combination of tree columns through size \(m\) that is physically zero in the old tableau, with formal polynomial \(P(X)\) of degree at most \(m-1\). The ordinary order tests give \(I(X^jP)=0\) for \(0\le j\le m-2\), by adjoining leaves. Hence \(P\) is a scalar multiple of that orthogonal polynomial. The actual pure sample at \(\alpha\) gives \(P(\alpha)=0\), which forces \(P=0\). For a literal decoder, use those first \(m-1\) weighted moments on any old vector together with its one coordinate at \(\alpha\). Their \(m\)-by-\(m\) moment/evaluation matrix is invertible by this same kernel argument.

For target \(p=2m\) use \(q=m-1\) and the stronger dense \(m\) decoder in the preliminary feed. Put the old reusable \(\alpha\) first, a fresh exterior clock \(\beta\) second, then the remaining ordinary free nodes, then the \(m\) ladder nodes. Reserve the first two rows away from the correction pivots. The first is a literal old duplicate; the second becomes individually exact through size \(m+1\), and \(\beta<0\) keeps it off the next shifted Legendre node set. Thus this local information is passed forward at every jump. The initial \(\alpha=9075/9133\) from the order-ten construction is also not a shifted Legendre root: a rational interior shifted Legendre root can only be \(1/2\), by the integer constant term \(\pm 1\) and reflection, as in the even support tradeoff proof.

This continuation preserves the same diagonal \(1/8\). At each step put \(\alpha,\beta\) first, using \(\beta=-1\) at even \(m\) and \(\beta=-2\) at odd \(m\). Add the first \(m-4\) strictly negative integers not already in the initial list, fix the \(m\) ladder sites, and solve the one remaining free site by the same \(z=I(XH)/I(H)\). No integer chosen this way collides with the odd-eighth ladder. For reference, exact scalar gates through twenty are:

| \(p\) | \(\alpha\) | New high-ready \(\beta\) | Solved \(z\) | \(I(XF)\) | Weight signs | Total stages |
|---:|---|---|---|---|---|---:|
|12|\(9075/9133\)|\(-1\)|\(597420361/783319131\)|\(-1151734070569817279/8045432679821389332480\)|++-++-+++++|31|
|14|\(-1\)|\(-2\)|\(68974053965/68685634853\)|\(-481089601965156873323/51907773859107082076160\)|+-+-++-++++++|43|
|16|\(-2\)|\(-1\)|\(18597392131407/18589798585870\)|\(-31190692020337801883236423/272949334598284557366067200\)|+--+-+++-+-++++|57|
|18|\(-1\)|\(-2\)|\(42860523819631628/42976648351311529\)|\(-53423004336711538615343627383823/30518195131275698497920046202880\)|--+-+-++++-+-++++|73|
|20|\(-2\)|\(-1\)|\(44123254076509126587/44354273258678140634\)|\(-93218764777653353237419043912078394203/2771688644799123950668448067213066240\)|+--+-+-++-++-+-++++|91|

The quotas add \(p-2\) chronological stages per row of this table: \(p-1\) physical nodes before one merge. Retaining a new higher-local receiver costs no extra preparation row or output slot. The counts are constructive rational continuation bounds; they remain above the unrestricted real-algebraic upper counts. Only the scalar quadrature and old local gates were computed, not a solver or higher-order exhaustive tree pass. The analytic argument covers all the rooted conditions.
