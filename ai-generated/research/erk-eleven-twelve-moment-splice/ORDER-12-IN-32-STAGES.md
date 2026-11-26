# Exact paid order twelve in 32 explicit stages

This is an absolute upper bound over \(\mathbb U_{12}\coloneqq\mathbb Z[1/12!]\) and every nonzero commutative algebra over it. It uses the archived [16-stage paid order-nine seed](paid9-seed.json) unchanged. The improvement over the archived 33-row order-twelve method is one preparatory stage: an exact contrast between two literal old quarter-clock rows replaces one new value read. The final eleven-site reverse splice has the same coefficients and four mergers as before. The proof gives an exact next-order unit ideal without inverting thirteen.

## A contrast that costs no stage

Write \(g_t(x)\coloneqq |t|x^{|t|-1}/t!\) for the exact derivative polynomial of a rooted tree, \(I_x f\coloneqq\int_0^x f(z)\,dz\), and \(E_x f\coloneqq f(x)\). In the archived order-nine seed let \(\widehat\Pi_5\) be its degree-four forward chart. Its literal pure rows at \(1/4,1/2,3/4\) have incoming rows \(I_x\widehat\Pi_5\); for the midpoint this is the already proved merge with its original preparatory row. The chart is exact through tree order five and is pinned at zero, one and one-half, using the actual origin, the copied order-six output stage, and that midpoint. Its integral is the old order-six output read on arbitrary data.

For any child \(r\) of order six the residual \(g_r-\widehat\Pi_5\boldsymbol{\Phi}_r\) has degree at most five, zero values at all three pinned points, and zero mean. The three point values are exact: the origin, the order-six output stage and the pure midpoint all give the correct grade-six derivative profile. In the centered variable \(u\coloneqq2x-1\), the even part of the residual has the form \((1-u^2)(a+bu^2)\). The midpoint makes \(a=0\), and the mean then makes \(b=0\). The residual is odd, so its primitive from zero in \(x\) is symmetric about one-half.

It follows that the old stage-derivative read at \(1/4\) minus the old read at \(3/4\) realizes \(E_{1/4}-E_{3/4}\) through tree order seven. Each quarter is individually exact through order six. At order seven only a unary root with a child of size six can introduce an error, and the primitive errors at the two quarters are equal. A root with several children has all child sizes at most five and is exact at both.

## The 22-row forward prefix

Append the actual order-nine output stage to the old sixteen rows. Its incoming row is the old output and is henceforth the unit-clock pin. Use the old output weights multiplied by the \(j\)th clock powers as the moment read \(I_1(x^j\,\cdot)\) through tree order \(9-j\). This is a rooted-tree condition with \(j\) root leaves adjoined.

The grade-six chart is given by the two endpoint evaluations and the four moments of degrees zero through three on polynomials of degree at most five. The inverse is paid. After the endpoint reads are fixed, its matrix is the Gram matrix of monomials of degrees zero through three under weight \(x(1-x)\). The Jacobi construction by differentiating \(x^{j+1}(1-x)^{j+1}\) \(j\) times and dividing by \(x(1-x)\), then normalizing to be monic, has paid leading coefficients and moments through \(2j+3\le9\). Use this chart to append a single new row with incoming read \(I_{1/2}\Pi_6\). This new midpoint is a correct evaluation through grade seven.

The grade-seven chart now uses \(E_0,E_1,I_1,I_1(x\,\cdot),I_1(x^2\,\cdot)\), the old quarter contrast, and the new midpoint. The first five form a paid isomorphism on polynomials of degree at most four by the same beta argument. Their kernel on polynomials of degree at most six has the basis
\[
 (1-u^2)(u^3-3u/7),\qquad
 (1-u^2)(u^4-2u^2/3+1/21).
\]
The quarter contrast has values \(15/112,0\) on this basis; the midpoint has values \(0,1/21\). Both additional pivots are units. Append four new rows of the form \(I_x\Pi_7\) with clocks \(1/12,1/4,1/3,1/2\). All four are individually correct grade-eight evaluations.

Use those four evaluations, the two endpoint evaluations and the moments of degrees zero and one for the final chart \(\Pi_8\) on polynomials of degree at most seven. To see its paid pivot directly, use \(v\coloneqq12x-6\). The kernel of the six point reads is the span of \(P(v),vP(v)\), where
\[
 P(v)\coloneqq v(v^2-36)(v+5)(v+3)(v+2).
\]
For the normalized average on \([-6,6]\), the values of \(I[P],I[vP],I[v^2P]\) are
\[
 -56160/7,\qquad -222912/7,\qquad -4758912/35.
\]
They follow from \(P=v^6+10v^5-5v^4-330v^3-1116v^2-1080v\) and \(I[v^{2j}]=36^j/(2j+1)\). Their two-moment determinant is \(2^{14}3^8\cdot5/7\), a unit. Changing from moment \(v\) to moment \(x\) uses a unit affine transform. Thus the final chart is paid, correct through grade eight, and pins the actual endpoints and the old zeroth and first moments on arbitrary data.

The prefix uses \(16+1+1+4=22\) rows. The old contrast was a linear combination of actual old derivative rows, not an additional stage.

## The reusable ten-row suffix

Take the eleven-site interpolation rule with \(v=12x-6\) running through \(0,\pm2,\pm3,\pm4,\pm5,\pm6\). It integrates degree ten by interpolation and degree eleven by reflection. Its raw masses per clock are

| clocks | mass per clock |
|:--|--:|
| \(0,1\) | \(35663/1524600\) |
| \(1/12,11/12\) | \(576/4235\) |
| \(1/6,5/6\) | \(-9/1925\) |
| \(1/4,3/4\) | \(448/2475\) |
| \(1/3,2/3\) | \(783/15400\) |
| \(1/2\) | \(262/1155\) |

Use the origin mass on the existing origin. One can define the masses equivalently by integrating the eleven Lagrange cardinal polynomials. Use the following reverse labels, splitting the masses at \(1,1/3,1/2,2/3\) into a selected weight one and the later remainder:
\[
 (1,1/12,1/6,5/6,1/4,1/3,1/2,2/3,3/4,11/12,1/3,1/2,2/3,1).
\]
Only the first four labels are donor columns; their masses are all units. Write \(y=1-x\) for the reverse clock, and let \(\boldsymbol\beta\) be the virtual weights. On the nine distinct selected nonendpoint clocks \(\mathcal I\), set
\[
 u_x\coloneqq\frac{\eta}{\beta_x x(1-x)\prod_{z\in\mathcal I\setminus\{x\}}(x-z)} ,
 \qquad u_{1/12}=-\frac12(11/12)^2 .
\]
This determines the unit \(\eta\). All other labels have \(u=0\). Thus the \(u\)-pairing kills \(x(1-x)\mathcal P_{\le7}\) by the leading-coefficient identity, where \(\mathcal P_{\le j}\) denotes polynomials of degree at most \(j\).

Define \(L\) in reverse chronology, using only the four donor columns. Its first row is zero, its second reads only the first donor, and its third and fourth use the first two. These choices enforce \(L\mathbf1=\mathbf y\) and \(L\mathbf y=\mathbf y^{\odot2}/2+\mathbf u\). Set
\[
 \mathbf g\coloneqq L\mathbf y^{\odot2}-\mathbf y^{\odot3}/3,\qquad
 \mathbf v\coloneqq L\mathbf u.
\]
The four donor input columns \(\mathbf1,\mathbf y,\mathbf y^{\odot2},\mathbf u\) form a unit matrix. Indeed, the other two nonendpoint donor values are each \(100u_{1/12}\): the centered nodal derivative ratio is \(-25/4\), the ratio of \(x(1-x)\) is \(11/20\), and the mass ratio is \(-320/11\). The resulting determinant is five times \(u_{1/12}\), namely \(-605/288\).

At the six selected late clocks \(1/4,1/3,1/2,2/3,3/4,11/12\), prescribe the values of \(\mathbf g,\mathbf v\) so that both annihilate the space of endpoint-zero polynomials of degree at most eight and integral zero, with the \(\boldsymbol\beta\) weights. This is a paid six-coordinate solve. Its test functions are \(x(1-x)\) times polynomials of degree at most six with the one mean condition. In centered \(v\)-coordinates the nodal polynomial for the six sites and endpoints is
\[
 Q(v)\coloneqq v(v^2-36)(v^2-4)(v^2-9)(v-5).
\]
Its mean is \(-124416/5\): its even part is \(v^8-49v^6+504v^4-1296v^2\). This is a unit, proving that the mean condition supplies the one missing interpolation coordinate. The masses on the six selected sites are also units. On other later labels set \(g=v=0\). Using the four paid donor inputs gives each actual reverse row from its four action values. The last clock-one row is zero.

Reverse the order to obtain the primal suffix block \(T\) as the \(\boldsymbol\beta\)-weighted transpose of \(L\); division occurs only by the four donor masses. On the prefix coefficients its rows are \((I-TE)\Pi_8\), where \(E,I\) collect evaluation and primitive at the suffix clocks. Use the virtual masses for the output and the origin mass on the prefix origin. Thus each nondonor has the literal row \(I_x\Pi_8\). The remainder at one is identical to the appended endpoint, because \(I_1\Pi_8\) is exactly the old output row. The pairs at \(1/3,1/2,2/3\) consist of nondonors with identical rows, so each pair merges after redirecting taps and summing weights. The fourteen labels therefore contribute ten physical rows.

## Order and exactness

For a child tree \(r\), put \(\rho_r\coloneqq g_r-\Pi_8\boldsymbol{\Phi}_r(A_F)\), with \(A_F\) the 22-row prefix. The suffix derivative error obeys the standard extension identity
\[
 \boldsymbol\epsilon_{[r]}=T\boldsymbol\epsilon_r+(TE-I)\rho_r.
\]
Here \(\rho_r=0\) for \(|r|\le8\), so through order twelve any rooted product has at most one sourced error. One, two or three additional root operations correspond to words of length zero, one or two after that source, with letters \(T\) and multiplication by the clock. For a length-zero word the weighted source vanishes by \(L\mathbf1=\mathbf y\) and triangular integration. Length one occurs only for children of size at most ten; the only extra reverse term is \(\pm\mathbf u\), testing \(\rho_r\) of degree at most nine with two endpoint zeros. Length two occurs only for a child of size nine. Its residual has degree at most eight, two endpoint zeros and mean zero, so the \(\mathbf g,\mathbf v\) tests vanish as paid above. Any primitive term paired with \(\mathbf u\) has degree at most nine and endpoint zeros as well. All polynomial integrations used in this ordinary verification have degree at most eleven and the quadrature is exact on them. This proves every rooted condition through order twelve.

For exactness let \(r\coloneqq[\bullet]^{\#10}\), \(t\coloneqq[r]\#[\bullet]\), and \(B\coloneqq[\bullet]^{\#12}\), so \(t,B\) have size thirteen. The bushy tree \(r\) has exact derivative weights \(x^{10}\) at every stage, regardless of its stage order. Hence \(\rho_r\) has degree ten, leading coefficient one, and endpoint zeros. Its quotient by \(x(1-x)\) has degree eight and leading coefficient \(-1\); the normalized barycentric rule above gives \(U(\rho_r)=-\eta\), where \(U(f)\coloneqq\sum_i\beta_i u_i f(x_i)\).

For completeness, on \(t\) there is just the source \(r\), its unary extension and multiplication by \(x\). If \(Jf(x)\coloneqq\int_x^1 f(z)\,dz\), the reverse action is \(L\mathbf x=E(Jx)-\mathbf u\). The triangle identity for the degree-twelve polynomial \((Jx)\rho_r-xI_x\rho_r\) has integral zero and leading coefficient \(-1/2-1/11\). The exact derivative polynomial of \(t\) adds \(1/11\) times the degree-twelve quadrature error. Thus for the factorial-cleared defects \(D_t,D_B\) the resulting identity is
\[
 D_t/11+D_B/2=-13\,U(\rho_r)=13\eta .
\]
Although the unnormalized degree-twelve integral could use \(1/13\), this displayed identity is already in \(\mathbb U_{12}\). Also \(D_B=13\mathcal Q[x^{12}]-1\), with \(\mathcal Q\) the grouped quadrature. Since \(\eta\) is a unit, the defects generate the unit ideal. This proves exact order twelve under every nonzero paid base change.

The total is \(22+10=32\) allocated literal rows, after the documented mergers. Additional accidental coincidences are not assumed. This proof reconstructs all rows by finite paid linear operations; it does not rely on a new numerical replay.
