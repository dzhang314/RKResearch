# Eight rational sites are necessary and sufficient for anchored degree-nine quadrature

Let a quadrature rule on $[0,1]$ have rational abscissae and integrate every polynomial of degree at most nine. Suppose its possible support is a rational set containing 0 and 1, even if their weights vanish. Then this set has at least eight sites. No sign assumption on the weights is needed. This applies to a Runge–Kutta tableau only when its ordinary quadrature can be supported on such an endpoint-anchored set. It is not a separate stage bound of eight plus a chosen construction overhead.

## Seven is impossible: reduce three nodal moments modulo 4

Pad a hypothetical set of at most seven sites by distinct rational dummy sites of weight zero until there are seven. Write the five sites other than 0 and 1 as reduced fractions $u_i/v_i$. Form

$$
 P(x)=\prod_{i=1}^{5}(v_i x-u_i)=\sum_{j=0}^{5}a_j x^j.
$$

Each linear factor is primitive at 2. Exactness applied to $x(1-x)x^kP(x)$ for $k=0,1,2$ says the integral vanishes, since the integrand is zero at every quadrature site. The coefficient of $a_j$ in the integral is $1/((j+k+2)(j+k+3))$. Multiplying the three equations by 840, 2520 and 2520, respectively, gives the following rows modulo 4, in ascending coefficient order:

$$
  (0,2,2,0,0,3),\qquad (2,2,0,0,1,3),\qquad (2,0,0,1,3,0).
$$

Modulo 2 the three equations force $a_5=a_4=a_3=0$. The product $P$ is nonzero modulo 2 because no factor becomes zero. Its degree is therefore at most two, so at least three of the five factors have even slope. Every term contributing to $a_4$ or $a_5$ uses slopes from at least two of those factors. Hence $a_4,a_5$ are actually zero modulo 4. The first two congruences now force $a_0=a_1=a_2$ modulo 2. The product is nonzero, so it must reduce to $1+x+x^2$. That polynomial has no root in $\mathbb F_2$ and therefore cannot be a product of linear factors there. Contradiction.

The [portable Lean receipt](../../lean/RKCert/ReviewedNative/RationalEndpointNineGate.lean) checks the three coefficient lists and independently checks the entire modular obstruction by enumerating the normalized factor multisets. The reduction of an arbitrary quadrature to those three equations is the argument above.

## Eight suffice, with positive weights

In increasing order the abscissae are

$$
 0,\quad 1/9,\quad 4/13,\quad 2/5,\quad 3/5,\quad 9/13,\quad 8/9,\quad 1.
$$

They are symmetric under $x\mapsto 1-x$. The weights at the first four are respectively

$$
 46201/1451520,\quad 176969853/1001960960,\quad
 815730721/5391671040,\quad 4609375/32864832;
$$

the remaining four are their reflections. [Exact replay](replay.py) checks every moment through degree nine and the degree-ten failure. This scalar rule does not by itself enforce any non-scalar Runge–Kutta order condition.
