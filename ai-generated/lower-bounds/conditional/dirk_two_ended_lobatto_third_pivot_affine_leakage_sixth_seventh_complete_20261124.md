# A two-ended, three-pivot Lobatto obstruction at orders 16, 18, 20

**Systematic characteristic-zero result.** Let m=8,9,10, put d=m-3 and p>=2m. On the fixed (m+1)-point Lobatto grid G={0,1} union roots of the derivative of the shifted degree-m Legendre polynomial, a clean contrast of degree AND genuine grade at most d cannot be paid at BOTH ends by zero pure trace through m, a single fixed Jacobi trace at m+1, and an affine Jacobi trace at m+2. The degree bounds are respectively 5,6,7. For m=8 the last (m+2)-band hypothesis is not required. The earlier p16/s22 proof realizes the first of these three cases; no claim is made that every p18/s25 or p20/s29 tableau satisfies the hypotheses. The two-headed tests form an immediate reusable exclusion for rank charts that actually prove the stated leakage inclusions. In particular they do not need active clocks in either temporal direction to be in the same chronological or numerical order.

Here are exact sufficient hypotheses. In each orientation take a physical lower triangular primitive and split diagonal clock X, with genuine feature operations Jf(x)=integral from 0 to x of f, x multiplication, and a scalar base beta (1 in the ordinary case; b or a properly certified projected base is allowed). There is a genuine pair of grade <=d, zero on untested stages, equal to beta_i P(x_i) at each tested/clean stage, with scalar density P. In the other orientation the scalar density is P(1-y). The underlying numerical contrasts need not be identical if the two independent feature lifts are available. At every nonzero contrast coordinate its clock belongs to G and the residual inclusions below hold. The scalar output on every multiple of the given lift agrees with the [0,1] integral within the total grade p-1. In each orientation, on these active coordinates, all genuine pure errors actually used are zero through m; at m+1 they have the simultaneous form beta_i phi(x_i) h0 for a scalar h0, and at m+2 the simultaneous form beta_i phi(x_i)(h0+h1 x_i), with h0,h1 depending on the error but the same on ALL active coordinates. Here phi(x)=x J_(m-1)(x), where J_(m-1) is the shifted polynomial orthogonal for x dx. The commutator R=X A-A X-A² must have its actual triangular first-pivot value minus the diagonal squared times the input for the chosen numerical operator; if a projection is used, all discrepancies of projected primitives and commutators must individually fit the indicated bands. On the true reflected terminal-zero band it suffices that the masks used start with x, all formal primitive profiles vanish at zero, and actual reverse row zero makes their true residuals terminal-zero. Arbitrary claims about products of two marked rows or order of a folded tableau do not supply these assumptions.

The leakage hypotheses have a common scalar origin. If numerical E_(m+q) has a direct P_m scalar part plus genuine pure bands vanishing at all tested sites, a scalar part of a true grade-(m+q) pure is anchored x times a polynomial perpendicular through m-q-1 to x dx, hence a combination of x J_(m-q),...,x J_(m-1). For q=1 this is phi. For q=2 its clean trace is phi times an affine polynomial: at nonzero Lobatto sites, the Christoffel identity for (x-1) times the Jacobi polynomial of degree m-1 for x(1-x) implies J_m+aJ_(m-1)=0 there for a fixed a (including x=1). The three-term x-weighted recurrence expresses J_(m-2)/J_(m-1) affinely there. Consecutive orthogonal polynomials ensure phi does not vanish at a nonzero Lobatto site. This explanation is a sufficient mechanism, not permission to infer the E dimensions at higher orders.

**Chronological equations.** Three distinct nonzero active clocks exist in each orientation when P is nonzero. Otherwise the numerical pair x(x-a)(x-d)theta vanishes on the whole array (omit missing factors). Its scalar tests against all q through degree d+2 cost at most d+3+d+2=2m-1. The rational x dx Gram on (x-a)(x-d)P would force the polynomial to vanish. Take successive first surviving active clocks a,d0,e by masking x, then x(x-a), then x(x-a)(x-d0). To avoid confusing degree bound d and clock d0 denote the latter by v below. Prior actual coordinates with zero contrast, regardless of their clocks, cause no difficulty.

First refund each of their actual diagonals. The three commutators cost at most m, m+1, m+2. The second is numerically zero at the preceding active pivot because its input is zero throughout that prefix; this forces its constant clean-trace coefficient to vanish, since beta_i phi(a) is nonzero. The third commutator vanishes at both distinct preceding pivots a,v, forcing its affine multiplier to vanish too. A zero diagonal at each selected current pivot follows from its commutator diagonal value, with no assumption about any other row at that same clock.

Write I_t[f]=integral from zero to t of f and V_t=I_t[x(x-a)(x-v)P]. Then there are SIX linear conditions per end:
1. I_a[xP]=I_a[x²P]=I_v[x(x-a)P]=0, by the fully zero pure trace through m and the first two diagonal refunds.
2. phi(v) I_a[x²(x-a)P]-phi(a) I_v[x²(x-a)P]=0. The primitive has grade at most m+1; its numerical value is zero at both pivots and the pure residual shares one common multiplier of beta phi. Divide only by the actual nonzero base at each active pivot.
3. phi(e) V_a-phi(a) V_e=0. The same common-multiplier test now uses the first and third pivots after the third refund. There is also a comparison with the second pivot; it is not needed.
4. The three numbers I_t[x²(x-a)(x-v)P]/phi(t), at t=a,v,e, are evaluations of ONE AFFINE polynomial. Indeed the numerical primitive is zero at all three, its total grade is at most m+2, and that is the exact pure envelope there. The signed three-point divided-difference numerator is the required last linear condition. It is important not to set that affine multiplier individually to zero. In the reflected direction substitute P(1-y), not P(y), in all six equations.

Hence a nonzero coefficient vector of length m-2 would be in the common kernel of twelve explicitly specified rows. The same split-prime/rational-lifting principle as dirk_order16_hidden_six_two_ended_lobatto_pivot_replay_20261123.md verifies no such kernel. Enumerate all (m(m-1)(m-2))² choices of the two ordered triples from the m nonzero Lobatto sites (the choices on opposite ends can coincide, reflect or repeat across pairs). Only triples above deficient first-pair tests need be computed individually. The final rank is m-2 in EVERY case for both primes at each order. At m=10 the extra affine divided-difference equation really matters: using only one new third-pivot equation per orientation leaves 72 modular failures at 4523 and at 15727, with first clocks 1 and second/third clocks mirror-matched. Adding the sixth equation removes all. A good split prime preserves all distinct fixed roots, the localized rational denominators and phi values; if the characteristic-zero rank vanished for an algebraic choice, all maximal minors would vanish on reduction. This establishes nonexistence over any characteristic-zero extension, with no evaluation of unknown tableau coefficients modulo a prime.

Exact outputs from standalone Python, counting each certified family of rank-sufficient two-pivot pairs for every possible third-pivot extension:
~~~text
8 1033 pairs 3136 unresolved pairs 0 paid triple checks 0 all triple pairs covered 112896
8 1237 pairs 3136 unresolved pairs 0 paid triple checks 0 all triple pairs covered 112896
9 3529 pairs 5184 unresolved pairs 8 paid triple checks 392 all triple pairs covered 254016
9 5531 pairs 5184 unresolved pairs 8 paid triple checks 392 all triple pairs covered 254016
10 4523 pairs 8100 unresolved pairs 247 paid triple checks 15808 all triple pairs covered 518400
10 15727 pairs 8100 unresolved pairs 245 paid triple checks 15680 all triple pairs covered 518400
~~~

Source:
~~~python
from itertools import permutations, product
from math import comb, isqrt

def prove(m,p):
    assert p>2*m and all(p%t for t in range(2,isqrt(p)+1))
    n=m-2                             # coefficient count, deg P <= m-3
    L=[(-1)**(m-j)*comb(m,j)*comb(m+j,j) for j in range(m+1)]
    D=[j*L[j] for j in range(1,len(L))]
    J=[(-1)**(m-1-j)*comb(m-1,j)*comb(m+j,m-1) for j in range(m)]
    def ev(f,u):
        y=0
        for t in reversed(f):y=(y*u+t)%p
        return y
    assert D[-1]%p
    inside=[u for u in range(p) if ev(D,u)==0]
    assert len(inside)==m-1 and 0 not in inside and 1 not in inside
    G=[1]+inside                         # all nonzero sites, endpoint included
    I=lambda u,j:pow(u,j+1,p)*pow(j+1,-1,p)%p
    H=lambda u:u*ev(J,u)%p
    assert all(H(u) for u in G)
    def rank(A):
        A=[row[:] for row in A]
        d=0
        for j in range(n):
            k=next((k for k in range(d,len(A)) if A[k][j]%p),None)
            if k is None:continue
            A[k],A[d]=A[d],A[k]
            C=pow(A[d][j],-1,p)
            for k in range(d+1,len(A)):
                q=C*A[k][j]%p
                if q:
                    for l in range(j,n):A[k][l]=(A[k][l]-q*A[d][l])%p
            d+=1
        return d
    def flip(A):
        return [[sum(row[j]*(-1)**j*comb(i,j) for j in range(i+1))%p
                 for i in range(n)] for row in A]
    def pair(a,d):
        return [
           [I(a,j+1) for j in range(n)],
           [I(a,j+2) for j in range(n)],
           [(I(d,j+2)-a*I(d,j+1))%p for j in range(n)],
           [(H(d)*(I(a,j+3)-a*I(a,j+2))-H(a)*(I(d,j+3)-a*I(d,j+2)))%p
            for j in range(n)]]
    def third(a,d,e):
        V=lambda u,j:(I(u,j+3)-(a+d)*I(u,j+2)+a*d*I(u,j+1))%p
        return [
           [(H(e)*V(a,j)-H(a)*V(e,j))%p for j in range(n)],
           [((d-e)*pow(H(a),-1,p)*V(a,j+1)
             +(e-a)*pow(H(d),-1,p)*V(d,j+1)
             +(a-d)*pow(H(e),-1,p)*V(e,j+1))%p for j in range(n)]]
    pp=list(permutations(G,2))
    V={q:pair(*q) for q in pp}
    W={q:flip(z) for q,z in V.items()}
    triples={q:third(*q) for q in permutations(G,3)}
    others={q:flip(z) for q,z in triples.items()}
    bad2=used3=total=0
    for q,r in product(pp,repeat=2):
        rows=V[q]+W[r]
        if rank(rows)==n:
            total+=(m-2)**2
            continue
        bad2+=1
        for u in G:
            if u in q:continue
            for v in G:
                if v in r:continue
                full=rows+triples[q+(u,)]+others[r+(v,)]
                assert rank(full)==n,(m,p,q,u,r,v)
                used3+=1;total+=1
    assert total==(m*(m-1)*(m-2))**2
    print(m,p,'pairs',len(pp)**2,'unresolved pairs',bad2,
          'paid triple checks',used3,'all triple pairs covered',total)
for m,p in [(8,1033),(8,1237),(9,3529),(9,5531),(10,4523),(10,15727)]:
    prove(m,p)
~~~
