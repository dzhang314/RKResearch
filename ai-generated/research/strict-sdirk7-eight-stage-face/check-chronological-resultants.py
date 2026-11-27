"""Exact characteristic-zero/rational near-edge obstructions."""
import sympy as s
x,z,v=s.symbols('x z v')
def m(A,B,e=0):
    P=s.Poly(x**e*A*B.subs(x,z-x),x)
    return s.factor(sum(co*z**j[0]/(j[0]+1) for j,co in P.terms()))
def step(A):
    return s.integrate(A,(x,0,x))-A
def cuts(H,K):
    F,G=step(H),step(K)
    T=m(H,G)
    assert s.expand(T-m(F,K)) == 0
    L,M=m(H,G,1),m(F,K,1)
    S0,S1,S2=[m(H,K,i) for i in range(3)]
    q=s.factor(m(F,G)).as_numer_denom()[0]
    P=s.factor(S2*T*T-(L+M)*S1*T+L*M*S0).as_numer_denom()[0]
    assert s.rem(P,z*z,z)==0
    return q,s.cancel(P/z**2)
H=s.laguerre(2,x)
q0,p0=cuts(H,H)
rr=1639*z**5-39460*z**4+322200*z**3-1068000*z**2+1344600*z-456480
assert s.rem(p0,q0,z)==-112896*rr
assert s.resultant(q0,rr,z)==2**25*3**8*5**10*2843
K=v*v*(v-1)-v*(v-2)*(2*v-1)*x+(v-2)*(v-1)**2*x*x/2
Q,P=cuts(H,K)
res=s.factor_list(s.resultant(Q,P,v))
fac=sorted((s.degree(F,z),k) for F,k in res[1])
assert fac == [(1,24),(4,1),(4,2),(4,3),(30,1)]
for F,k in res[1]:
    if s.degree(F,z)==1:
        assert F==z
        continue
    F=s.Poly(F,z)
    coeff=list(map(int,reversed(F.all_coeffs())))
    assert coeff[-1]%43  # projective point at infinity
    assert all(sum(c*pow(a,i,43) for i,c in enumerate(coeff))%43 for a in range(43))
print("Both-zero resultant is nonzero in characteristic zero.")
print("Every nonzero parameter factor for one zero edge is projectively rootless modulo 43.")
