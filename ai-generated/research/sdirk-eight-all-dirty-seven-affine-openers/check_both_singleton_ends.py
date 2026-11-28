"""Complete both-second singleton, both-end singleton affine-stage exclusion."""
import sympy as S
a,b,y,z,D=S.symbols('a b y z D')
L3=lambda v,d:5*v**3-3*d*d*v
L4=lambda v,d:35*v**4-30*d*d*v*v+3*d**4
K,r=S.div(L3(y,D)*L4(z,D)-L4(y,D)*L3(z,D),y-z,y)
assert r==0
def y3(v,w,mode):
    return 8+v+w-4/v if mode=='A' else v+w+2/v
def make(v,w,mode):
    f=S.cancel(K.subs({y:y3(v,w,mode),z:w-v,D:2-v-w})).as_numer_denom()[0]
    return S.Poly(f,a,b,domain=S.QQ)
F={d:make(a,b,d) for d in ('A','S')}
Q={d:make(b,a,d) for d in ('A','S')}
mesh=S.Poly(L4(b-a,2-a-b)-560*(a*a+2*a-1)*(b*b+2*b-1),a,b,domain=S.QQ)
Fmesh={k:f.resultant(mesh) for k,f in F.items()}
Qmesh={k:q.resultant(mesh) for k,q in Q.items()}
for d,e in [('A','A'),('A','S'),('S','S')]:
    rr=F[d].resultant(Q[e]); g=rr.gcd(Fmesh[d]).gcd(Qmesh[e])
    assert g.degree()==0
    print(d,e,'mesh projection gcd 1',flush=True)
print('verified affine S,S,D / S,S,D when both endpoints are singleton')
