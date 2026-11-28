import sympy as S,flint as fl,time,json
from pathlib import Path
R=S.Rational
x,y,t,T=S.symbols("x y t T")
a=R(1,2)
L=lambda j,v:sum(k*(-1)**(j-k)*S.binomial(j,k)*S.binomial(j+k,k)*v**(k-1) for k in range(1,j+1))
K=lambda j,s:s*L(j,a*s)
D=2*x*y-x-3*y*y+2*y
S0=3*x*x-2*x*y-2*x+y
DB=5*x*x-5*x+1
eb=-(7*x*x-7*x+2)/1260
rb=x**3*(15*x**3-49*x*x+55*x-20)/DB
kb=-30*x**3*(x-1)**3/DB
P0=T*(T-1)*(T-x)*(T-y)
I=lambda f,z:sum(v*z**(k+1)/(k+1) for (k,),v in S.Poly(f,T).terms())
P00,P10=I(P0,1),I(T*P0,1)
K10=I(T*T*P0,1)-eb
Delta=-DB*D/10800
r0=(K10*I(P0,t)-P10*I(T*P0,t))/Delta
k0=(P00*I(T*P0,t)-P10*I(P0,t))/Delta
rY=S.factor(r0.subs(t,y))
G3=S.Poly(S.cancel((x*x*(x-1)**3*D*L(6,a*y)+y*y*(y-1)**3*S0*L(6,a*x))/((y-1)*(y-x))).as_numer_denom()[0],y,x).primitive()[1].as_expr()
fmt=lambda w:S.Poly(w,x,y,t).degree_list()
def ce(w):return S.cancel(w).as_numer_denom()[0]
def trimmed(w,dgr):
    q,r=S.div(ce(w), P0.subs(T,t), t)
    u,d=S.fraction(S.factor(q))
    fs=S.factor_list(u)[1]
    print('q factors',[(fmt(f),m) for f,m in fs],flush=True)
    assert {f for f,m in fs if S.degree(f,t)==0} == (
        set() if dgr==2 else {x-1,y-1,x,y,x-y})
    f,=[f for f,m in fs if S.degree(f,t)==dgr and m==1]
    return f
st=time.monotonic()
k=S.factor(kb*K(6,t)/K(6,x))
E2=trimmed(k-k0,2)
print('E2',fmt(E2),time.monotonic()-st,flush=True)
M=S.Matrix([[K(j,s) for j in (5,6,7)] for s in (1,x,y)])
A=[K(j,t) for j in (5,6,7)]
# A dot adj(M) r; expand numerator before quotient by P0 and original modal det.
E3eq=(S.Matrix([A])*M.adjugate()*S.Matrix([1,rb,rY]))[0] - M.det()*r0
E3=trimmed(E3eq,3)
print('E3',fmt(E3),time.monotonic()-st,flush=True)
ctx=fl.fmpz_mpoly_ctx.get(('x','y','t'))
def conv(f):return ctx.from_dict({p:int(c) for p,c in S.Poly(f,x,y,t).terms()})
F2,F3=map(conv,(E2,E3));GF=conv(G3)
R0=F2.resultant(F3,2)
fs=R0.factor()[1]
print('t-result',R0.degrees(),[(p.degrees(),m) for p,m in fs],time.monotonic()-st,flush=True)
def rows(p):return [[*map(int,i),int(c)] for i,c in p.to_dict().items()]

assert len(fs)==1 and fs[0][1]==1
H=fs[0][0]
X=GF.resultant(H,1)
xs=X.factor()[1]
assert X.degrees()==(256,0,0)
assert [(p.degrees()[0],e) for p,e in xs]==[(36,1),(20,2),(2,13),(1,22),(4,22),(1,44)]
for i,(p,e) in enumerate(xs[2:]):
    v=[5*x*x-5*x+1,x,33*x**4-132*x**3+168*x*x-72*x+8,x-1][i]
    assert p==conv(v)
data=dict(G3=rows(GF),H=rows(H),E2=rows(F2),E3=rows(F3),bases=[rows(e) for e,k in xs])
dest=Path(__file__).with_name('projection.json')
if dest.exists():assert json.loads(dest.read_text())==data
else:dest.write_text(json.dumps(data)+'\n')
print('Degree-36 and degree-20 midpoint projection with exact guard discards')
