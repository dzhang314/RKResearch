import sympy as S
Y,d,e,v,r=S.symbols('Y d e v r')
Q=S.Rational
a,t=Q(2,5),Q(3,5)
def I(p):return sum(z/(k+1)for (k,),z in S.Poly(p,Y).terms())
def J(p):return sum(z*Y**(k+1)/(k+1)for (k,),z in S.Poly(p,Y).terms())
common=Y*(Y-1)*(Y-a)*(Y-t)*(Y-d)*(Y-1+d)
H=Y*Y-Y+v
N=S.factor(I(common*H))
dv=S.solve(N,v)[0]
print('nodal integral',N,'v',dv,flush=True)
mu={x:S.factor(I(S.cancel(common/(Y-x))*H)) for x in (a,t,d)}
def rho(x):return x*(3*x*x-10*a*x+9*a*a)/12
w={x:S.factor(mu[x].subs(v,dv)*rho(x)) for x in mu}
C=S.factor((t-a)*(r-d)*w[d]+(a-d)*(r-t)*w[t]+(d-t)*(r-a)*w[a])
print('normalized C',C,flush=True)
c=S.Poly(S.cancel(C).as_numer_denom()[0],r)
u0,u1=c.nth(0),c.nth(1)
j=J(Y*(Y-a)*(Y-t)*(Y-d))
for case,H2 in enumerate((H,(Y-1+d)*(Y-1+e))):
    D=S.factor(I((Y-1)*(Y-r)*H2*j).subs(v,dv))
    D=S.Poly(S.cancel(D).as_numer_denom()[0],r)
    E=S.factor(u1*D.nth(0)-u0*D.nth(1))
    print('case',case,'elimination=',E,flush=True)
    if case:
        DD=e*(1-e)-dv
        f=S.factor(S.resultant(E,S.cancel(DD).as_numer_denom()[0],e))
    else:f=E
    print('case',case,'univariate=',f,flush=True)
F=711210*d**5-1803594*d**4+1765173*d**3-800550*d**2+148396*d-8325
G=3256913840040*d**12-19053265961520*d**11+48782085508776*d**10-71868319149468*d**9+67398713896668*d**8-42059238871662*d**7+17759469826357*d**6-5073391911785*d**5+968755211794*d**4-120749999221*d**3+9379137769*d**2-410612850*d+7716250
assert S.expand(f+(5*d-3)**2*(5*d-2)**2*G)==0
K=S.factor(I((Y-1)*(Y-r)*H*j).subs(v,dv))
K=S.Poly(S.cancel(K).as_numer_denom()[0],r)
E0=S.factor(u1*K.nth(0)-u0*K.nth(1))
assert S.expand(E0+(5*d-3)*(5*d-2)*F)==0
assert 70*(27*d*d-27*d+4)-27*(70*d*d-70*d+9)==37
for name,f,p in (('quintic',F,7),('degree twelve',G,19)):
    g=S.Poly(f,d)
    assert int(g.LC())%p and all(int(g.eval(j))%p for j in range(p))
    print(name,'has no projective roots modulo',p,'coefficients',tuple(int(c)%p for c in g.all_coeffs()))
