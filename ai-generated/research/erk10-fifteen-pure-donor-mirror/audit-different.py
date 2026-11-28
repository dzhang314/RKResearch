import sympy as S
Y,a,e,v,r=S.symbols('Y a e v r')
Q=S.Rational
t,b,c=3*a/2,1-a,1-3*a/2
simm=[a,t,b,c]
H=Y**2-Y+v
H4=Y*(Y-1)*S.prod(Y-z for z in simm)
def I(p):return sum(z/(k+1)for (k,),z in S.Poly(p,Y).terms())
def J(p):return sum(z*Y**(k+1)/(k+1)for (k,),z in S.Poly(p,Y).terms())
N=S.factor(I(H4*H))
vd=S.solve(N,v)[0]
num,den=S.fraction(S.cancel(vd))
assert S.gcd(num,den)==1
N0,N1=S.Poly(N,v).nth(0),S.Poly(N,v).nth(1)
assert S.degree(S.gcd(N0,N1),a)==0
print('v=',vd,flush=True)
frel=e**2-e+vd
def apert(f):
    f=S.cancel(f.subs(v,vd))
    f=S.Poly(f,e,domain=S.QQ.frac_field(a))
    return S.rem(f,S.Poly(frel,e,domain=S.QQ.frac_field(a))).as_expr()
mu={x:S.factor(I(Y*(Y-1)*S.prod(Y-z for z in simm if z!=x)*H)) for x in simm}
mu[e]=S.factor(I(H4*(Y-1+e)))
rho=lambda z:z*(3*z*z-10*a*z+9*a*a)/12
w={z:S.cancel(mu[z].subs(v,vd)*rho(z)) for z in mu}
def qr(p):
 p=S.Poly(p,r)
 return p.nth(0),p.nth(1)
def check(ff):
 for f,n in S.factor_list(ff,a)[1]:
    f=S.Poly(f,a)
    if f.degree()<2:
        rr=S.solve(f.as_expr(),a)
        assert all(x in (0,Q(1,3),Q(2,5),Q(1,2),Q(2,3))for x in rr)
        print('lin root',rr,n,flush=True)
        continue
    assert all(c.is_Integer for c in f.all_coeffs())
    for p in (11,13,17,19,29):
        if int(f.LC())%p and all(int(f.eval(j))%p for j in range(p)):
            print('rootless factor degree',f.degree(),'exp',n,'mod',p,
                  tuple(int(c)%p for c in f.all_coeffs()),flush=True);break
    else:
        raise AssertionError(f'No verified prime for factor {f.degree()}')
choices=[(b,c),(b,e),(c,b),(c,e),(e,b),(e,c),(e,1-e)]
for i,(d,u) in enumerate(choices):
    print('case',(d,u),flush=True)
    C=(t-a)*(r-d)*w[d]+(a-d)*(r-t)*w[t]+(d-t)*(r-a)*w[a]
    others=[z for z in (b,c,e,1-e)if z!=d and z!=u]
    blind=S.prod(Y-z for z in others)
    if sorted(map(str,others))==sorted(map(str,(e,1-e))):blind=H
    DD=I((Y-1)*(Y-r)*blind*J(Y*(Y-a)*(Y-t)*(Y-d)))
    C0,C1=map(apert,qr(C));D0,D1=map(apert,qr(DD))
    lin=S.cancel(S.rem(S.Poly(C1*D0-C0*D1,e,domain=S.QQ.frac_field(a)),S.Poly(frel,e,domain=S.QQ.frac_field(a))).as_expr()).as_numer_denom()[0]
    f=S.factor(S.resultant(lin,den*(e**2-e)+num,e)if lin.has(e) else lin)
    print('reduced',S.factor(lin),flush=True)
    print('univariate',f,flush=True)
    check(f)
