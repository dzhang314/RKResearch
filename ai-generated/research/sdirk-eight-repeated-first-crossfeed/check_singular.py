import arith_model as A
from sympy import Symbol,degree
from functools import lru_cache
from flint import fq_default_ctx,fq_default_poly_ctx,nmod_poly,fmpz_mod_poly_ctx,fmpq_mpoly_ctx,fmpq_poly,fmpq
K=A.K;m=A.m;u=A.u
ss=Symbol('u');tt=Symbol('m')

for scalar,pdeg in [(A.delta,2),(A.U*(A.q-1)-A.V*(A.k-1),7)]:
    rest=A.ff(scalar.numer)
    assert [(str(g),e) for g,e in rest[:2]]==[('u',3),('u - 2',1)] and len(rest)==3
    assert degree(rest[2][0],ss)==pdeg and rest[2][1]==1
select=lambda f:max((g for g,e in A.ff(f.numer)),key=lambda g:degree(g,ss))
df=select(A.delta);bf=select(A.U*(A.q-1)-A.V*(A.k-1))
MR=fmpq_mpoly_ctx.get(('m','u'),'lex')
cv=lambda e:MR.from_dict({ds:fmpq(str(c)) for ds,c in K(e).numer.items()})
res=cv(df).resultant(cv(bf),1).to_dict()
r=fmpq_poly([res.get((i,0),fmpq(0)) for i in range(max(a for a,b in res)+1)])
ps=[(f,e) for f,e in r.factor()[1]]
assert sorted((f.degree(),e) for f,e in ps)==[(1,2),(27,1)]
assert df.subs(tt,2).expand()==(46-69*ss)
lin=next(f for f,e in ps if f.degree()==1)
assert lin[0]+2*lin[1]==0
target=next(f for f,e in ps if f.degree()==27)
ds=K(df).numer;bs=K(bf).numer

class Bad(Exception):pass
def ck(b,msg):
 if not b:raise Bad(msg)

def check(p):
 mod=nmod_poly([int(c.numerator)*pow(int(c.denominator),-1,p)%p for c in target.coeffs()],p)
 ck(mod.degree()==27,'projection degree')
 f=mod.factor()[1]
 ck(all(e==1 for x,e in f),'inseparable m')
 for mod,_ in f:
  if mod.degree()==1:
   E=fq_default_ctx(p);m0=E(-int(mod[0])*pow(int(mod[1]),-1,p)%p)
  else:
   E=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)(list(map(int,mod.coeffs()))))
   m0=E.gen()
  R=fq_default_poly_ctx(E);x=R.gen()
  def c(v):return E(int(v.numerator))/E(int(v.denominator))
  mp=[m0**j for j in range(20)]
  def vp(f):
   return sum((c(q)*mp[i]*x**j for (i,j),q in f.items()),start=R.zero())
  a,b=vp(ds),vp(bs)
  ck(a.degree()==2 and b.degree()==7,'projective infinity')
  U=a.gcd(b);ck(U.degree()==1,'gap degree')
  u0=-U[0]/U[1]
  def ev(fr):
   return vp(fr.numer)(u0)/vp(fr.denom)(u0)
  k0,qs,ht,rt,DT,y1,x1=[ev(f) for f in [A.k,A.q,A.ht,A.rt,A.delta,A.U,A.X]]
  ck(ht!=0 and rt!=0 and k0!=0 and qs!=0 and DT==0 and k0!=1 and m0!=0 and u0!=0,'guard')
  t0=1-m0; t1=m0-1;t2=t1-u0;t3=t1-2*u0
  n=3*m0*m0/5;beta=3-m0
  L3=lambda t:t*(t*t-n)
  L4=lambda t:t**4-6*m0*m0*t*t/7+3*m0**4/35
  P3=lambda t:(t-beta)*((t-beta)**2-4)
  S=lambda t:ev(A.s0)+ev(A.s1)*t+ev(A.s2)*t*t
  J=(y1-x1*x)/(k0-1);h=E.one()/2
  T=L4(t1)*x-S(t1)*x*x-J*(x-h)
  ck(T.degree()==2,'terminal scale infinity')
  ck(L4(t0)!=0,'zero quartic constant')
  C=L3(t0)*J/L4(t0)
  def rw(t,g):
   # Quintic determinant with the H^2 common denominator multiplied on every row,
   # and a common extraneous H factored off before taking the determinant.
   return [2*g*P3(t)*x, -g*(g-h)*(t-t0)*x,
            (-(1-2*g)*L3(t)*x*x+g*(g-h)*C)//x]
  a,b,c0=[rw(t,rr*x) for t,rr in [(t1,E.one()),(t2,k0),(t3,qs)]]
  V=sum((a[j]*(b[(j+1)%3]*c0[(j+2)%3]-b[(j+2)%3]*c0[(j+1)%3]) for j in range(3)),start=R.zero())
  ck(T.gcd(V).degree()==0,'third reverse fit remains')
 return [x.degree() for x,e in f]

if __name__=='__main__':
    assert sorted(check(43))==[5,5,17]
    print('singular cross-fed corner: degree-27 quotient passes all modular exclusions')
