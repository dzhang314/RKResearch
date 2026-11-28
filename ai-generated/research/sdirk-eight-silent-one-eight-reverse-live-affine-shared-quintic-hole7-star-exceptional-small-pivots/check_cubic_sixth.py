"""Complete lambda U=d2, actual seventh hole with exceptional fifth and cubic sixth."""
from flint import fq_default_ctx, fq_default_poly_ctx, nmod_poly, fmpz_mod_poly_ctx
from collections import Counter
from field_tools import Ext,tail_cuts,gcd
from check_small_pivots import factor
from flint import fmpq, fmpq_mpoly_ctx,fmpq_poly
from itertools import combinations
from functools import lru_cache
from functools import reduce
C=fmpq_mpoly_ctx.get(("s","gamma"),ordering="lex")
s,g=C.gens()

def mul(a,b):
 z=[C.constant(0)]*(len(a)+len(b)-1)
 for i,c in enumerate(a):
  for j,d in enumerate(b):z[i+j]+=c*d
 return z

def ev(H,x):
 return sum(a*x**j for j,a in enumerate(H))

def coefs():
 d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
 d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
 d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
 return d0,d1,d2,4*(1-2*d0)/3,8*(d2-70*g**4)

@lru_cache(None)
def fixed_profile():
 d0,d1,d2,l0,l1=coefs()
 y=(3*s-1)/2
 D=d0+d1*s+d2*s*s
 U=l0+l1*y+fmpq(4,3)*D*(5-s)
 V=d2*(s+y)+d1
 E2=[2*g*g,-4*g,C.constant(1)]
 E3=mul(E2,[-g*s,C.constant(1)])
 C3=[6*g**3,-18*g*g,9*g,C.constant(-1),C.constant(0)]
 L=(8*U-64*V)*D-(9*U-8*V)*l1
 H=[g*U*a+8*b for a,b in zip(C3,mul(E3,[g*(d1+d2*s),d2]))]
 assert H[-1]==8*d2
 m=[sum(a/(i+j+1) for i,a in enumerate(H)) for j in range(4)]
 F=[m[0]*m[2]-m[1]**2,m[0]*m[3]-m[1]*m[2],m[1]*m[3]-m[2]**2]
 return L,F,(g,d2,D,U,V,m[0]),m,H

def diag():
 L,F,gs,m,H=fixed_profile()
 R=[]
 for j,k in combinations(range(3),2):
  z=F[j].resultant(F[k],0)
  assert z.degrees()==(0,180)
  tb=z.to_dict();R.append(fmpq_poly([tb.get((0,l),0) for l in range(181)]))
 Q=R[0].gcd(R[1]).gcd(R[2])
 G=fmpq_poly([0,1])
 Pi=fmpq_poly([1,-20,180,-840,1400])/1400
 D2=fmpq_poly([1,-20,180,-840,1680])/1680
 P,rem=divmod(Q,G**12*Pi**8*D2**12)
 assert rem==0 and P.degree()==66
 return P,F,gs,m,H

def red(p,q):
 return int(q.p)*pow(int(q.q),-1,p)%p

def cp(F,g,K,W,p):
 ks=[K(0)]*(F.degrees()[0]+1)
 for (i,j),c in F.to_dict().items():ks[i]+=red(p,c)*g**j
 return W(ks)

def check():
 p=1009
 a,F,gs,m,H=diag()
 diagp=nmod_poly([red(p,z) for z in a.coeffs()],p)
 assert diagp.degree()==66 and diagp.leading_coefficient()==1
 fac=factor(diagp)
 assert sorted((u.degree(),e) for u,e in fac)==[(2,1),(3,1),(4,1),(9,1),(16,1),(32,1)]
 Cnt=Counter()
 for G,e in fac:
  K=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)([int(c) for c in G.coeffs()]),var='g')
  W=fq_default_poly_ctx(K);gg=K.gen()
  cv=lambda t:cp(t,gg,K,W,p)
  FF=list(map(cv,F));q=FF[0].gcd(FF[1]).gcd(FF[2])
  assert [k.degree() for k in FF]==[6,6,6] and q.degree()==1
  for Q,f in factor(q):
   A=Ext(K,W,Q);S=A.gen()
   gg0=A(gg);z=lambda t:A(cv(t))
   U,V,D,d2=[z(gs[i]) for i in [3,4,2,1]]
   m0,m1=z(m[0]),z(m[1])
   assert all(t!=0 for t in [gg0,U,V,D,d2,m0])
   r=m1/m0;y=(3*S-1)/2;w=gg0*(y-V/d2)
   Hp=list(map(z,H));Hp=[u/Hp[-1] for u in Hp]
   for mode in ('star','arith','silent8'):
    t,B,V=tail_cuts(A,gg0,r,S,y,w,Hp,mode)
    d=gcd(t,reduce(gcd,B));e=gcd(d,V)
    assert d==e==[A(1)]
    Cnt[mode]+=1
 assert Cnt==Counter({"star":6,"arith":6,"silent8":6})
 print("lambda U=d2: exact gamma66, all full-degree s fibers and all three signed rear modes excluded",flush=True)


if __name__=="__main__":
 check()
