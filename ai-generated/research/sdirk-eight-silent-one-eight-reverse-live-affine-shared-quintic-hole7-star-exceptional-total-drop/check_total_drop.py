"""Exact complete total sixth-clock drop, exceptional star actual hole seven."""
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

def cv(Q,w):
 a=Q.to_dict(); return [w(fmpq_poly([a.get((i,j),0) for j in range(Q.degrees()[1]+1)])) for i in range(Q.degrees()[0]+1)]

def tn(a):
 while a and not a[-1]:a.pop()
 return a

def exact_field(M):
 def norm(v):return v%M
 def inv(x):
  d,a,_=x.xgcd(M);assert d==fmpq_poly([1])
  return a
 def rem(a,b):
  a=tn(a[:]); b=tn(b[:]);d=inv(b[-1])
  while a and len(a)>=len(b):
   i=len(a)-len(b);h=norm(a[-1]*d)
   for j,z in enumerate(b):a[i+j]=norm(a[i+j]-z*h)
   tn(a)
  return a
 def gcd(a,b):
  while b:a,b=b,rem(a,b)
  return [norm(x*inv(a[-1])) for x in a] if a else []
 return norm,gcd,rem


def check():
    L,F,guards,m,H=fixed_profile()
    g0,d2,D,U,V,p0=guards
    assert L.degrees()==(5,8) and [f.degrees() for f in F]==[(6,16)]*3
    pi=fmpq_poly([1,-20,180,-840,1400])/1400
    d2=fmpq_poly([1,-20,180,-840,1680])/1680
    assert [(f.degree(),i) for f,i in pi.factor()[1]]==[(4,1)]
    assert pi.gcd(d2)==1
    R=[]
    for p in F:
        Q=L.resultant(p,0)
        assert Q.degrees()==(0,128)
        tab=Q.to_dict()
        R.append(fmpq_poly([tab.get((0,j),0) for j in range(129)]))
    q=R[0].gcd(R[1]).gcd(R[2])
    assert q==pi**4*d2**10
    # Actual d2 is nonzero, so the entire Pi field must be retained.
    nr,gcd,rem=exact_field(pi)
    polys=[tn(cv(P,nr)) for P in [U-8*V,*F]]
    assert [len(p)-1 for p in polys]==[3,6,6,6]
    assert reduce(gcd,polys)==[fmpq_poly([1])]
    print("exact gamma projection degrees 128,128,128; common Pi^4 d2^10;")
    print("complete Pi field, exact s gcd of U-8V and the three paid minors is one.")


if __name__=="__main__":
    check()
