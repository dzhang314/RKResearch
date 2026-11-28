"""Complete exceptional star seventh-hole small pivot checks."""
from flint import (fmpq, fmpq_mpoly_ctx, fmpq_poly, fq_default_ctx,
                   fq_default_poly_ctx, nmod_poly, fmpz_mod_poly_ctx)
from itertools import combinations
from collections import Counter
from functools import reduce
from field_tools import Ext,mul,add,sc,hor,gcd,summ,tail_cuts

P12=[17,-825,20170,-320520,3616560,-30205800,190510800,-912794400,3303417600,
     -8812944000,16130016000,-16595712000,4741632000]
LEG=[[1],[-1,2],[1,-6,6],[-1,12,-30,20],[1,-20,90,-140,70]]
P=1009


def factor(f):
    parts=f.factor()[1]
    prod=f**0
    for p,e in parts:
        prod*=p**e
    assert prod*f.leading_coefficient()==f
    return parts


def early_K(g,r):
    return ((33600*g**3-16800*g*g+3360*g-280)*r**3
            +(-50400*g**3+25920*g*g-5400*g+480)*r**2
            +(20160*g**3-10800*g*g+2400*g-240)*r
            -1680*g**3+960*g*g-240*g+32)


def exact_ingress():
    C=fmpq_mpoly_ctx.get(("s","gamma"),ordering="lex")
    s,g=C.gens()
    d0,d1,d2,l0,l1=coefs(g)
    y=(3*s-1)/2
    D=d0+d1*s+d2*s*s
    U=l0+l1*y+fmpq(4,3)*D*(5-s)
    num,den=d2-2*d1,5*d2
    hu=sum(C.from_dict({(0,j):v for (i,j),v in U.to_dict().items() if i==k})
           *num**k*den**(3-k) for k in range(4))
    assert 3*hu==d2*sum(c*g**i for i,c in enumerate(P12))

    C=fmpq_mpoly_ctx.get(("Y","r","g"),ordering="lex")
    X,r,g=C.gens()
    evaluate=lambda p,y:sum(c*y**i for i,c in enumerate(p))
    l4=evaluate(LEG[4],g*X)
    k3=sum((2*j+1)*evaluate(L,r)*evaluate(L,g*X) for j,L in enumerate(LEG[:4]))
    e2=X*X-4*X+2
    for P0,eq in ((l4,2*(1400*g**4-840*g**3+180*g*g-20*g+1)),
                  (k3,early_K(g,r))):
        z=P0%e2
        slope=2*C.from_dict({(0,j,k):sum(z.to_dict().get((i,j,k),0) for i in (0,1))
                             for _,j,k in z.to_dict()})
        assert z.degrees()[0]==1 and slope==eq


def det(M):
 a,b,c=M
 return sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))

def coefs(g):
 d2=(1680*g**4-840*g**3+180*g*g-20*g+1)/4
 d1=-1680*g**4+1050*g**3-270*g*g+35*g-2
 d0=(2520*g**4-1680*g**3+540*g*g-120*g+11)/4
 return d0,d1,d2,4*(1-2*d0)/3,8*(d2-70*g**4)

def integ(P,i):
 return sum(v/(i+j+1) for j,v in enumerate(P))

def u0_fibers():
 p=P
 q=nmod_poly(P12,p)*pow(P12[-1],-1,p)
 assert q.degree()==12 and q.leading_coefficient()==1
 assert q.factor()[1]==[(q,1)]
 for g0,e in factor(q):
  Kg=fq_default_ctx(modulus=fmpz_mod_poly_ctx(p)([int(a) for a in g0.coeffs()]),var='g')
  Wr=fq_default_poly_ctx(Kg);g=Kg.gen()
  d0,d1,d2,e0,e1=coefs(g)
  assert g!=0 and d2!=0
  s=(d2-2*d1)/(5*d2); y=(3*s-1)/2
  D=d2*s*s+d1*s+d0
  assert D!=0
  C3=[6*g**3,-18*g*g,9*g,Kg(-1)]
  E2=[2*g*g,-4*g,Kg(1)]
  E3=mul(E2,[-s*g,Kg(1)]);E4=mul(E3,[-y*g,Kg(1)])
  cols=[C3,[8*x for x in E3],E4]
  r=Wr.gen()
  mom=[[integ(P,j+1)-r*integ(P,j) for P in cols] for j in range(3)]
  F=det(mom)
  assert F.degree()==3
  fr=factor(F)
  assert sorted((z.degree(),i) for z,i in fr)==[(1,1),(2,1)]
  for Q,n in fr:
   A=Ext(Kg,Wr,Q);r=A.gen()
   rows=[[A(t) for t in cc] for cc in mom]
   for i,j in combinations(range(3),2):
    ma,mb,mc=rows[i]; md,me,mf=rows[j]
    lead=mb*mf-mc*me
    if lead!=0:
     eta=(mc*md-ma*mf)/lead
     Lam=(ma*me-mb*md)/lead
     break
   else: raise AssertionError('full paid moment rank lost')
   consistent=all(a+b*eta+c*Lam==0 for a,b,c in rows)
   assert consistent
   lam=Lam*A(g)/8;L1=A(D)*(8-64*eta)-(9-8*eta)*A(e1)
   assert eta!=0 and Lam!=0 and L1!=0
   w=A(g)*(A(y)+(-eta-(9-8*eta)*A(d2)/L1)/lam)
   H=add(add(list(map(A,C3)),[A(x)*eta*8 for x in E3]),[A(x)*Lam for x in E4])
   H=[x/H[-1] for x in H]
   yield A,A(g),r,A(s),A(y),w,H

def rank0_fibers():
 K=fq_default_ctx(P,12,var='a')
 W=fq_default_poly_ctx(K);x=W.gen()
 Pi=1400*x**4-840*x**3+180*x*x-20*x+1
 assert Pi.degree()==4
 for G,eg in factor(Pi):
  assert G.degree()==1 and eg==1
  g=-G[0]/G[1]
  R=early_K(g,x)
  assert R.degree()==3
  for q,eq in factor(R):
   assert q.degree()==1 and eq==1
   r=-q[0]/q[1]
   d0,d1,d2,l0,l1=coefs(g)
   assert l1==0 and g!=0 and d2!=0 and l0!=0
   ls=list(map(W,LEG[:4]))
   KR=sum((2*j+1)*H(r)*H for j,H in enumerate(ls))
   KG=KR(g*x)
   H4=(6-18*x+9*x*x-x**3)/8
   E2=x*x-4*x+2
   Z=KG%E2
   assert Z.degree()==1 and Z[0]==-Z[1]
   lk=2*Z[1]
   E,rem=divmod(KG-lk*H4,E2)
   assert rem.is_zero() and E.degree()==1
   D=d0+d1*x+d2*x*x
   V=d1-d2/2+5*d2*x/2
   U=l0+4*D*(5-x)/3
   F=4*V*E*(5-x)/3-E[1]*U+V*lk
   A0=l0*E-lk*D
   assert F.degree()==3
   ff=factor(F)
   assert sorted((a.degree(),e) for a,e in ff)==[(1,1),(2,1)]
   for P0,ep in ff:
    B=Ext(K,W,P0)
    S=B.gen();y=(3*S-1)/2
    ee,dd,uu,vv,aa=map(B,(E,D,U,V,A0))
    assert all(z!=0 for z in (ee,dd,uu,aa))
    alpha,beta=ee/aa,-dd/aa
    eta=alpha*vv+beta*B(E[1]);lam=alpha*B(d2)
    pvt=dd*(8-64*eta)
    assert pvt!=0 and lam!=0
    assert eta*uu==vv
    w=B(g)*(y+(-eta-(9-8*eta)*(B(d2)-lam*uu)/pvt)/lam)
    Hp=summ((sc(list(map(B,[1,-20,90,-140,70])),alpha),sc(list(map(B,KR.coeffs())),beta)))
    Hp=[a/Hp[-1] for a in Hp]
    yield B,B(g),B(r),S,y,w,Hp

def check_all(label,fibers,num):
    hist=Counter()
    count=0
    for A,g,r,s,y,w,H in fibers():
        count+=1
        for mode in ("star","arith","silent8"):
            F,B,T=tail_cuts(A,g,r,s,y,w,H,mode)
            signed=gcd(F,reduce(gcd,B))
            assert signed==[A(1)] and gcd(signed,T)==[A(1)]
            hist[mode]+=1
    assert count==num
    assert hist==Counter({"star":num,"arith":num,"silent8":num})
    print(label, "complete physical mode exclusions",dict(hist),flush=True)


if __name__=="__main__":
    exact_ingress()
    check_all("U=0 gamma12 r=(1,2)",u0_fibers,2)
    check_all("Delta=0 gamma4 r3 s=(1,2)",rank0_fibers,24)
