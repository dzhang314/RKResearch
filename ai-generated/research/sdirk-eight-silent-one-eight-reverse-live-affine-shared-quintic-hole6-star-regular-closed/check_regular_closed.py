"""Full source-guarded exclusion, regular star-front actual hole six."""
from flint import (fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx, nmod_poly)
from compact_projection import (diagonal, projections, small_exact_guard, auxiliar,
                                reduce_coef)
from itertools import combinations
from collections import Counter

P=1009

def hor(a,x):
 z=x*0
 for b in reversed(a):z=z*x+b
 return z

def mul(a,b):
 if not a or not b:return []
 z=[a[0]*0]*(len(a)+len(b)-1)
 for i,c in enumerate(a):
  for j,d in enumerate(b):z[i+j]+=c*d
 return tr(z)

def add(a,b):
 if not a:return b[:]
 if not b:return a[:]
 z=[a[0]*0]*max(len(a),len(b))
 for i,c in enumerate(a):z[i]+=c
 for i,c in enumerate(b):z[i]+=c
 return tr(z)

def sc(a,b):return tr([t*b for t in a])
def tr(a):
 while a and a[-1]==0:a.pop()
 return a

def mod_monic(a,m):
 a=a[:]
 assert m[-1]==1
 while len(a)>=len(m):
  q=a[-1];i=len(a)-len(m)
  for j,b in enumerate(m):a[i+j]-=q*b
  tr(a)
 return a

def gcd(a,b):
 if not a:return mon(b)
 if not b:return mon(a)
 while b:
  b=mon(b)
  a,b=b,mod_monic(a,b)
 return a

def mon(a):return sc(a,a[-1].inverse()) if a else []

class Ext:
 def __init__(self,K,P,f):
  self.K,self.P,self.f=K,P,f
 def __call__(self,v):
  if isinstance(v,Elt):
   if v.E is self:return v
   raise TypeError("different extensions")
  return Elt(self,self.P(v))
 def gen(self):return Elt(self,self.P.gen())

class Elt:
 def __init__(self,E,p):self.E,self.p=E,p%E.f
 def __add__(self,x):return Elt(self.E,self.p+self.E(x).p)
 __radd__=__add__
 def __neg__(self):return Elt(self.E,-self.p)
 def __sub__(self,x):return self+-self.E(x)
 def __rsub__(self,x):return self.E(x)+-self
 def __mul__(self,x):return Elt(self.E,self.p*self.E(x).p)
 __rmul__=__mul__
 def __eq__(self,x):return self.p==self.E(x).p
 def inverse(self):
  d,p,q=self.p.xgcd(self.E.f)
  assert d.degree()==0
  return Elt(self.E,p/d[0])
 def __truediv__(self,x):return self*self.E(x).inverse()
 def __rtruediv__(self,x):return self.E(x)*self.inverse()
 def __pow__(self,n):
  z=self.E(1);a=self
  while n:
   if n%2:z*=a
   a*=a;n//=2
  return z
 def __repr__(self):return str(self.p)

def remainders(H,r,D,A):
 R=mod_monic(mul([-r,A(1)],list(map(A,[1,-20,90,-140,70]))),H)
 T=mod_monic(D,H)
 R+=[A(0)]*(4-len(R));T+=[A(0)]*(4-len(T))
 return [R[i]*T[j]-R[j]*T[i] for i,j in combinations(range(4),2)]

def missing(E0,H,r,c,x,A):
 E=E0[:]
 for k in (c,x):E=mul(E,[-k,A(1)])
 ac=hor(H,c)*(c-x)*hor(E0,c);ax=hor(H,x)*(x-c)*hor(E0,x)
 dn=mul(E,[ax*x-ac*c,ac-ax])
 return remainders(H,r,dn,A)


def mod_poly(q):
    z=nmod_poly([reduce_coef(c,P) for c in q.coeffs()],P)
    assert z.degree()==q.degree() and z.leading_coefficient()==1
    return z


def cv_r(p,g,B,W):
    coeff=[B(0)]*(p.degrees()[1]+1)
    for (i,j,k),c in p.to_dict().items():
        assert i==0
        coeff[j]+=reduce_coef(c,P)*g**k
    return W(coeff)


def cv_q(p,r,g,B,W):
    coeff=[B(0)]*(p.degrees()[0]+1)
    for (i,j,k),c in p.to_dict().items():
        coeff[i]+=reduce_coef(c,P)*r**j*g**k
    return W(coeff)


def fibers():
    Q,f,t,projs,guards,abc=projections()
    _,det,alpha,beta=guards
    pol=diagonal()
    aux=auxiliar(P)
    branch=Counter()
    for X,e in pol:
        n=X.degree()
        if (n,e) in ((1,42),(4,27)):
            # Those exact factors were identified as gamma and the true beta guard.
            continue
        Z=mod_poly(X)
        if n==144:
            assert Z.gcd(aux)==1
            branch[n]+=1
            continue
        if n in (4,12,30):
            guard=det if n==30 else alpha
            lower=small_exact_guard(projs,guard,X)
            assert lower==(3 if n==4 else 1)
        else:
            assert n==331
            lower=1
        factors=Z.factor()[1]
        full=nmod_poly([1],P)
        for p,k in factors:
            full*=p**k
        assert full==Z
        if n==331:
            assert sorted((p.degree(),k) for p,k in factors)==[
                (1,1),(19,1),(33,1),(65,1),(100,1),(113,1)]
        for p,k in factors:
            B=fq_default_ctx(modulus=fmpz_mod_poly_ctx(P)(
                [int(a) for a in p.coeffs()]),var="g")
            W=fq_default_poly_ctx(B)
            g=B.gen()
            cv=lambda q:cv_r(q,g,B,W)
            rows=[cv(x) for x in projs]
            assert [row.degree() for row in rows]==[15,16,23]
            common=rows[0].gcd(rows[1]).gcd(rows[2])
            assert common.degree()==lower
            if n!=331:
                # Matching exact cubic-guard lower bound and integral gcd upper bound.
                continue
            r=-common[0]/common[1]
            assert g!=0
            assert all(cv(v)(r)!=0 for v in (det,alpha,beta,abc[2]))
            assert 70*r**4-140*r**3+90*r*r-20*r+1!=0
            arr=[cv_q(h,r,g,B,W) for h in (Q,f,t)]
            assert [x.degree() for x in arr]==[2,1,1]
            cq=arr[0].gcd(arr[1]).gcd(arr[2])
            assert cq.degree()==1
            q=-cq[0]/cq[1]
            a,b,c=[cv(v)(r) for v in abc]
            h=cv(det)(r)
            H=h*W([6*g**3,-18*g*g,9*g,-1])+W([2*g*g,-4*g,1])*W([a,b,c])
            assert H.degree()==4 and H.leading_coefficient()==c!=0
            H=H/c
            assert H(r)!=0
            yield B,W,g,r,q,H
        branch[n]+=1
    assert branch==Counter({4:1,12:2,30:1,144:1,331:1})
    print("exact guard prune: degree-4 and both degree-12 via alpha; degree-30 via det;",
          "degree-144 via auxiliary; full degree-331 retained",flush=True)

def test_rear():
    count=Counter()
    ts=[x for x in range(P) if x*x%P==2]
    assert len(ts)==2
    for G,W,gg,r0,q0,H in fibers():
        q5=(3*q0-gg)/2
        a,b=[gg*(2+t) for t in ts]
        levels=list(H.coeffs())
        x=1-gg
        X=W.gen()
        for rear in ("star","arith","silent8"):
            if rear=="star":
                k=2-X**2;c=x-gg*(1+X);d=x-gg*(1-X)
                FN=(1-X)*hor(levels,c)-(1+X)*hor(levels,d)+2*X*k*H(x)
                pad=X*(1-X**2);degree=2;top=2*gg**4
            elif rear=="arith":
                k=1+2*X-X**2;c=x-gg*X;d=x-2*gg*X
                j=2+3*X-12*X**2+4*X**3
                q=-2+X+4*X**2-X**3
                FN=q*hor(levels,d)+2*j*hor(levels,c)-k*j*H(x)
                pad=X**2;degree=5;top=-8*gg**4
            else:
                k=1+2*X-X**2;c=x-gg*X;d=x+gg*k*(X-2)/2
                FN=(X-2)*hor(levels,c)-(2*X+k*(X-2))*H(x)
                pad=X;degree=4;top=gg**4
            q0p,rem=divmod(FN,pad)
            assert rem.is_zero() and q0p.degree()==degree and q0p.leading_coefficient()==top
            fac=q0p.factor()[1]
            complete=W(1)
            for zz,ee in fac:
                complete*=zz**ee
            assert complete*q0p.leading_coefficient()==q0p
            for z,m in fac:
                E=Ext(G,W,z)
                cc,dd,kk,cx=map(E,(c,d,k,x))
                a0,b0,s0,y0,r1=map(E,(a,b,q0,q5,r0))
                Hh=list(map(E,levels))
                def nodal(pts):
                    a=[E(1)]
                    for vv in pts:a=mul(a,[-vv,E(1)])
                    return a
                def pen(z):
                    return (cx-z)*hor(Hh,cc)-kk*(cc-z)*hor(Hh,cx)
                ep=[a0,b0,s0,y0]
                if rear=="silent8":
                    seq=[(8,missing(nodal(ep),Hh,r1,cc,cx,E))]
                else:
                    seq=[]
                    for i,pt in enumerate(ep):
                        xs=ep[:i]+ep[i+1:]+[dd]
                        seq.append((2+i,[pen(pt)]+missing(nodal(xs),Hh,r1,cc,cx,E)))
                    E0=nodal(ep+[dd])
                    D7=nodal(ep+[dd,cc,cx])
                    ac=hor(Hh,cc)*(cc-cx)*hor(E0,cc);ax=hor(Hh,cx)*(cx-cc)*hor(E0,cx)
                    seq.append((7,[ac-ax]+remainders(Hh,r1,D7,E)))
                for typ,cuts in seq:
                    assert any(a!=0 for a in cuts),(rear,typ,z.degree())
                    count[rear,typ]+=1
    assert count==Counter({("silent8",8):10,
                           **{("star",j):10 for j in (2,3,4,5,7)},
                           **{("arith",j):13 for j in (2,3,4,5,7)}})
    print("complete degree-331 at 1009:",dict(count),flush=True)


if __name__=="__main__":
    test_rear()
