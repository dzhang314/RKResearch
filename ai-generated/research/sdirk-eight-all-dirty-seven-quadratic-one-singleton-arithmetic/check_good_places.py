"""Fixed good-place checks for all five large S,S,S arithmetic factors."""
from projection import branches
import sympy as S
from flint import nmod_poly as P
from math import isqrt

def specialize(f,p,hs,at):
    j=0 if hs is None else 1
    ii=-1 if hs is not None and at is not None else j
    cs=[0]*(1 if ii<0 else f.degrees()[ii]+1)
    for ix,a in f.to_dict().items():
      z=int(a)
      if hs is not None and ix[0]:z=z*pow(hs,ix[0],p)%p
      if at is not None and ix[1]:z=z*pow(at,ix[1],p)%p
      cs[0 if ii<0 else ix[ii]]+=z
    return P(cs,p) if ii>=0 else cs[0]%p
def liftq(P1,P2,W):
    j,a,_=P2.xgcd(W)
    if j.degree()!=0:raise ZeroDivisionError()
    return (P1*a)%W
def solve3(A,p):
    A=[[a%p for a in s] for s in A]
    for i in range(3):
      j=next((j for j in range(i,3) if A[j][i]),None)
      if j is None:raise ZeroDivisionError()
      A[i],A[j]=A[j],A[i]
      k=pow(A[i][i],-1,p)
      A[i]=[a*k%p for a in A[i]]
      for j in range(3):
         if i!=j:
            k=A[j][i];A[j]=[(a-k*b)%p for a,b in zip(A[j],A[i])]
    return [x[-1] for x in A]
def check(p,h,u,mode):
    Z=lambda x:x%p
    def I(a):
      a=Z(a)
      if not a:raise ZeroDivisionError()
      return pow(a,-1,p)
    D=lambda z:Z(-2+z+4*z*z-z**3)
    k=lambda z:Z(1+2*z-z*z)
    N=lambda z:Z((1+4*z-4*z*z)*D(z)+4*z*z*(3*z-2))
    try:
      H=Z(2*h);m=h+1
      de=D(u)
      if not Z(h*m*u*(u-1)*(u-2)*k(u)*N(u)*(3*u-2)):return None
      y=P([0,1],p)
      R=(1+2*y-y*y)*I(2)+Z((3*u-2)*I(de))*y*(y-u)
      if R.degree()!=2:return None
      W=R*I(int(R[2]))
      t=y-h
      L3=t**3-Z(3*m*m*I(5))*t
      L4=t**4-Z(6*m*m*I(7))*t*t+Z(3*m**4*I(35))
      F=liftq(L3,L4,W)
      P3,re=divmod(L3-F*L4,W)
      assert not re
      de1,re=divmod(P3,y-H)
      if re or de1.degree()!=2:return None
      dt=de1*I(int(de1[2]))
      sig=Z(-int(dt[1]))
      Q3=y*(y-u)*(y-2*u%p)
      remp=liftq(L4,Q3,W)
      if remp.degree()!=1:return None
      U=int(remp[1])
      s=Z(-int(remp[0])*I(U))
      H4=U*Q3*(y-s)
      C,re=divmod(L4-H4,R)
      if re or C.degree()>2:return None
      if mode=='triple star':
          if sig!=Z(4*h-2):return None
          roots=dt.roots()
          if len(roots)!=2:return None
          d1,d2=[int(x) for x,e in roots]
          rs=[(d1,d2),(d2,d1)]
      elif mode=='triple arithmetic':
          d1=Z((sig+H)*I(3));d2=Z(2*d1-H)
          if dt(d1) or dt(d2):return None
          rs=[(d1,d2)]
      elif mode=='extra D A2':d1=Z((s+H)*I(2))
      elif mode=='extra D A3':d1=Z(2*(s-h))
      else:
          assert mode=='extra D star'
          d1=Z(4*h-2-s)
      if mode.startswith('triple'):
          dset=[H,d1,d2]
      else:
          d2=Z(sig-d1)
          if dt(d1) or dt(d2):return None
          dset=[H,d1,d2]
      sset=[0,u,Z(2*u),s]
      if len(set(dset+sset))!=7:return None
      if not all(int(R(x)) for x in sset):return None
      for x in dset:
          if not int(L4(x)):return None
      def phases(v,star):
          if star:
            if not Z(v*(v-1)*(v-2)*k(v)):raise ZeroDivisionError()
            return Z(k(v)*I(2)),Z(k(v)*I(2))
          if not Z(v*k(v)*D(v)*N(v)*(3*v-2)):raise ZeroDivisionError()
          return Z(k(v)*I(2)),Z(N(v)*I(2*D(v)))
      if mode.startswith('triple'):
          dd=[]
          for D1,D2 in rs:
            v=Z(H-D1)
            xs=[H,D1,D2];gg=[I(2)]+list(phases(v,mode=='triple star'))
            A=[[j*int(C(x)),j*j,-j*int(R(x)),int(L4(x))] for x,j in zip(xs,gg)]
            X,Y,ZB=solve3(A,p)
            fail=Z(Y-X*ZB)
            if not fail:return None
            dd.append(fail)
          return tuple(sorted(dd))
      if mode=='extra D A2':
        v=Z(H-d1);gD,gS=phases(v,False)
      if mode=='extra D A3':
        v=Z((H-d1)*I(2));gS,gD=phases(v,False)
      if mode=='extra D star':
        v=Z(H-d1);gD,gS=phases(v,True)
      lm=Z(int(R(s))*I(gS))
      gT=Z(lm*I(2))
      B=Z((int(L4(H))-gT*int(C(H)))*I(gT*(gT-int(R(H)))))
      g=Z(lm*gD)
      fail=Z(int(L4(d1))-g*int(C(d1))-B*g*(g-int(R(d1))))
      return (fail,) if fail else None
    except ZeroDivisionError:
      return None

FIXED={
 'triple star':(36,47,43,((17,(31,31)),)),
 'triple arithmetic':(63,37,19,((4,(25,)),)),
 'extra D A2':(117,19,2,((17,(16,)),)),
 'extra D A3':(117,53,22,((40,(22,)),)),
 'extra D star':(117,41,4,((27,(26,)),)),
}
def run():
    covered=set()
    for mode,ff,ab,_ in branches():
        deg,p,h,expected=FIXED[mode]
        assert p>7 and all(p%d for d in range(2,1+isqrt(p)))
        [(f,e)]=[(g,n) for g,n in ff if g.total_degree()>12]
        X=S.Symbol('h')
        pol=S.Poly.from_dict({(ix[0],):int(q) for ix,q in f.to_dict().items()},X,domain=S.QQ)
        assert e==1 and pol.degree()==deg and pol.is_irreducible
        px=specialize(f,p,None,0)
        assert px.degree()==deg and not px(h) and px.derivative()(h)
        t=specialize(ab[0],p,h,None);q=specialize(ab[1],p,h,None)
        assert t.degree()==ab[0].degrees()[1]==9
        G=t.gcd(q)
        roots=G.roots()
        assert sum(e for _,e in roots)==G.degree()
        out=tuple((int(u),check(p,h,int(u),mode)) for u,_ in roots)
        assert out==expected,out
        print(mode,'fixed simple place',p,h,out,flush=True)
        covered.add(mode)
    assert covered==set(FIXED)
if __name__=='__main__':run()
