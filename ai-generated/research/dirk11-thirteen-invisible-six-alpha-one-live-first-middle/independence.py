"""Small-field independence check only; never a characteristic-zero proof."""
from flint import nmod_poly
from math import comb
from itertools import permutations
from sys import argv
p=int(argv[1]) if len(argv)>1 else 103
F=lambda x:nmod_poly(x,p)
Y=F([0,1]);one=F([1]);zero=F([])
J4=F([1,-14,56,-84,42]);J5=F([-1,20,-120,300,-330,132])
inv=lambda x:pow(int(x),-1,p)
def I(f):return F([0]+[int(a)*inv(i+1)%p for i,a in enumerate(f.coeffs())])
def div(f,g):
 q,r=divmod(f,g)
 assert not r
 return q
def quot(f,g,h):
 d,i,j=g.xgcd(h)
 if d.degree()!=0:raise ZeroDivisionError
 return (f*i)%h
def rev(f):
 n=f.degree()
 return F([(-1)**i*sum(comb(j,i)*int(f[j])for j in range(i,n+1))for i in range(n+1)])
def wedge(*c):
 cs=[tuple(a[i]for i in range(len(c)))for a in c]
 return sum((-1)**sum(j>k for a,j in enumerate(pi)for k in pi[a+1:])*
            prod(cs[i][j]for i,j in enumerate(pi)) for pi in permutations(range(len(c))))%p
def prod(seq):
 v=1
 for a in seq:v=v*int(a)%p
 return v
def evalf(f,z):return int(f(z))
def coeff(f,i):return int(f[i]) if i<=f.degree() else 0
count=0; keep1=keep2=0; new1=new2=0
for v in range(2,p):
 jv=evalf(J4,v)
 if not jv:continue
 l=-evalf(J5,v)*inv(jv)%p
 T=(J5+l*J4)*inv(132)
 if not evalf(T,0) or not evalf(T,1) or T.gcd(T.derivative()).degree()>0:continue
 T4=div(T,Y-v)
 for bb,_ in T4.roots():
    B=int(bb);b=(1-B)%p;a=(1-v)%p
    R=div(T4,Y-B);c0,c1,c2=map(int,R.coeffs()[:3])
    if not c0 or not c2 or B==v:continue
    Fn=F([-c0*c1*c1,-12*c0*c1+12*c0*c2*c2-c1*c1*c2,-36*c0-4*c1*c2,12*c2])
    for ss,_ in Fn.roots():
      s=int(ss)
      if not s or (c1+6*s)%p==0 or (c2*s-c0)%p==0:continue
      r=6*c2*s*inv((c1+6*s)%p)%p
      if not r:continue
      m=F([s,r,1])
      if m.gcd(R).degree()!=0:continue
      P=Y*m;IP=I(P);I2P=I(IP)
      ell=quot(div(IP,Y),m,R);rho=quot(div(I2P,Y),m,R)
      if ell.degree()!=1:continue
      z=-coeff(ell,0)*inv(coeff(ell,1))%p
      P0=Y*R;P1=Y*P-P0
      L0,L1=(div(I(q0),Y)for q0 in (P0,Y*P0))
      M,W,Q=(quot(x,m,R)for x in (J4,L0,L1))
      if evalf(W,z)!=0 or evalf(rho,z)!=0:continue
      Wf,rf=div(W,Y-z),div(rho,Y-z)
      D4=div(L0*M-W*J4,R);D5=div(L1*M-Q*J4,R)
      Rv,lv,p0v=(evalf(x,v)for x in (R,L0,P0))
      H=Y*J4;hv=evalf(H,v)
      u=F([evalf(M,v),Rv]);cv=F([evalf(D4,v),lv])
      AV=((z-v)*((evalf(ell,v)*hv-evalf(IP,v)*u)*u+
                 cv*(evalf(P,v)*u-hv))-(evalf(I2P,v)*u-evalf(rho,v)*hv)*u)
      if AV.degree()<1:continue
      S=(Y-1)*(Y-v)*(Y-B)*R
      for tt,_ in AV.roots():
        t=int(tt)
        if not t:continue
        U=M+t*R
        if evalf(U,z)==0 or U.gcd(S).degree()>0:continue
        Uv=evalf(U,v);Uz=evalf(U,z)
        J=I(Y*rev(U));Jr=rev(J)
        assert evalf(J,b)==(evalf(I((1-Y)*U),1)-evalf(I((1-Y)*U),B))%p
        hb=evalf(H,b)
        if not hb:continue
        Kb=I(Y*(Y-b)*rev(U)); Kb-=evalf(Kb,b)*inv(hb)*H
        if wedge(S%U,(Y*S)%U,((Y-z)*rev(Kb))%U):continue
        cvv=evalf(D4+t*L0,v)
        d=cvv*inv(Uv)%p;k=hv*inv(Uv)%p
        lA=evalf(Kb,a)-d*a*(a-b)*Uv
        if lA%p:continue
        Ap= (Q-v*W)*jv+evalf(D5+t*L1-v*(D4+t*L0),v)*R
        Q5=Uz*Ap-evalf(Ap,z)*U
        if Q5.degree()<2:continue
        DQ=div(Q5,Y-z)
        xc=[int(x)for x,_ in DQ.roots() if int(x)!=z and evalf(U,int(x))]
        if not xc:continue
        qq=div(Uz*R-evalf(R,z)*U,Y-z)
        # Compare the two actual formulas for the first middle diagonal.
        cstar=-(d*d)*Uv*inv(jv)*inv(Uz)%p
        MID=Wf*(Y-v-d-ell+rf-Wf*((v-z)*(k-evalf(P,v))*inv(p0v)%p))+cstar*qq
        count+=1
        b1=[x for x in xc if wedge(S%U,(Y*S)%U,((Y-z)*(Y-x)*Jr)%U)==0]
        b2=bool(len(xc)==2 and Q5.degree()==3 and
                (not evalf(J,b) or not wedge(U%Q5,(Y*U)%Q5,((Y-v)*R)%Q5)))
        m1=[x for x in b1 if not evalf(MID,x)]
        m2=b2 and any(not evalf(MID,x)for x in xc)
        keep1+=len(b1);new1+=len(m1);keep2+=int(b2);new2+=int(m2)
        if b1 or b2:
          print('paid old has candidate',p,v,B,r,s,t,z,xc,'B1',b1,'mid',m1,'B2',b2,'mid',m2,flush=True)
print('all candidate comparison',p,count,'B1',keep1,new1,'B2',keep2,new2,flush=True)
