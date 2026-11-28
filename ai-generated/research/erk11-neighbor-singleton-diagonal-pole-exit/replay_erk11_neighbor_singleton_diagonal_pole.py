#!/usr/bin/env python3
"""Entire neighboring singleton diagonal-pole replay. Requires python-flint 0.9.0."""
import flint
from itertools import combinations
qp=flint.fmpq_poly
N=[[3,-32,108,-144,66],[-32,388,-1404,1956,-924],[108,-1404,5316,-7644,3696],
   [-144,1956,-7644,11256,-5544],[66,-924,3696,-5544,2772]]

def monic(f):
    return f/f[f.degree()]

def number_field(F):
    F=monic(F)
    qone=qp([1])
    qzero=qp()
    def trim(xs):
        while xs and xs[-1].is_zero():
            xs.pop()
        return xs
    def inv(x):
        r,s=F,x
        y,z=qzero,qone
        while not s.is_zero():
            h,v=divmod(r,s)
            r,s=s,v
            y,z=z,(y-h*z)%F
        assert r.degree()==0 and r[0]!=0
        return (y/r[0])%F
    def rem(f,g):
        out=f[:]
        i=inv(g[-1])
        while len(out)>=len(g):
            shift=len(out)-len(g)
            c=(out.pop()*i)%F
            for j in range(len(g)-1):
                out[shift+j]=(out[shift+j]-c*g[j])%F
            trim(out)
        return out
    def gcd(f,g):
        while g:
            f,g=g,rem(f,g)
        assert f
        c=inv(f[-1])
        return [(x*c)%F for x in f]
    def from_biv(f):
        c=f.to_dict()
        na,nd=f.degrees()
        return trim([qp([c.get((i,j),0) for i in range(na+1)])%F for j in range(nd+1)])
    def at_biv(f,v):
        z=qzero
        for u in reversed(from_biv(f)):
            z=(z*v+u)%F
        return z
    return from_biv,at_biv,gcd

def compact_pole():
    P=qp
    C=flint.fmpq_mpoly_ctx.get(('a','b','X'))
    a,b,X=C.gens()
    R=flint.fmpq_mpoly_ctx.get(('a','b'))
    aa,bb=R.gens()
    rr=R.from_dict({})
    d=1-b
    W=X**2*(X-a)**2
    V=(1-X)**2*(X-d)**2
    def primitive(p):
        return C.from_dict({(i,j,k+1):c/(k+1) for (i,j,k),c in p.to_dict().items()})
    def integrate(p,shift=0):
        u={}
        for (i,j,k),c in p.to_dict().items():
            u[(i,j,0)]=u.get((i,j,0),0)+c/(k+shift+1)
        return C.from_dict(u)
    def width_poly(p):
        assert p.degrees()[2]<=0
        return R.from_dict({(i,j):c for (i,j,k),c in p.to_dict().items()})
    p=primitive(W)
    q=integrate(V)-primitive(V)
    H=integrate(p*V)
    C1=integrate(p*V,1)
    C2=integrate(W*q,1)
    J=integrate(p*q)
    assert C1-C2==J and H==integrate(W*q)
    I0,I1,I2=[integrate(W*V,k) for k in range(3)]
    T=H**2*I2-2*H*C2*I1+C2**2*I0
    epoch=H*X-C2
    w=(1-X)*(X-d)
    M=[width_poly(T*integrate(p*w*epoch,j)-J*H*integrate(W*w*epoch**2,j))
       for j in range(3)]
    assert all(f.degrees()==(10,9) for f in M)
    assert -M[2]+(2-bb)*M[1]-(1-bb)*M[0]==rr
    for poly in M[:2]:
        dct=poly.to_dict()
        U=P()
        aa_deg,bb_deg=poly.degrees()
        for k in range(bb_deg+1):
            U=U.gcd(P([dct.get((j,k),0) for j in range(aa_deg+1)]))
        assert U==P([1])
    re=M[0].resultant(M[1],'b')
    assert re.degrees()[1]==0
    dic=re.to_dict()
    univ=P([dic.get((i,0),0) for i in range(re.degrees()[0]+1)])
    fac=sorted((t.degree(),m) for t,m in univ.factor()[1])
    assert univ.degree()==176
    assert fac==[(1,8),(2,2),(2,2),(8,1),(8,1),(8,9),(12,1),(60,1)]

    return M[0],M[1],width_poly(H),width_poly(J),univ.factor()[1]
def setup(C,a,b):
 x=C.gen();y=1-x;zero=C([0])[0];one=C([1])[0];d=1-b
 w=x*x*(x-a)**2;V=y*y*(x-d)**2
 def int_(r,k=0):return sum((r[i]/(i+k+1) for i in range(len(r))),zero)
 def primitive(p):return C([zero]+[p[i]/(i+1) for i in range(len(p))])
 P=primitive(w);Q=int_(V)-primitive(V)
 H=int_(P*V);C1=int_(P*V,1);C2=int_(w*Q,1);J=int_(P*Q)
 I0,I1,I2=[int_(w*V,i) for i in range(3)]
 s=C2/H;z=(I2-s*I1)/(I1-s*I0)
 A=s*(s-a);B=(1-s)*(s-d)
 vv=J*B*(s-z)/(C1-z*H)
 L0=[(s**(i+1)-P(s)/P(a)*a**(i+1))/A for i in range(5)]
 L1=[a**(i+1)/P(a) for i in range(5)]
 R0=[((1-s)*s**i-Q(s)/Q(d)*(1-d)*d**i)/B+vv*(1-d)*d**i/Q(d) for i in range(5)]
 D0=[one,zero,zero,zero,zero];Da=[(i+1)*a**i for i in range(5)]
 E0=[one]*5;Ed=[d**i-((1-d)*i*d**(i-1) if i else zero) for i in range(5)]
 def dt(l,r):return sum((l[i]*N[i][j]*r[j] for i in range(5) for j in range(5)),zero)
 S=[(dt(l,e0),dt(l,e1)) for l in (L0,L1) for e0,e1 in [(E0,Ed)]]
 K=[(dt(l,E0),dt(l,Ed)) for l in (D0,Da)]
 return (a,b,d,s,z,vv,J,L0,L1,R0,D0,Da,E0,Ed,S,K,H,I0,I1,I2),dt
class Ops:
    def __init__(self,C):
        self.C=C;self.u=C.gen(); self.one=C([1]);self.z=C([])
    def add(self,f,g):
        z=self.z
        h=[(f[i] if i<len(f) else z)+(g[i] if i<len(g) else z) for i in range(max(len(f),len(g)))]
        while h and not h[-1]:h.pop()
        return h
    def mul(self,f,g):
        if not f or not g:return []
        h=[self.z]*(len(f)+len(g)-1)
        for i,a in enumerate(f):
            for j,b in enumerate(g):h[i+j]+=a*b
        while h and not h[-1]:h.pop()
        return h
    def sub(self,f,g):return self.add(f,self.scale(g,-1))
    def scale(self,f,k):return [k*t for t in f]
    def prod(self,fs):
        p=[self.one]
        for f in fs:p=self.mul(p,f)
        return p
    def sum(self,fs):
        p=[]
        for f in fs:p=self.add(p,f)
        return p
    def linear(self,a):return [-self.C([a]),self.one]
    def ev(self,f,a):
        p=self.z
        for t in reversed(f):p=self.C([a])*p+t
        return p
    def monicquot(self,f,g):
        assert g[-1]==self.one
        f=f[:];q=[self.z]*max(0,len(f)-len(g)+1)
        while len(f)>=len(g):
            lc=f.pop();j=len(f)-len(g)+1
            q[j]=lc
            for i,t in enumerate(g[:-1]):f[i+j]-=lc*t
        assert all(t.is_zero() for t in f)
        return q
def det3(A):
 x,y,z=A
 return x[0]*(y[1]*z[2]-y[2]*z[1])-x[1]*(y[0]*z[2]-y[2]*z[0])+x[2]*(y[0]*z[1]-y[1]*z[0])

def polydata(C,a,b,side):
 data,f=setup(C,a,b)
 a,b,d,s,z,v,J,L0,L1,R0,D0,Da,E0,Ed,S,K,*_=data
 X=Ops(C);u=X.u;zz=X.z
 U=[C([v])+u*w for v,w in zip(L0,L1)]
 DL,RD=[C([p])+u*q for p,q in zip(*S)]
 R11=[RD*E0[i]-DL*Ed[i] for i in range(5)]
 if side:
  w,op,x0,sc=a,d,s,s
  l0,l1=[sum((q[i]*N[i][j]*R11[j] for i in range(5) for j in range(5)),zz) for q in (D0,Da)]
  Epr=[zz]+[sum((N[i][j]*R11[j] for j in range(5)),zz) for i in range(5)]
 else:
  w,op,x0,sc=b,1-a,1-z,1-s
  l0,l1=DL,RD
  Epr=X.sum([X.scale(X.prod([[zz,X.one]]+[X.linear(1)]*j),(-1)**j*sum((U[i]*N[i][j] for i in range(5)),zz)) for j in range(5)])
 h=w/2
 xx=[zz,X.one]
 B0=X.prod([xx,X.linear(w),X.linear(h)])
 B1=X.mul(X.linear(h),[w*l0,l1-l0])
 phi=[zz,zz,C([w]),-X.one]
 pshape=[zz,zz,zz,C([10*w*w]),C([-15*w]),C([6])]
 E=X.monicquot(X.sub(X.scale(Epr,w**5),X.scale(pshape,X.ev(Epr,w))),X.mul(xx,X.linear(w)))
 S0=X.scale(X.mul(X.linear(w),X.linear(h)),-w*E[0])
 S1=X.monicquot(X.scale(X.sub(X.scale(E,B1[0]),X.scale(B1,E[0])),w),xx)
 mt=X.prod([xx, X.linear(1), X.linear(w), X.linear(op)])
 mt=X.scale(mt,-1)
 cols=[phi,X.mul(xx,B0),X.mul(xx,B1),B0,B1]
 A=[]
 for j in range(3):
  row=[]
  for c in cols:
   r=X.mul(mt,c)
   row.append(u*sum((r[k]/(j+k+1) for k in range(len(r))),zz)-(J/v)*sc**j*X.ev(c,sc))
  A.append(row)
 O=[w*x0*(x0-w)*E[0],x0*X.ev(S0,x0),x0*X.ev(S1,x0),X.ev(S0,x0),X.ev(S1,x0)]
 assert all((o%l0).is_zero() for o in O)
 O=[o//l0 for o in O]
 det=det3([r[:3] for r in A])/(u**2)
 NN=[]
 for j in (3,4):
  NN.append([-det3([[r[k] if k!=i else r[j] for k in range(3)] for r in A])/(u**2) for i in range(3)])
 gg=[sum((c*f for c,f in zip(NN[j],O[:3])),zz)+det*O[3+j] for j in range(2)]
 if side:
  assert all((g%u).is_zero() for g in gg)
  gg=[g//u for g in gg]
 n,m=-gg[0],gg[1]
 c=[m*v+n*w for v,w in zip(*NN)]
 p1=m*c[2]-n*c[1]
 p0=n*c[0]-h*p1
 return dict(E=E,B0=B0,B1=B1,dt=det,gg=gg,n=n,m=m,p0=p0,p1=p1,A=A,O=O,side=side,l0=l0,l1=l1,cols=cols,NN=NN)
def fields(C,pol):
 for f,m in pol.factor()[1]:
  if f.degree()==1:
   C1=C; u=-f[0]/f[1]; z=C1([0])[0]
   conv=lambda q:C1([int(q)])[0]
  else:
   k=flint.fq_default_ctx(modulus=f,fq_type='FQ_NMOD')
   C1=flint.fq_default_poly_ctx(k);u=k.gen();z=k.zero()
   conv=lambda q:k(int(q))
  def ev(r):return sum((conv(c)*u**i for i,c in enumerate(r.coeffs())),z)
  yield f,m,C1,u,conv,ev

def state(B,ev):
 cs=[ev(B[i]) for i in ('l0','l1','dt','n','m')]
 if cs[0]==0:
  return 'slope0',cs
 M=[[ev(w) for w in r] for r in B['A']+[B['O']]]
 minors=[(I,det3([M[j][:3] for j in I])) for I in combinations(range(4),3)]
 z0=next(((I,v) for I,v in minors if v!=0),None)
 if cs[-1]==0:return ('raw both zero' if cs[-2]==0 else 'infinite t'),cs,z0
 t=cs[-2]/cs[-1]
 if t==0:return 'zero t',cs,z0
 if z0 is None:return 'rank lost',cs
 return 'fit',cs,t,z0,M

def fit(K,B,st,w,ev):
 assert st[0]=='fit'
 _,_,t,(jj,dd),M=st
 S=[M[i][:3]+[M[i][3]+t*M[i][4]] for i in jj]
 U,W,T=[-det3([[r[k] if k!=i else r[3] for k in range(3)] for r in S])/dd for i in range(3)]
 assert all(r[0]*U+r[1]*W+r[2]*T+r[3]+t*r[4]==0 for r in M)
 h=w/2;X=K.gen()
 Q=U*K([ev(c) for c in B['cols'][0]])+W*K([ev(c) for c in B['cols'][1]])+T*K([ev(c) for c in B['cols'][2]])+K([ev(c) for c in B['B0']])+t*K([ev(c) for c in B['B1']])
 P=w*(U+(X-h)*(T-t*W)/t)
 hull=K([ev(c) for c in B['B0']])+t*K([ev(c) for c in B['B1']])
 return P,Q,hull,t

def special(K,data,lp,R,ev):
 a,b,d,s,z,v,J,u,H,*_=data
 y0=1-z; X=K.gen();Y=1-X
 P,Q,BL,t=lp
 P=P(Y);Q=Q(Y)
 h=b/2;f=X*X*(b-X)/b
 if any(w==0 for w in (P(h),Q(h),P(y0),Q(y0))):return 'special calibration guard'
 Q=Q*(P(h)*f(h)/Q(h))
 E=K([ev(c) for c in R['E']])
 B0=K([ev(c) for c in R['B0']])
 B1=K([ev(c) for c in R['B1']])
 S0=-b*E[0]*(X-b)*(X-h)
 S1,rem=divmod(b*(E*B1(0)-E[0]*B1),X)
 assert rem.is_zero()
 k0=Q(y0)*S0(y0)
 k1=P(y0)*y0*(y0-b)*E(y0)*B1(0)+Q(y0)*S1(y0)
 if k1==0:return 'special slope guard', k0,k1
 tR=-k0/k1
 rem=(Q-P*f)%(B0+tR*B1)
 return 'special remainder', k0,k1,tR,rem,P,Q,B0+tR*B1,(Q-P*f)//(B0+tR*B1)

def routine(K,data,L,R):
 a,b,d,s,z,v,J,u,H,I0,I1,I2=data
 P,Q,BL,tl=L
 Pr,Qr,BR,tr=R
 X=K.gen();Y=1-X;c0=K([0])[0]
 mm=P[0]*Pr[1]+P[1]*(Pr[0]+Pr[1])
 if mm!=0:return 'alternate-P mark',mm
 Q1=Qr(Y)
 if any(Q[i]*Q1[j]-Q[j]*Q1[i]!=0 for i in range(5) for j in range(i+1,5)):return 'Q compatibility fails'
 if Q.degree()!=4:return 'Q degree loss',Q.degree()
 Ds=-BL*BR(Y)*(X-s)*(X-z)
 assert Ds.degree()==8 and Ds[8]==1
 Om=X*(X-1)*(X-a)*(X-d)
 f=Om*Q
 Mr=K([sum((f[i]/(i-j) for i in range(j+1, f.degree()+1)),c0) for j in range(f.degree())])
 V0=(Ds*Mr-(J/(u*v))*Q(s)*(Ds//(X-s)))%Q
 V1=(P*P*X*(X-1))%Q
 cc=[(i,j) for i,j in combinations(range(4),2) if V0[i]*V1[j]-V0[j]*V1[i]!=0]
 if cc:return 'ghost minors',cc
 idx=next((i for i in range(4) if V1[i]!=0),None)
 if idx is None:return 'ghost scale all zero',V0
 scale=-V0[idx]/V1[idx]
 if scale==0:return 'zero scale impossible?', V0
 if P.degree()!=1:return 'linear P lost'
 A=s*(s-a);B=(1-s)*(s-d)
 b9=J/(A*B*u*v)
 xi=-P[0]/P[1]
 if Ds(xi)==0:return 'shape root guard'
 Pa=scale*P;Qa=scale*Q
 lam=-Qa(xi)**2/Ds(xi)
 B3,rem=divmod(Qa**2+lam*Ds,Pa)
 assert rem.is_zero()
 ell=(Om//(X-a))/Om.derivative()(a)
 gg,ip,_=((X-a)*Q).xgcd(Ds)
 if gg.degree()!=0:return 'scalar pair weight inverse guard'
 pp=(P*P*X*(X-1)*ip)%Ds
 Ba=sum((ell[i]/(i+1) for i in range(len(ell))),c0)-scale*pp[7]/(gg[0]*Om.derivative()(a))-b9*ell(s)
 Ds_a=(a-d)*Ds(a)
 if Ds_a==0:return 'pair clock denominator'
 nu,mu,tau=[w(a)/Ds_a for w in (Pa,Qa,B3)]
 f=-a*a/2
 mk=(mu-f*nu)**2-(nu-f*Ba)*(tau-f*mu)
 return 'pair mark',mk,(Ba,nu,mu,tau,f,scale)

def width_place(F,e0,e1):
    p,a0=31,10
    C=flint.fmpz_mod_poly_ctx(p)
    red=lambda q:int(q.numerator)*pow(int(q.denominator),-1,p)%p
    f=C([red(q) for q in monic(F).coeffs()])
    assert f.degree()==60 and f(a0)==0 and f.derivative()(a0)!=0
    a=C([a0])[0]
    z=C([0])[0]
    def at(h):
       B=[z]*(h.degrees()[1]+1)
       for (i,j),q in h.to_dict().items():B[j]+=red(q)*a**i
       return C(B)
    E0,E1=at(e0),at(e1)
    assert E0.degree()==9
    g=E0.gcd(E1)
    assert g.degree()==1 and -g[0]/g[1]==5
    return C,a,C([5])[0]

def quotient_monic(f,g,F):
    rem=f[:]
    out=[qp()]*(len(f)-len(g)+1)
    assert g[-1]==qp([1])
    while len(rem)>=len(g):
        j=len(rem)-len(g)
        c=rem.pop()
        out[j]=c
        for i,w in enumerate(g[:-1]):rem[i+j]=(rem[i+j]-c*w)%F
    assert all(w.is_zero() for w in rem)
    return out

def small_factors(factors,E0,E1,H,J):
    summary=[]
    for f,m in factors:
        F=monic(f)
        deg=F.degree()
        if deg==60:continue
        if deg==1:
            assert F==qp([0,1])
        elif deg==2:
            assert F[1]**2-4*F[0]<0
        else:
            bv,_,gcd=number_field(F)
            g=gcd(bv(E0),bv(E1))
            dg=len(g)-1
            if (deg,m,dg)==(8,1,0):
                summary.append((8,1,0,'none'))
            else:
                live,name=(J,'J') if deg==12 else (H,'H')
                while len(g)>1:
                    h=gcd(g,bv(live))
                    assert len(h)>1
                    g=quotient_monic(g,h,F)
                summary.append((deg,m,dg,name))
    assert sorted(summary)==[(8,1,0,'none'),(8,1,1,'H'),(8,9,3,'H'),(12,1,1,'J')]
    print('small pole exits: a=0, negative discriminant quadratics, exact b-gcd degrees '
          '0,1(H),3(H),1(J)')

def large_factor(F,E0,E1):
    C,a,b=width_place(F,E0,E1)
    data,dt=setup(C,a,b)
    a,b,d,s,z,v,J,L0,L1,R0,D0,Da,E0,Ed,S,K,H,I0,I1,I2=data
    assert list(map(int,(a,b,d,s,z,v)))==[10,5,27,2,11,30]
    assert all(t!=0 for t in (a,b,a-d,H,J,I1-s*I0,s-z,C1_gap(C,a,b,s,z),s*(s-a),(1-s)*(s-d)))
    dd2=lambda X:X[0][0]*X[1][1]-X[0][1]*X[1][0]
    assert dd2(S)==6 and dd2(K)==9
    print('degree60 good place (31,10,5), all width guards; alternative slope/cross determinants 6,9')
    L,R=[polydata(C,a,b,side) for side in (True,False)]
    assert [[W[k].degree() for k in ('dt','n','m','p0','p1')] for W in (L,R)]==[[2,1,2,5,5],[2,2,3,7,7]]
    Pi=L['p0']*R['p1']+L['p1']*(R['p0']+R['p1'])
    assert Pi.degree()==12 and Pi[0]!=0
    exp={(25,1):1,(13,1):3,(24,23,1):1,(24,27,1):1,(15,1,1):1,(27,6,1):1}
    assert {tuple(map(int,f.coeffs())):m for f,m in Pi.factor()[1]}==exp
    print('unconditional u-projection retains degree12; all six residue factors accounted for')
    for f,m,K,u,conv,ev in fields(C,Pi):
        tag=tuple(map(int,f.coeffs()))
        l=state(L,ev)
        r=state(R,ev)
        vals=tuple(map(conv,(a,b,d,s,z,v,J)))+(u,)+tuple(map(conv,(H,I0,I1,I2)))
        SL=fit(K,L,l,conv(a),ev)
        if tag==(13,1):
            assert r[0]=='raw both zero'
            ex=special(K,vals,SL,R,ev)
            assert ex[0]=='special remainder' and tuple(map(int,ex[1:4]))==(17,24,29)
            assert list(map(int,ex[4].coeffs()))==[16,18,20]
            assert [list(map(int,h.coeffs())) for h in ex[5:]]==[[13,2],[11,9,25,12,2],[25,4,26,1],[6,21]]
            print(' u+13: guarded right fallback temporal t=29, remainder 20Y^2+18Y+16')
            continue
        assert r[0]=='fit'
        SR=fit(K,R,r,conv(b),ev)
        ex=routine(K,vals,SL,SR)
        if tag in ((25,1),(24,27,1)):
            assert ex==('alternate-P mark', (conv(21) if tag==(25,1) else 3*u+22))
            print(' factor',f,'restored actual temporal projectivity',ex[1])
        else:
            wanted={
                (24,23,1):(23*u+8,(25*u+1,7*u+26,4*u+4,9*u+12,conv(12),conv(13))),
                (15,1,1):(16*u+3,(17*u+1,2*u+4,24*u+1,26*u+6,conv(12),18*u+12)),
                (27,6,1):(30*u+23,(5*u+7,18*u+26,conv(20),22*u+8,conv(12),20*u+12)),
            }[tag]
            assert ex==('pair mark',*wanted) and ex[1]!=0
            print(' factor',f,'corrected ghost-fit and paid left pair mark',ex[1])
    print('all degree60 u factors excluded')

def C1_gap(C,a,b,s,z):
    x=C.gen()
    W=x*x*(x-a)**2
    V=(1-x)**2*(x-(1-b))**2
    w=W.integral()*V
    return (w*(x-z)).integral()(1)

def replay():
    E0,E1,H,J,fac=compact_pole()
    small_factors(fac,E0,E1,H,J)
    large_factor(next(f for f,m in fac if f.degree()==60),E0,E1)
    print('neighboring singleton diagonal pole excluded over ordered fields; other width curve/pivots not covered')

if __name__=='__main__':
    replay()
