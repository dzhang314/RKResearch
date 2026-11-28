# This file is evaluated after the exact old-clock field and its
# selected good reduction have been rebuilt by the frozen sibling.
tt=T.gen()
v,b,l,pr,qr,nn=map(et,(v,b,one,p0,q0,n))
zz,oo=et(0),et(1)
a,fb=l-v,l-b
L0=IP0[1:]
L1=prim([zero,*P0])[1:]
Q0=fit(L1)
def monic_div(f,monic):
    w=list(f); k=len(monic)-1
    assert monic[-1]==1
    y=[f[0].r.to(0)]*(len(f)-k)
    for i in range(len(w)-1,k-1,-1):
        y[i-k]=c=w[i]
        for j in range(k):w[i-k+j]-=c*monic[j]
    assert all(x==0 for x in w[:k])
    return y
d4=monic_div(pplus(mul(L0,M),pscale(mul(W0,J4p),-one)),R3)
d5=monic_div(pplus(mul(L1,M),pscale(mul(Q0,J4p),-one)),R3)
Mt,Rt,L0t,L1t,Wt,Qt,J4t,Hp=map(lift,(M,R3,L0,L1,W0,Q0,J4p,[zero,*J4p]))
Pt,IPt,I2Pt,Elt,Rht=map(lift,(P,IP,I2P,ell,rho))
UR=pplus(Mt,pscale(Rt,tt))
def rev(f):
    return [(-1)**i*sum(comb(j,i)*f[j]*l**(j-i)for j in range(i,len(f)))
            for i in range(len(f))]
UF=rev(UR)
UV=ev(UR,v)
cv=ev(lift(d4),v)+tt*ev(L0t,v)
jv=ev(J4t,v);hv=v*jv
Adj=(pr-v*qr)*((ev(Elt,v)*hv-ev(IPt,v)*UV)*UV
               +cv*(ev(Pt,v)*UV-nn*hv)) - qr*(ev(I2Pt,v)*UV-ev(Rht,v)*hv)*UV
# F_b uses the forward coefficients all the way to K_f; only then reflect.
Ff=prim(mul([zz,-fb,oo],UF))
Kf=pplus(pscale(Ff,ev(Hp,fb)),pscale(Hp,-ev(Ff,fb)))
Kdiv=cofact(cofact(rev(Kf),l),b)
N=mul([-v,oo],Mt)
DR=mul([-v,oo],Rt)
E6=det(cols(UR,N,rem([zz,*N],DR),rem(mul([-pr,qr],Kdiv),DR)))
assert Adj.degree<=2 and E6.degree<=2
# Literal weighted quintic fit, with zero weighted inputs through first middle.
D5V=ev(lift(d5),v)+tt*ev(L1t,v)
B5=pplus(pscale(pplus(Qt,pscale(Wt,-v)),jv),pscale(Rt,D5V-v*cv))
def hom(f,x,d):return sum(f[i]*x**i*d**(len(f)-1-i)for i in range(len(f)))
UZ=hom(UR,pr,qr)
Q5=pplus(pscale(B5,UZ),pscale(UR,-hom(B5,pr,qr)))
assert len(Q5)==4 and all(q.degree<=1 for q in Q5)
J=prim([zz,*UF])
Jdiv=cofact(rev(J),l)
DR2=mul([-b,oo],DR)
M2=mul(mul([-v,oo],[-b,oo]),Mt)
C0=rem(mul([-pr,qr],Jdiv),DR2)
C1=rem([zz,*C0],DR2)
WW=[UR+[zz],[zz,*UR],M2,rem([zz,*M2],DR2)]
g1,g0=(det(cols(*WW,f))for f in (C0,C1))
assert g1.degree<=3 and g0.degree<=3
q0_,q1_,q2_,q3_=Q5
dd=[qr**2*q1_+pr*qr*q2_+pr**2*q3_,qr**2*q2_+pr*qr*q3_,qr**2*q3_]
B1=hom(dd,g0,g1)
assert B1.degree<=7

def basis(r):
    if r is base:return [base.to(1)]
    lo=basis(r.low)
    return [r.to(x)*r.gen()**i for i in range(r.n)for x in lo]
def vect(e):
    if isinstance(e,PE):return [e.f]
    return sum([vect(x) for x in e.cs],[])
bb=basis(S)
cap=9
dim=len(bb)*(cap+1)
blank=base.to(0).f
def makecols(rows):
    for f,upper in rows:
        assert f.degree<=upper
        for j in range(cap-upper+1):
            for x in bb:
                v=[blank]*(len(bb)*j)
                for c in f.cs:v+=vect(c*x)
                v+=[blank]*(dim-len(v))
                yield v
def rank(rows):
    piv={}
    for v in makecols(rows):
        for i in range(dim):
            if v[i]==0:continue
            h=v[i]
            if i in piv:
                d=piv[i]
                for j in range(i+1,dim):v[j]=(v[j]-h*d[j])%baseMod
                continue
            g,iv,_=h.xgcd(baseMod)
            assert g==1 and h*iv%baseMod==1
            piv[i]=[None]*(i+1)+[v[j]*iv%baseMod for j in range(i+1,dim)]
            break
    return len(piv)
rows=[(Adj,2),(E6,2),(B1,7)]
oldrows=rows[:2]
actual_rank=rank(rows)
log('literal cubic beta1',baseMod,'dimensions',len(bb),'ranks',
    rank(oldrows),actual_rank,'of',dim,'intrinsic degrees',[g.degree for g,_ in rows])
assert actual_rank==dim
