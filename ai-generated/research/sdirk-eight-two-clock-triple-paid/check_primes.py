#!/usr/bin/env python3
from gauss import ctx,phase
from itertools import permutations

def chrono(F,a,b):
    one=F.one()
    k=a+b-2;q=(a+b)*k-a*b+9*one/7
    r=lambda x:x*x+k*x+q
    j=lambda x:x*x*x/3+k*x*x/2+q*x
    G=j(a)/r(a)
    if G==0 or r(G)==0 or r(1-G)==0:return
    latest=[z for z in (a,b) if G*r(z)==j(one)-j(z)]
    if not latest:return
    def gap(R,k):
        d=R+G*G;n=2*R-G*(2*G+k)
        if d==0:
            assert n!=0,('free second gap',a,b,G,R,k)
            return
        return n/d
    u=gap(r(G),k);v=gap(r(1-G),-2-k)
    if u is None or v is None:return
    def options(uu,R,zero,clock):
        ans=[]
        for kind,w,Q,T in phase(uu):
            x=clock(G*(1+w))
            if Q==0 and x in zero and kind=='A':ans.append((kind+'0',x,Q,T))
            if Q!=0 and R*Q==r(x):ans.append((kind,x,Q,T))
        return ans
    f=options(u,r(G),[a],lambda x:x)
    rr=options(v,r(1-G),latest,lambda x:1-x)
    if v==2:rr.append(('silent',None,F.zero(),F.zero()))
    if f and rr:return G,u,v,f,rr

primes=(13,19,107,139,227,233,241,509,739,10067,234847,1352963,1207117,127835437,3716728837183)
out=[]
for p in primes:
    F,_,d,rs=ctx(p)
    surviving=[]
    for a,b in permutations(rs,2):
        c=chrono(F,a,b)
        if c:
            out.append((p,a,b,*c))
            surviving.append((a,b,*c))
    print(p,'splitting degree',d,'both-end survivors',len(surviving),flush=True)


def fourth(F,a,b,G,u,data,rev=False):
    from flint import fq_default_poly_ctx
    R=fq_default_poly_ctx(F);X=R.gen();p=F.characteristic()
    z=lambda x:(1-x) if rev else x
    k=a+b-2;q=(a+b)*k-a*b+9*F.one()/7
    rr=lambda x:x*x+k*x+q
    P=(G*G/2)*rr(z(X))/rr(z(G))
    rows=[(G,G*G/2),(G*(1+u),(1+2*u-u*u)*G*G/2),(z(data[1]),data[2]*G*G/2)]
    Q=R.zero()
    for i,(x,y) in enumerate(rows):
        term=R([y])
        for j,(t,_) in enumerate(rows):
            if i!=j:term=term*(X-t)/(x-t)
        Q+=term
    J=R([F.zero()]+[Q[j]/(j+1) for j in range(3)])
    a0=J(rows[0][0])/rows[0][1];b0=J(rows[1][0])/rows[1][1]
    B=(b0-a0)/(rows[1][0]-rows[0][0]);A=a0-B*rows[0][0]
    D=J-G*Q
    Z=D+P*(G-A-B*X)
    assert all(Z(x)==0 for x,g in rows if g!=0)
    f,rs=Z.factor()
    o=[(z(x),m) for x,m in Z.roots() if all(x!=q for q,g in rows) and rr(z(x))!=0]
    zz=[c for c in (a,b) if D(z(c))==0 and all(z(c)!=x or g!=0 for x,g in rows)]
    return Z,rs,o,zz

expected={
    139:(137,3,32,82,'A0',8,132),
    509:(302,208,50,86,'A',None,None),
    739:(412,328,707,224,'A0',670,70),
    1352963:(42484,1310480,603822,1219811,'A0',1095488,257476),
    3716728837183:(3244963624905,471765212279,1085191571854,3576205281375,'A',None,None),
}
assert len(out)==len(expected) and {x[0] for x in out}==set(expected)
for p,a,b,G,u,v,f,r in out:
    F,_,_,_=ctx(p)
    ra,rb,rg,ru,kind,x,y=expected[p]
    assert tuple(map(int,(a,b,G,u)))==(ra,rb,rg,ru)
    assert v==u and len(f)==len(r)==1 and f[0][0]==r[0][0]==kind
    assert a+b==1
    fr,ft,fo,fz=fourth(F,a,b,G,u,f[0]);br,bt,bo,bz=fourth(F,a,b,G,v,r[0],True)
    assert fr.degree()==br.degree()==3
    assert all(f.degree()==e==1 for f,e in (*ft,*bt))
    if kind=='A0':
        assert f[0][1]==a and r[0][1]==b
        assert fo==[(F(x),1)] and bo==[(F(y),1)] and fz==bz==[]
    else:
        assert fo==bo==[] and fz==[a] and bz==[b]
    N=-a*a*(7*a-2)*(7*a-6)/84
    assert N!=0
    print('fourth',p,fr,'offzero',fo,bo,'zero',fz,bz,'singleton obstruction',N)
