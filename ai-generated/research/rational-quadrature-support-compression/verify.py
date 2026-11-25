#!/usr/bin/env python3
'''One canonical interval prefix. No group point or alternative drop set is searched.'''
from itertools import chain
from math import prod, isqrt
q=2147483647
assert all(q%d for d in range(2,isqrt(q)+1))
def inv(x):return pow(x%q,-1,q)
def mul(p,r):
    out=[0]*(len(p)+len(r)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(r):out[i+j]+=x*y
    return [x%q for x in out]
def nod(xs):
    p=[1]
    for z in xs:p=mul(p,[-z,1])
    return p
def moment(p,k=0,center=False):return sum(v*inv(j+k+1) for j,v in enumerate(p) if not center or (j+k)%2==0)%q
def cof(xs,i,center):return moment(nod(xs[:i]+xs[i+1:]),center=center)
labels=['m1','m2','m3','p1','p2','p3','m','p']; xs=[q-1]*3+[1]*3+[-inv(3)%q,inv(3)]
for t,(ul,vl) in enumerate([('p','p1'),('1c','p2'),('m1','1a'),('m2','2b'),('m','2a'),('5b','5c'),('6b','6c'),('7c','7a')],1):
    if t==5:xs=[(1+z)*inv(2)%q for z in xs]
    i,j=labels.index(ul),labels.index(vl); u,v=xs[i],xs[j]; d=(v-u)%q
    h=moment(nod(xs),2,t<5); C,D=cof(xs,i,t<5),cof(xs,j,t<5)
    a=h*inv(C*d**3)%q;b=-h*inv(D*d**3)%q
    new=[(u+d*z)%q for z in [a*(b+1)*inv(a-b),(a-b)*inv(a+1),(a+1)*inv(b+1)]]
    labels=[l for k,l in enumerate(labels) if k not in (i,j)]+[f'{t}{a}' for a in 'abc'];xs=[x for k,x in enumerate(xs) if k not in (i,j)]+new
assert len(xs)==len(set(xs))==16 and [moment(nod(xs),j) for j in range(3)]==[0,0,844394583]
uL,vL='7b','6a';i,j=labels.index(uL),labels.index(vL);u,v=xs[i],xs[j]; c=[cof(xs,k,False) for k in (i,j)];B=nod([u,v]); H=nod([x for k,x in enumerate(xs) if k not in (i,j)]);P=mul(B,H)
h,k=moment(P,2),moment(P,3);tau=(k*inv(h)-u-v)%q;R,S=[-h*inv(d*y)%q for d,y in zip((u-v,v-u),c)];G=mul(B,[-tau,1]);G[0]=(G[0]-R*v-S*u)%q;G[1]=(G[1]+R+S)%q
M=[moment(H,j) for j in range(6)]
a,b,c0,d,e,f=M; det=(a*(c0*e-d*d)-b*(b*e-d*c0)+c0*(b*d-c0*c0))%q
print('seed and prefix',labels, 'drop',uL,u,vL,v, 'C',c, 'h,k,tau,R,S',h,k,tau,R,S)
print('prefix moments',M,'Hankel det',det,'G',G,'nodal rows',[moment(mul(H,G),j) for j in range(4)])
assert det and G==[630645229,2011688757,1159916673,1]
assert all(sum(G[j]*M[i+j] for j in range(4))%q==0 for i in range(3))
def trim(p):
    while p and not p[-1]%q:p.pop()
    return [x%q for x in p]
def prem(p,r):
    p=trim(p[:]); r=trim(r[:]);u=inv(r[-1]);
    while len(p)>=len(r):
        i=len(p)-len(r);c=p[-1]*u%q
        for j,y in enumerate(r):p[i+j]=(p[i+j]-c*y)%q
        p=trim(p)
    return p
def modpow(p,n,r):
    a=[1]
    while n:
        if n%2:a=prem(mul(a,p),r)
        p=prem(mul(p,p),r); n//=2
    return a
def gcd(p,r):
    while r:p,r=r,prem(p,r)
    return [(x*inv(p[-1]))%q for x in p]
Xq=modpow([0,1],q,G); delta=Xq[:]; delta[1]=(delta[1]-1)%q; D=gcd(G,delta)
print('X^q mod G',Xq, 'gcd(G,X^q-X)',D)
assert D!=G
assert D==[1]
ell=(v-u)%q;s=(tau-u)*inv(ell)%q; aa=h*inv(c[0]*ell**3)%q;bb=-h*inv(c[1]*ell**3)%q
Gn=[-aa%q,(s+aa+bb)%q,(-1-s)%q,1]; assert Gn==[273581351,1877309364,165315245,1]
y=modpow([0,1],q,Gn);e=y[:];e[1]=(e[1]-1)%q;g=gcd(Gn,e); assert g==[1]
print('normalized s,a,b',s,aa,bb,'G',Gn,'Z^q mod G',y,'gcd(G,Z^q−Z)',g)
# Replay only the two published, predetermined interval group points; no phase step or alternate candidate.
def prescribed(n,l):
    ul,vl=l;i,j=labels.index(ul),labels.index(vl); u,v=xs[i],xs[j];d=(v-u)%q;h=moment(nod(xs),2)
    a=h*inv(cof(xs,i,False)*d**3)%q;b=-h*inv(cof(xs,j,False)*d**3)%q
    al=(b-a-1)%q;be=a*(2*b+1)%q; eta=4*a*b*(a-b)%q;theta=-4*a*a*b*(b+1)%q
    A=(al*al-4*be)%q;B=(2*al*eta-4*theta)%q;C=eta*eta%q
    x0=0;y0= -eta%q if n>0 else eta;X,Y=x0,y0
    for bit in bin(abs(n))[3:]:
        m=(3*X*X+2*A*X+B)*inv(2*Y)%q; xn=(m*m-A-2*X)%q;yn=(m*(X-xn)-Y)%q;X,Y=xn,yn
        if bit=='1':
            m=(Y-y0)*inv(X-x0)%q;xn=(m*m-A-X-x0)%q;yn=(m*(X-xn)-Y)%q;X,Y=xn,yn
    assert (Y*Y-X**3-A*X*X-B*X-C)%q==0
    x=(Y-al*X-eta)*inv(2*X)%q;w=(X*inv(2)-x*x-al*x-be)%q;L=(x*x+(a+b-1)*x-a)%q
    y=(w+L)*inv(2*x*(x-1))%q;sm=(x+a*inv(x)+b*inv(x-1))%q;z=(1+sm-x-y)%q
    assert (x*y*z-a)%q==0 and ((x-1)*(y-1)*(z-1)+b)%q==0
    lab=9 if n==168 else 10
    return [l for k,l in enumerate(labels) if k not in (i,j)]+[f'{lab}{l}' for l in 'abc'],[t for k,t in enumerate(xs) if k not in (i,j)]+[(u+d*w)%q for w in (x,y,z)]
labels,xs=prescribed(168,('7b','6a'));assert moment(nod(xs),2)==1698450493
labels,xs=prescribed(-42,('9b','9a'));assert moment(nod(xs),2)==240109312
print('final 18 labels',labels,'h',moment(nod(xs),2))
tail=labels[-4:];assert tail==['9c','10a','10b','10c'] and nod(xs[:-4])==H and len(set(xs))==18
D4=xs[-4:];C4=[cof(xs,j,False) for j in range(14,18)];D4p=[prod(x-y for y in D4 if y!=x)%q for x in D4]
U4=[sum(nod(D4[:i]+D4[i+1:])[j]*inv(D4p[i]*C4[i]) for i in range(4))%q for j in range(4)]
assert U4[-1] and [x*inv(U4[-1])%q for x in U4]==G
print('drops',tail,'sites',D4,'C',C4,'Dprime',D4p,'reciprocal interpolant',U4,'J',U4[-1])
print('PASS: same rigid cubic from independent three prefix moments, ancestor overtime, and final four-drop barycentric compression.')
# Vector of retained cofactors of this ONE forced nodal polynomial H*G.
# These are not scans of other candidate supports.
oldC=[cof(xs,i,False) for i in range(14)]
evalp=lambda P,x:sum(y*pow(x,i,q) for i,y in enumerate(P))%q
Cret=[moment(mul(nod(xs[:i]+xs[i+1:14]),G)) for i in range(14)]
assert all(Cret) and Cret==[(oldC[i]*evalp(G,x)-inv(U4[-1]))*inv(evalp(nod(D4),x))%q for i,x in enumerate(xs[:14])]
print('retained (H*G)/(X−a) cofactor residues',Cret,'product',prod(Cret)%q)
