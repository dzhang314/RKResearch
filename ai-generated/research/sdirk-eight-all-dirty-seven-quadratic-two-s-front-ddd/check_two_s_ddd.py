"""One singleton endpoint: two forward singleton labels and rear D,D,D."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from itertools import product,combinations
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,v=field('H,v',S.QQ)
C=MC.get(('H','v'),'lex')
m=(H+2)/2
def L(y,j=4):
    t=y-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def poly(a):
    if not a:return C.constant(0)
    l=lcm(*(int(S.Rational(c).q) for c in a.values()))
    return C.from_dict({tuple(map(int,i)):int(c*l) for i,c in a.items()})
def num(x):return poly(x.numer)
def strip(p,gs):
    for q in gs:
        while p and (g:=p.gcd(q)).total_degree()>0:
            p,r=divmod(p,g);assert not r
    return p
def ip(y,pts):
    a=F.zero
    for x,t in pts:
        for z,_ in pts:
            if z!=x:t*= (y-z)/(x-z)
        a+=t
    return a
def tail(rm):
    ds=[H,H-v,H-2*v if rm=='A' else H+v-2]
    (r2,r3),rg=op(v,rm)
    rr=[F.one/2,r2,r3]
    T,y=ring('y',F.to_domain())
    t=y-T(H/2)
    L4=t**4-T(6*m*m/7)*t*t+T(3*m**4/35)
    L3=t**3-T(3*m*m/5)*t
    aa=L(H,3)/L(H)
    bb=(L(ds[1],3)/L(ds[1])-aa)/(ds[1]-H)
    M=(L3-(T(aa)+T(bb)*(y-T(H)))*L4).exquo((y-T(H))*(y-T(ds[1])))
    assert M.degree()==3 and bb
    E=M.evaluate(y,ds[2]);M0=M.get((0,),F.zero)
    assert M0 and E
    return ds,rr,rg,M,y,bb,M0,E
def chart(rm,fo,i):
    ds,rr,rg,M,y,bb,M0,E=tail(rm)
    d=ds[i]
    if fo=='A2':
        u=d;s=2*d;(fd,fs),fg=op(u,'A')
    elif fo=='A3':
        u=d/2;s=u;(fs,fd),fg=op(u,'A')
    else:
        u=d;s=2-d;(fd,fs),fg=op(u,'S')
    gs=list(rg)+list(fg)+[m,H,u-2]+[a-b for a,b in combinations([F.zero]+ds+[s],2)]
    gs+=[2*z-H for z in ds]+[x+z-H for x,z in combinations(ds,2)]
    gs+=[L(z) for z in ds]
    if fo=='S':gs+=[s-2]
    if not all(gs):return None
    base=[num(z) for z in gs]
    assert all(poly(z.denom).total_degree()==0 for z in gs)
    gs+=[bb,M0]
    assert all(strip(poly(z.denom),base).total_degree()==0 for z in gs)
    A=ds[2]*M.evaluate(y,s)+2*M0*(s-ds[2])*fs
    be=-L(d)/(fd*rr[i])
    U=[(x,L(x)/r) for x,r in zip(ds,rr)]
    V=[(x,-be*r) for x,r in zip(ds,rr)]
    a0=ip(F.zero,U)/2+be/4;b0=ip(F.zero,V)/2-L(F.zero)
    a1=fs*ip(s,U)+be*fs*fs;b1=fs*ip(s,V)-L(s)
    B=a0*b1-a1*b0
    gs+=[M.evaluate(y,s)]
    assert all(gs)
    assert all(strip(poly(z.denom),base).total_degree()==0 for z in gs)
    gi=[num(z) for z in gs]+[poly(z.denom) for z in gs]
    assert all(strip(poly(z.denom),gi).total_degree()==0 for z in [E,A,B])
    e,a,b=[strip(num(z),gi) for z in [E,A,B]]
    assert e and a and b
    return (e,a,b),gi,(ds,rr,M,y,bb,M0,E,d,s,fd,fs,u,be,a0,b0,a1,b1,gs)
EXPECTED={
 ('A','A2'):[(54,130),(62,173),(59,160)],('A','A3'):[(25,127),(44,168),(38,165)],
 ('A','S'):[(39,100),(44,128),(42,126)],('S','A2'):[(68,66),(82,147),(78,147)],
 ('S','A3'):[(30,98),(55,147),(51,147)],('S','S'):[(46,48),(48,84),(55,84)]
}
def project():
 for rm,fo,i in product('AS',('A2','A3','S'),range(3)):
    seq=chart(rm,fo,i)
    if seq is None:
        print(rm,fo,i+1,'literal collapse',flush=True);continue
    rows,gg,_=seq
    E,A,B=rows
    hs=[z for z in gg if not z.degrees()[1]]
    pp=[strip(E.resultant(z,'v'),hs) for z in [A,B]]
    assert all(pp)
    g=pp[0].gcd(pp[1])
    assert g and g.total_degree()==0
    assert tuple(w.total_degree() for w in pp)==EXPECTED[rm,fo][i]
    fx=g.factor()[1]
    print(rm,fo,i+1,'rows',[z.degrees() for z in rows],'degrees',
      [w.total_degree() for w in pp],'H factors',[(w.total_degree(),e) for w,e in fx],flush=True)
    yield rm,fo,i,fx,seq
if __name__=='__main__':
    seen={(r,f,i) for r,f,i,_,_ in project()}
    assert seen==set(product('AS',('A2','A3','S'),range(3)))
    print('all eighteen literal 2S/1D versus D,D,D phase charts excluded')
