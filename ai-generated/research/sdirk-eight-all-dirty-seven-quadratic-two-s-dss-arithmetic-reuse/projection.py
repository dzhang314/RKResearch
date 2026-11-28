"""Two S front, rear D,S,S arithmetic, reused H. Test regular and rank-zero."""
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from itertools import combinations
from math import lcm
import sympy as S
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,v=field('H,v',S.QQ)
C=MC.get(('H','v'),'lex')
m=(H+2)/2;p=H-v;q=H-2*v
D=DD(v);k=K(v);hh=D-v*(v-2)*(3*v-2)
assert NN(v)==k*hh
def lp(x,j=4):
    t=x-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def phase(fo):
    if fo=='A2':
        u=H;s=2*H;(fd,fs),gg=op(u,'A')
    elif fo=='A3':
        u=H/2;s=u;(fs,fd),gg=op(u,'A')
    else:
        u=H;s=2-H;(fd,fs),gg=op(u,'S')
    return s,fd,fs,gg+[u-2]
def poly(q):
    if not q:return C.constant(0)
    d=lcm(*(int(S.Rational(c).q) for c in q.values()))
    return C.from_dict({tuple(map(int,ix)):int(d*c) for ix,c in q.items()})
def num(q):return poly(q.numer)
def strip(p,gs):
    for x in gs:
        while p and (z:=p.gcd(x)).total_degree()>0:
            p,r=divmod(p,z);assert not r
    return p
def prepare(fo):
    s,fd,fs,gg=phase(fo)
    gg += [m,H,v,D,k,hh,3*v-2,lp(H)]
    gg += [a-b for a,b in combinations([F.zero,s,p,q,H],2)]
    assert all(gg)
    gs0=[num(a) for a in gg]
    assert all(poly(a.denom).total_degree()==0 for a in gg)
    a=(fs-F.one/2)/s
    U=D*(2*H-3*v-s)-(v-2)*(3*v-2)*p*(p-s)
    V=D*a-(v-2)*(3*v-2)*(F.one/2+a*p)
    R0=p+q-s+2*a*p*q
    assert D*q*(q-s)-hh*p*(p-s)==-v*U
    assert D*(F.one/2+a*q)-hh*(F.one/2+a*p)==-v*V
    assert all(strip(poly(w.denom),gs0).total_degree()==0 for w in [U,V,R0])
    return s,fd,fs,gg,a,U,V,R0
def shape(fo):
    s,fd,fs,gg,a,U,V,R0=prepare(fo)
    guards=[num(g) for g in gg]
    ee,ff,gg0=[strip(num(z),guards) for z in (U,V,R0)]
    assert ee and ff and gg0
    return (ee,ff,gg0),guards
def project_zero():
 for fo in ('A2','A3','S'):
    rows,gs=shape(fo)
    hh0=[g for g in gs if g.degrees()[1]==0]
    pp=[strip(x.resultant(y,'v'),hh0) for x,y in combinations(rows,2)]
    assert all(pp)
    gcd=pp[0].gcd(pp[1]).gcd(pp[2])
    assert gcd
    h={'A2':15,'A3':5,'S':9}[fo]
    assert [(z.total_degree(),e) for z,e in gcd.factor()[1]]==[(h,1)]
    assert [x.total_degree() for x in pp]=={'A2':[15,15,21],'A3':[5,5,5],'S':[9,10,9]}[fo]
    print(fo,'rank zero projected degrees' ,[x.total_degree() for x in pp],
       'H factors',[(z.total_degree(),e) for z,e in gcd.factor()[1]],flush=True)
    yield fo,gcd.factor()[1],rows,gs
def core(fo):
    s,fd,fs,guards,a,U,V,R0=prepare(fo)
    base=[num(g) for g in guards]
    b=-V/U
    assert b
    guards += [U,V]
    gs=[num(g) for g in guards]
    assert all(strip(poly(w.denom),base).total_degree()==0 for w in guards)
    T,y=ring('y',F.to_domain())
    RR=T(F.one/2)+T(a)*y+T(b)*y*(y-T(s))
    t=y-T(H/2)
    L3=t**3-T(3*m*m/5)*t
    L4=t**4-T(6*m*m/7)*t*t+T(3*m**4/35)
    W=RR.exquo(T(b))
    w0,w1=[W.get((i,),F.zero) for i in range(2)]
    sr=y*(y-T(s))*(y-T(p))*(y-T(q))
    l=L4%W;j=L3%W;z=sr%W
    l0,l1=[l.get((i,),F.zero) for i in range(2)]
    j0,j1=[j.get((i,),F.zero) for i in range(2)]
    z0,z1=[z.get((i,),F.zero) for i in range(2)]
    det=l0*l0-w1*l0*l1+w0*l1*l1
    aa=(j0*(l0-w1*l1)+w0*l1*j1)/det
    bb=(l0*j1-j0*l1)/det
    Proj=(L3-(T(aa)+T(bb)*y)*L4).exquo(W)
    e=Proj.evaluate(y,H)
    n=l0*z1-l1*z0
    # A genuine front/terminal overlap fixes beta; no fit pivot is divided by.
    Rp=RR.evaluate(y,p);Rq=RR.evaluate(y,q)
    mu=2*Rp
    rel=-2*lp(H)/fd # beta = B lambda
    RH=RR.evaluate(y,H)
    L0=fd*(fd-RH)
    paid=[]
    for zz,ll in [(z0,l0),(z1,l1)]:
        Cfit=(T(zz)*L4-T(ll)*sr).div(RR)[0]
        paid.append(mu*(zz*lp(H)-fd*Cfit.evaluate(y,H))-zz*rel*k*L0)
    support=base+[num(U),num(V)]
    assert strip(poly(det.denom),support).total_degree()==0
    support+=[num(det)]
    guards += [det,bb,Rp,Rq,L0,Proj.get((0,),F.zero),mu-2*k*fd]
    assert all(strip(poly(w.denom),support).total_degree()==0 for w in guards)
    assert all(guards)
    gg=[num(g) for g in guards]+[poly(g.denom) for g in guards]
    assert all(strip(poly(w.denom),gg).total_degree()==0 for w in [e,n]+paid)
    rows=[strip(num(z),gg) for z in [e,n]+paid]
    return rows,gg
def project_regular():
 for fo in ('A2','A3','S'):
    rows,gs=core(fo)
    hgs=[g for g in gs if g.degrees()[1]==0]
    print(fo,'regular bivariate degrees',[t.degrees() for t in rows],flush=True)
    e,n,*ps=rows
    pp=[]
    for zz in [n]+ps:
      pr=e.resultant(zz,'v')
      if pr:pp.append(strip(pr,hgs))
    assert pp
    gg=pp[0]
    for a in pp[1:]:gg=gg.gcd(a)
    assert gg
    assert sorted((z.total_degree(),n) for z,n in gg.factor()[1])=={
       'A2':[(15,3)],'A3':[(3,2),(5,2)],'S':[(9,3)]}[fo]
    assert [x.total_degree() for x in pp]=={'A2':[242,361,406],'A3':[112,192,211],'S':[142,226,243]}[fo]
    print(fo,'regular projected degrees' ,[x.total_degree() for x in pp],
      'H factors',[(z.total_degree(),n) for z,n in gg.factor()[1]],flush=True)
    yield fo,gg.factor()[1],rows,gs
if __name__=='__main__':
    list(project_zero())
    list(project_regular())
