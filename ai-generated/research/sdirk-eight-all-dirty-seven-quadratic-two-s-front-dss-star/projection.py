"""Two S at singleton front, rear D,S,S star: exact regular and half-amplitude gates."""
import sympy as S
from sympy.polys.fields import field
from sympy.polys.rings import ring
from flint import fmpz_mpoly_ctx as MC
from math import lcm
from itertools import combinations
def K(u):return 1+2*u-u*u
def DD(u):return -2+u+4*u*u-u**3
def NN(u):return (1+4*u-4*u*u)*DD(u)+4*u*u*(3*u-2)
def op(u,ph):
    if ph=='S':return (K(u)/2,K(u)/2),[u,u-1,u-2,K(u)]
    return (K(u)/2,NN(u)/(2*DD(u))),[u,DD(u),NN(u),K(u),3*u-2]
F,H,d=field('H,d',S.QQ)
C=MC.get(('H','d'),'lex')
m=(H+2)/2;c=H-1
def L(y,j=4):
    t=y-H/2
    return t**3-3*m*m*t/5 if j==3 else t**4-6*m*m*t*t/7+3*m**4/35
def poly(p):
    if not p:return C.constant(0)
    z=lcm(*(int(S.Rational(a).q) for a in p.values()))
    return C.from_dict({tuple(map(int,ix)):int(z*a) for ix,a in p.items()})
def num(f):return poly(f.numer)
def strip(p,gg):
    for x in gg:
        while p and (z:=p.gcd(x)).total_degree()>0:
            p,r=divmod(p,z);assert not r
    return p
def phase(d,fo):
    if fo=='A2':
        u=d;s=2*d;(fd,fs),gg=op(u,'A')
    elif fo=='A3':
        u=d/2;s=u;(fs,fd),gg=op(u,'A')
    else:
        u=d;s=2-d;(fd,fs),gg=op(u,'S')
    gg+=[u-2]
    return s,fd,fs,gg
def regular(fo,reuse):
    D=H if reuse else d
    s,fd,fs,gg=phase(D,fo)
    t=2*fs-1
    gg += [m,H,H-2,D,s,s-H,s-D,s-2*c,t,2*D-H,L(H),L(D)]
    if not reuse:gg+=[D-H]
    assert all(gg)
    base=[num(g) for g in gg if poly(g.denom).total_degree()==0]
    assert all(strip(poly(g.denom),base).total_degree()==0 for g in gg)
    base += [num(g) for g in gg if poly(g.denom).total_degree()>0]
    W0=s*(s-2*c)/t
    U,y=ring('y',F.to_domain())
    z=y-U(H/2)
    W=y*y-U(2*c)*y+U(W0)
    LP3=z**3-U(3*m*m/5)*z
    LP4=z**4-U(6*m*m/7)*z*z+U(3*m**4/35)
    l4=LP4%W;l3=LP3%W
    l0,l1=[l4.get((i,),F.zero) for i in range(2)]
    j0,j1=[l3.get((i,),F.zero) for i in range(2)]
    nn=s*l1-t*l0
    det=l0*l0+2*c*l0*l1+W0*l1*l1
    gg += [W0,l0,det]
    bef=[num(g) for g in gg]
    assert all(strip(poly(g.denom),base).total_degree()==0 for g in gg)
    if not reuse:
        b=(L(D,3)/L(D)-L(H,3)/L(H))/(D-H)
        Q=LP3-(U(L(H,3)/L(H))+U(b)*(y-U(H)))*LP4
        M=Q.exquo((y-U(H))*(y-U(D)))
        assert M.degree()==3
        rem=M%W
        aa,bb=[rem.get((i,),F.zero) for i in range(2)]
        gg += [b,M.get((0,),F.zero),M.evaluate(y,s)]
        assert all(strip(poly(g.denom),base).total_degree()==0 for g in gg)
        data=[aa,bb,nn]
    else:
        a=(j0*(l0+2*c*l1)+W0*l1*j1)/det
        b=(l0*j1-l1*j0)/det
        Q=LP3-(U(a)+U(b)*y)*LP4
        M=Q.exquo(W)
        assert M.degree()==3
        gg += [b,M.get((0,),F.zero),M.evaluate(y,s)]
        assert all(strip(poly(g.denom),bef).total_degree()==0 for g in gg)
        data=[M.evaluate(y,H),nn]
    assert all(gg) and all(data)
    g=[num(f) for f in gg]+[poly(f.denom) for f in gg]
    assert all(strip(poly(z.denom),g).total_degree()==0 for z in data)
    rows=[strip(num(z),g) for z in data]
    return g,rows,(H,D,s,fd,fs,gg,M,W,LP4)
def project():
 for fo in ('A2','A3','S'):
    g,rows,dta=regular(fo,True)
    gd=strip(rows[0].gcd(rows[1]),g)
    assert gd and gd.total_degree()==0
    assert [z.degrees() for z in rows]=={'A2':[(21,0),(12,0)],
       'A3':[(11,0),(5,0)],'S':[(10,0),(5,0)]}[fo]
    print(fo,'reused regular' , [z.degrees() for z in rows],'H gcd factors',
                 [(q.total_degree(),e) for q,e in gd.factor()[1]],flush=True)
    yield True,fo,gd.factor()[1],g,rows,dta
    g,rows,dta=regular(fo,False)
    hs=[z for z in g if z.degrees()[1]==0]
    out=[strip(a.resultant(b,'d'),hs) for a,b in combinations(rows,2)]
    assert all(out)
    gd=strip(out[0].gcd(out[1]).gcd(out[2]),hs)
    assert gd
    assert [z.total_degree() for z in out]=={'A2':[82,80,84],
       'A3':[33,23,22],'S':[32,23,22]}[fo]
    assert sorted((z.total_degree(),e) for z,e in gd.factor()[1])==(
       [(1,1),(3,1)] if fo=='A2' else [])
    print(fo,'new regular' , [z.degrees() for z in rows],'projections',
        [z.total_degree() for z in out],'H gcd factors',[(q.total_degree(),e) for q,e in gd.factor()[1]],flush=True)
    yield False,fo,gd.factor()[1],g,rows,dta
if __name__=='__main__':list(project())
