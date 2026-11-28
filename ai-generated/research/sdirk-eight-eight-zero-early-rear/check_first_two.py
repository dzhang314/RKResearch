
"""Fixed exact certificates: first/second early mate, all finite gaps and terminal star."""
import sympy as S
from sympy.polys.rings import ring
from flint import nmod_poly
from sys import argv
kind=argv[1]
assert kind in ('ghost','arith','star')
vdegree=3 if kind=='ghost' else 6
u_,b_,w_,v_,z_=S.symbols('u b w v z')
Q=S.Poly(4*u_**3-12*u_**2+3*u_+2,u_).monic()
Hv=v_**3-4*v_**2-v_+2 if kind=='ghost' else 8*v_**6-44*v_**5+22*v_**4+97*v_**3-55*v_**2-13*v_+6
H=S.Poly(Hv,v_).monic()
assert Q.is_irreducible and (kind=='star' or H.is_irreducible)
K=S.QQ.algebraic_field((Q,u_));u=K.unit
R,b=ring('b',K)
Bb=b*b-(2*u+4)*b+1+2*u
F=S.Poly(S.resultant(Q,(b_**2-(2*u_+4)*b_+1+2*u_).subs(b_,w_-u_),u_),w_).monic()
assert F.degree()==6 and F.is_irreducible
def recover(K,R,t,mod,f,aa,bb,n,m):
    def vec(p):
        return S.Matrix([S.Rational(str((p.get((j,),K.zero).to_list()[::-1]+[0]*n)[i]))
                         for j in range(m) for i in range(n)])
    C=S.Matrix.hstack(*(vec(t**i%mod) for i in range(n*m)))
    I=C.inv()
    a=I*vec(aa);b=I*vec(bb)
    def ev0(z):
        return sum((R(K.convert(x))*t**i%mod for i,x in enumerate(z)),R.zero)%mod
    assert ev0(a)==aa and ev0(b)==bb and not ev0(f.all_coeffs()[::-1])
    return a,b
u_w,b_w=recover(K,R,R(u)+b,Bb,F,R(u),b,3,2)
E=S.QQ.algebraic_field((F,w_));w=E.unit
if kind=='star':
    G=F
else:
    G=S.Poly(S.resultant(H,F.as_expr().subs(w_,z_-2*v_),v_),z_).monic()
    assert G.degree()==6*vdegree and G.is_irreducible
    S0,v=ring('v',E)
    VH=sum((E.convert(x)*v**j for j,x in enumerate(H.all_coeffs()[::-1])),S0.zero)
    w_z,v_z=recover(E,S0,S0(w)+2*v,VH,G,S0(w),v,6,vdegree)
def rr(a,p):
    s=S.Rational(str(a));return int(s.p)*pow(int(s.q),-1,p)%p
def ev(coords,y,p):
    return sum(rr(co,p)*pow(y,i,p) for i,co in enumerate(coords))%p

if kind=='star':
    w_z,v_z=None,None

def solve(rows, col, p):
    m=[[(int(r)%p) for r in row]+[int(rhs)%p] for row,rhs in zip(rows,col)]
    for j in range(len(col)):
        k=next((k for k in range(j,len(col)) if m[k][j]),None)
        if k is None:return
        m[j],m[k]=m[k],m[j]
        y=pow(m[j][j],-1,p)
        m[j]=[(q*y)%p for q in m[j]]
        for k in range(len(col)):
            if k==j: continue
            y=m[k][j]
            m[k]=[(l-y*r)%p for l,r in zip(m[k],m[j])]
    return [row[-1] for row in m]

def test(p,u,b,v,slot,side):
    a=(1+2*u)%p
    q=(a,b)[side]
    D=(1+q+slot*v)%p
    s=(D-1)%p; t=(s-v)%p; r=(t-v)%p
    rear=[s,t,r]; assert rear[slot]==q
    keep=[x for i,x in enumerate(rear) if i!=slot]
    if not D or not a or not b or a==b:return
    if kind!='star' and (not v or len({a,b,*keep})!=4):return
    k=(1+2*v-v*v)%p
    ff=(v**3-4*v*v-v+2)%p; gg=(4*v**3-12*v*v+3*v+2)%p
    if kind!='star' and (not k or (kind=='arith' and (not ff or not gg))):return
    X=nmod_poly([0,1],p)
    L3=20*X**3-30*D*X**2+12*D**2*X-D**3
    L4=70*X**4-140*D*X**3+90*D**2*X**2-20*D**3*X+D**4
    L5=252*X**5-630*D*X**4+560*D**2*X**3-210*D**3*X**2+30*D**4*X-D**5
    def J(f):return nmod_poly([0]+[int(f[i])*pow(i+1,-1,p)%p for i in range(f.degree()+1)],p)
    def I(f):return sum(int(f[i])*pow(D,i,p)*pow(i+1,-1,p) for i in range(f.degree()+1))%p
    def ec(f,x):return int(f(x))
    Z2=(X-a)*(X-b);Z3=X*Z2;J2=J(Z2);J3=J(Z3)
    initials=(a,b)
    coeff=solve([[ec(JP,x) for JP in (J2,J3)] for x in initials],
        [-ec(L4,x) for x in initials],p)
    if coeff is None:return
    al,be=coeff
    C3,rr=divmod(al*(Z2-J2)+be*(Z3-J3)-L4,Z2)
    assert not rr
    if C3.degree()!=2:return
    tc=C3.roots()
    if len(tc)!=2 or any(e!=1 for _,e in tc):return
    res=[]
    for c,_ in tc:
        c=int(c)
        if c in (a,b) or (kind!='star' and c in keep):return
        sig=Z2*(X-c);Jsig=J(sig)
        coeff=solve([[ec(L,x) for L in (L3,L4,L5)] for x in (a,b,c)],
             [-(x-q)*ec(Jsig,x) for x in (a,b,c)],p)
        if coeff is None:return
        U=coeff[0]*L3+coeff[1]*L4+coeff[2]*L5
        C4,rr=divmod((X-q)*(sig-Jsig)-U,sig)
        assert not rr
        if kind=='star':
            P5,R=sig,sig*(X-(D-2))**2
        else:
            P5=sig*(X-keep[0])*(X-keep[1])
            if slot==2: R=k*(P5//(X-t))-P5//(X-s)
            elif kind=='ghost': R=P5//(X-r)
            elif slot==0: R=gg*(P5//(X-r))+ff*(P5//(X-t))
            else: R=k*gg*(P5//(X-r))+ff*(P5//(X-s))
        coeff=solve([[I(M),I(X*M)] for M in (P5,R)],
                     [-I(X**2*M) for M in (P5,R)],p)
        if coeff is None:return
        P2=X**2+coeff[1]*X+coeff[0]
        if P2.gcd(C4).degree():return
        res.append((c,list(map(int,P2.coeffs())),list(map(int,C4.coeffs()))))
    return res

def on_fiber(p,z0,slot,side):
    gp=nmod_poly([rr(c,p) for c in reversed(G.all_coeffs())],p)
    if gp(z0)!=0 or gp.derivative()(z0)==0:return
    try:
        ww,vv=(z0,0) if kind=='star' else [ev(x,z0,p) for x in (w_z,v_z)]
        uu,bb=[ev(x,ww,p) for x in (u_w,b_w)]
    except ValueError:return
    assert (uu+bb+2*vv-z0)%p==0
    ctrl=test(p,uu,bb,vv,slot,side)
    if ctrl:return (p,z0,uu,bb,vv,ctrl)

if __name__=='__main__':
    rows={
        'ghost': ((0,0,79,31),(0,1,17,1),(1,0,59,1),(1,1,59,1),(2,0,83,32),(2,1,59,1)),
        'arith': ((0,0,103,35),(0,1,113,60),(1,0,103,65),(1,1,103,35),(2,0,103,35),(2,1,59,28)),
        'star': ((0,0,43,2),(0,1,17,11)),
    }
    for slot,side,p,z in rows[kind]:
        assert S.isprime(p) and p>7
        ans=on_fiber(p,z,slot,side)
        assert ans is not None
        print(kind,slot,side,ans)
