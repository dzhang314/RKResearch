"""Exact five-label geometric projection, three distinct off-zero clocks."""
from itertools import combinations, permutations
from flint import nmod_poly, fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx
import sympy as S
from sympy.polys.rings import ring
v0=S.symbols('v')
V=S.Poly(4*v0**3-12*v0**2+3*v0+2,v0).monic()
assert V.is_irreducible
K=S.QQ.algebraic_field((V,v0));v=K.unit
C=lambda i,j=1:K.convert(S.Rational(i,j))
R,D,X=ring('D X',K)
s=D-1;t=s-v;r=s-2*v
P=(X-s)*(X-t)*(X-r)
I=lambda p:sum((c*C(1,j+1)*D**(i+j) for (i,j),c in p.items()),R.zero)
m=[I(P*X**j) for j in range(5)]
H=m[0]*(m[2]*m[4]-m[3]**2)-m[1]*(m[1]*m[4]-m[2]*m[3])+m[2]*(m[1]*m[3]-m[2]**2)
assert H.degree(D)==15
F,rem=divmod(H,D**6)
assert not rem
R0,Y=ring('Y',K)
F=R0.from_dict({(i,):c for (i,j),c in F.items()})
assert F.degree()==9 and [(f.degree(),e) for f,e in F.factor_list()[1]]==[(1,1),(8,1)]
print('exact diagonal projection degree 9 after D^6; factor degrees 1+8',flush=True)

# No three distinct Gaussian nodes fit either reflected third phase.
x0,y0=S.symbols('x0 y0')
LG=lambda t:70*t**4-140*t**3+90*t*t-20*t+1
dd=S.cancel((LG(y0)-LG(x0))/(y0-x0))
for y3 in (2*y0-x0,4*x0-y0):
    g=S.resultant(dd,LG(y3),y0)
    assert S.Poly(g,x0).gcd(S.Poly(LG(x0),x0)).degree()==0
print('both exact Gaussian rear triples excluded',flush=True)
def rr(a,p):
 t=S.Rational(str(a));return int(t.p)*pow(int(t.q),-1,p)%p
def ev(k,v,p):
 n=0
 for c in k.to_list():n=(n*v+rr(c,p))%p
 return n
def valid(p,v,D,Fq,P):
 X=P([0,1]);zz=Fq(0)
 if D==zz:return None
 s=D-1;t=s-v;r=s-2*v
 P3=(X-s)*(X-t)*(X-r)
 I=lambda P:sum((P[j]*D**j/Fq(j+1) for j in range(P.degree()+1)),zz)
 J=lambda pol:sum((pol[j]*X**(j+1)/Fq(j+1) for j in range(pol.degree()+1)),P([]))
 m0,m1,m2,m3,m4=[I(P3*X**j) for j in range(5)]
 de=m0*m2-m1*m1
 if de==zz:return None
 o1=(m1*m3-m2*m2)/de;p1=(m1*m2-m0*m3)/de
 Q2=X*X+p1*X+o1
 assert I(Q2*P3)==zz and I(X*Q2*P3)==zz and I(X**2*Q2*P3)==zz
 roots=Q2.roots()
 if len(roots)!=2 or any(j!=1 for _,j in roots):return None
 a1,a2=[x for x,_ in roots]
 labels=(s,t,a1,a2)
 if any(x==y for x,y in combinations(labels+(r,),2)):return None
 L=lambda x:70*x**4-140*D*x**3+90*D**2*x*x-20*D**3*x+D**4
 U=X
 H=-2+U+4*U**2-U**3
 Z=(2*X-1-X*X/Fq(2),(X-1)**2,-(X-1))
 zj=tuple(J(q) for q in Z);zjx=tuple(J(X*q) for q in Z)
 pc=0
 front=star=0
 def ordinary_gap(q,j,jx,a,b):
    return L(a)*((b-a)*q(b)+a*j(b)-jx(b))-L(b)*(a*q(a)-jx(a))
 def det(M):
    (a,b,c),(d,e,f),(g,h,j)=M
    return a*(e*j-f*h)-b*(d*j-f*g)+c*(d*h-e*g)
 def Q(k):return 4*k**3-12*k*k+3*k+2
 bad=[]
 for a,b in permutations(labels,2):
    k0,k1,k2=[j(a)-q(a) for j,q in zip(zj,Z)]
    F0=k0*H+(3*U-2)*(k1+k2*U)
    k0,k1,k2=[L(a)*((b-a)*q(b)+a*j(b)-jx(b))-L(b)*(a*q(a)-jx(a))
          for q,j,jx in zip(Z,zj,zjx)]
    F1=k0*H+(3*U-2)*(k1+k2*U)
    if max(F0.degree(),F1.degree())<3:return None
    hh=F0.gcd(F1)
    if hh.degree():
       bad.append((str(a),str(b),str(hh),str(hh.gcd(4*U**3-12*U**2+3*U+2))))
    pc+=1
    if zj[0](a)-Z[0](a)==zz:
      star+=1
      gstar=ordinary_gap(Z[0],zj[0],zjx[0],a,b)
      if gstar==zz:return None
    u=(a-1)/Fq(2)
    if Q(u)!=zz:continue
    front+=1
    if L(a)==zz:return None
    R0=Z[1]+u*Z[2]
    j0=J(R0)
    g=ordinary_gap(R0,j0,J(X*R0),a,b)
    if g==zz:return None
    lam=-ordinary_gap(Z[0],zj[0],zjx[0],a,b)/g
    T0=Z[0]+lam*R0
    Ta,Tb=T0(a),T0(b)
    if Ta==zz:return None
    JT=J(T0);JXT=J(X*T0)
    tap=(JT(b)-Tb)/Ta
    def G(S):
       h=S-J(S)
       return L(a)*(h(b)+tap*S(a))-L(b)*h(a)
    gd=G(R0)
    if gd==zz:return None
    d=G(X*R0)/gd
    R3=(X-d)*R0
    JR=J(R3)
    assert G(R3)==zz
    for c in labels:
      if c==a or c==b:continue
      F0=JT(c)-T0(c)
      F1=JXT(c)-c*T0(c)+(a*Ta-JXT(a))*L(c)/L(a)
      F2=JR(c)-R3(c)+(R3(a)-JR(a))*L(c)/L(a)
      n=det([[Ta,Tb,F0],[a*Ta,b*Tb,F1],[R3(a),R3(b),F2]])
      if n==zz:
         bad.append(("front-three",str(a),str(b),str(c),str(d)))

 return pc,bad,front,star

if __name__=='__main__':
    p,v=37,22
    assert S.isprime(p)
    vh=nmod_poly([rr(c,p) for c in reversed(V.all_coeffs())],p)
    assert vh(v)==0 and vh.derivative()(v)!=0
    dc=nmod_poly([ev(F.get((i,),K.zero),v,p) for i in range(10)],p)
    facts=((28,1),(25,6,35,16,1),(31,10,0,23,1))
    scalar,decomp=dc.factor()
    assert int(scalar)==16 and set((tuple(int(x) for x in f.coeffs()),e) for f,e in decomp)==set((c,1) for c in facts)
    moduli={1:[2,33,1],4:[2,1,27,20,7,0,0,0,1]}
    counts=[]
    for coeff in facts:
        deg=len(coeff)-1
        mod=fmpz_mod_poly_ctx(p)(moduli[deg])
        assert mod.is_irreducible()
        Fq=fq_default_ctx(modulus=mod,var='a')
        P=fq_default_poly_ctx(Fq)
        d_roots=P(list(coeff)).roots()
        assert len(d_roots)==deg and all(e==1 for _,e in d_roots)
        for D,e in d_roots:
            out=valid(p,Fq(v),D,Fq,P)
            assert out is not None
            paid,bad,front,star=out
            assert paid==12 and not bad and front==star==(3 if deg==1 else 0)
            counts.append((paid,front,star))
    assert len(counts)==9 and list(map(sum,zip(*counts)))==[108,3,3]
    print('fixed p37: 9 D roots; 108 ordered arithmetic checks; 3 possible first-zero-row3 and 3 front-star pairs all excluded',flush=True)
