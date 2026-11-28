"""Exact constant-graph seven-clock subcase with both endpoint labels singleton."""
import sympy as S
from itertools import permutations
from sympy.polys.rings import ring

QQ=S.QQ
A,W,X=S.symbols('a w x')
a2=S.Rational(3,5)
base=S.Poly(A*A-a2,A,domain=QQ)
assert base.is_irreducible
K=QQ.algebraic_field((base,A))
a=K.unit
test=lambda u:u**3-3*u*u+1
kappa=lambda u:1+2*u-u*u
hub=lambda u:-2+u+4*u*u-u**3
num=lambda u:(1+4*u-4*u*u)*hub(u)+4*u*u*(3*u-2)
assert S.expand(num(X)-hub(X)-4*X*(X-2)*test(X))==0
assert S.Poly(test(X),X).is_irreducible

# All permitted leading triples using two doubled labels. A sign of a
# labels the two noncentral doubled sites; no absolute ordering is used.
case={}
for e,f in permutations((-1,0,1),2):
    c,d=1+e*a,1+f*a
    for mode,den,cn in [('arith',2*c-d,1),('star',c+d,4)]:
        assert den
        m=K(cn)/den
        u=c*m-1
        if not m or m==K.one or not u or u==K(2) or not kappa(u): continue
        if mode=='star':
            if u==K.one: continue
            q=kappa(u)
        else:
            if 3*u==K(2):continue
            assert hub(u)
            q=num(u)/hub(u)
        if not q or q==K.one:continue
        h=m-1
        if h*h in (K.zero,a*a*m*m): continue
        rec=(mode,e,f,kappa(u)/2,q/2)
        case.setdefault(m,[]).append(rec)

# Can both forward and reversed prefixes occur with disjoint physical pairs?
# They consume their displayed pairs; reverse uses (t,g)->(-t,g) since r=1/2.
surv=[]
for m,recs in case.items():
    for k,e,f,b2,b3 in recs:
        for kr,er,fr,c2,c3 in recs:
            if {(e,b2),(f,b3)}.intersection({(-er,c2),(-fr,c3)}):continue
            surv.append((m,k,e,f,b2,b3,kr,er,fr,c2,c3))
assert set((k,e,f,kr,er,fr) for m,k,e,f,_,__,kr,er,fr,___,____ in surv)=={
  ('arith',1,-1,'arith',1,-1),('arith',-1,1,'arith',-1,1)
}
assert len(surv)==2
assert all(m==K.one/(1+3*e*a) for m,k,e,*_ in surv)
print('two-doubled openers: only opposite arithmetic survives both ends')

# Mixed opener with the third row singleton. Its phase is arithmetic,
# q=1, whence u^3-3u^2+1=0; since the third cannot be the other literal
# endpoint, the second doubled label is noncentral (e=±1).
RU,Y=ring('Y',K)
polys=[test(Y*(1+e*a)-1) for e in (-1,1)]
assert all(f.degree()==3 and len(f.factor_list()[1])==1 for f in polys)
assert polys[0].gcd(polys[1]).degree()==0
assert all(f.evaluate(Y,m) for f in polys for m in case)
# By conjugation take e=+1, construct any algebraic pair a,u by w=a+u.
F= S.Poly(test(W-A),A).rem(S.Poly(A*A-a2,A)).as_expr()
C,D=(F.subs(A,0),S.diff(F,A))
min6=S.Poly(C*C-a2*D*D,W).monic()
assert min6.degree()==6 and min6.is_irreducible
E=QQ.algebraic_field((min6,W))
w=E.unit
def atpoly(dom,f,var,z):
    return sum((dom.convert(k)*z**i[0] for i,k in S.Poly(f,var,domain=QQ).terms()),dom.zero)
cc,dd=(atpoly(E,f,W,w) for f in (C,D))
assert dd
aa=-cc/dd; u=w-aa
assert aa*aa==E.convert(a2) and not test(u)
assert u and u!=E(2) and 3*u!=E(2) and hub(u) and kappa(u)
assert num(u)==hub(u)
print('mixed opener: both ends use the same orientation, exact degree-six field')

def fourth(K,m,a,B,jj,k,q,e,third):
    """Both prefixes already fixed. Test every possible fourth clock/root."""
    r=K.one/2
    h=m-1
    assert m and h and jj and jj!=h*h and jj!=a*a*m*m
    R,T=ring('T',K)
    L4=lambda t:t**4-K.convert(S.Rational(6,7))*m*m*t*t+K.convert(S.Rational(3,35))*m**4
    H4=lambda t:(t*t-h*h)*(t*t-jj)
    A2=lambda t:(L4(t)-H4(t))/r-B*r
    UF=lambda t,g:L4(t)-g*(A2(t)+B*g)
    x1,x2,x3=K.one,m*(1+e*a),third
    gs=[r,k/2,q/2]
    assert len({x1,x2,x3})==3 and B
    assert all(not UF(x-m,g) for x,g in zip((x1,x2,x3),gs))
    T2=R.zero
    for x,g in zip((x1,x2,x3),gs):
        P=R.one
        for y in (x1,x2,x3):
            if y!=x:P*= (T-y)/R(x-y)
        T2+=g*P
    JT=R.from_dict({(i+1,):v/(i+1) for (i,),v in T2.items()})
    B0=T2.get((1,),K.zero); C0=T2.get((2,),K.zero)
    La=1+(T-1)/R(k); De=R(S.Rational(4,3))+ (T-1)*2*(k+1)/R(3*k)
    den=1-La+B0+C0*De
    nu=T2-JT
    def dg(x):
        return den.evaluate(T,x),nu.evaluate(T,x)
    root_test=lambda fc,x: (UF(x-m,T)).gcd(fc)
    # Both literal endpoints 1,2m−1 already occupied.
    poss=[]
    if q==K.one:
        # Third on one other singleton, reflected third on the other;
        # on each noncentral double one known pair already occupied.
        for ep in (-1,1):
            x=m*(1+ep*a)
            ga=-L4(ep*a*m)/(B*(k/2))
            assert ga and ga!=k/2 and not UF(x-m,ga)
            f,n=dg(x)
            if f*ga==n:poss.append(('free-copy',ep))
    else:
        # First and reverse triples jointly consume both copies at each
        # noncentral double. The two other singleton choices both have g=1/2.
        assert k!=q and not UF(a*m,k/2) and not UF(a*m,q/2)
        D0=(T-m)**2-jj
        G0=D0.gcd(nu-r*den)
        if G0.degree()>0:poss.append(('singletons',G0.degree()))
    f,n=dg(m)
    G0=root_test(f*T-n,m)
    if G0.degree()>0:poss.append(('center',G0.degree()))
    print('exact fourth possibilities',poss)
    assert not poss

# Opposite arithmetic double–double case.
m=K.one/(1+3*a)
u0=m*(1+a)-1;k=kappa(u0);q=num(u0)/hub(u0)
assert k and q and k!=q and q!=K.one
r=K.one/2; d=a*m; h=m-1
L=lambda t:t**4-K.convert(S.Rational(6,7))*m*m*t*t+K.convert(S.Rational(3,35))*m**4
assert L(d) and d*d!=h*h
B=-L(d)/(k*q/4)
a_at_d=-B*(k+q)/2
jj=d*d-(L(d)-r*(a_at_d+B*r))/(d*d-h*h)
fourth(K,m,a,B,jj,k,q,1,m*(1-a))

# Third singleton case, with field E and coordinates recovered above.
m=(u+1)/(1+aa);k=kappa(u);q=E.one
r=E.one/2; d=aa*m; h=m-1
t3=1+2*u-m
jj=t3*t3
L=lambda t:t**4-E.convert(S.Rational(6,7))*m*m*t*t+E.convert(S.Rational(3,35))*m**4
Hd=(d*d-h*h)*(d*d-jj)
g=k/2
assert g and g!=r
B=(L(d)-g*(L(d)-Hd)/r)/(g*(g-r))
fourth(E,m,aa,B,jj,k,q,1,1+2*u)
print('verified no constant-singleton-residual seven-clock tableau with both endpoints singleton')
