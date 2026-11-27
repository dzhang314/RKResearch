import sympy as S
from functools import reduce
from itertools import combinations,permutations
Y,A,T,g,u,c,d,e=S.symbols('Y A T g u c d e')
P=(A**3-7*A**2+16*A-12)*T**3+(-9*A**3+54*A**2-102*A+63)*T**2+(18*A**3-90*A**2+138*A-66)*T+(-6*A**3+24*A**2-30*A+12)
Q=S.expand(sum(k*(g+u)**i*c**j*g**(6-i-j)for (i,j),k in S.Poly(P,A,T).terms()))
def scan(p,v,w):
    S0=(g,u,c,d,e)
    F=lambda expr:S.Poly(expr,*S0,modulus=p)
    def mom(roots,j=0):
        q=S.Poly(1,Y,*S0,modulus=p)
        for r in roots:q*=S.Poly(Y-r,Y,*S0,modulus=p)
        return F(sum(co*pow(ii[0]+j+1,-1,p)*S.prod(z**h for z,h in zip(S0,ii[1:]))
                for ii,co in q.terms())).as_expr()
    def M(ro):return [mom(ro,i)for i in range(3)]
    def unit(q,*vars):
        gb=S.groebner(q,*vars,modulus=p,order='grevlex')
        return len(gb.polys)==1 and gb.polys[0].as_expr()==1
    def polyg(q):
        return S.Poly(F(q).as_expr(),g,modulus=p)
    def gc(q):
        return reduce(lambda a,b:a.gcd(b),[polyg(z)for z in q]).degree()==0
    def aff(M):
        return [M[i]*M[j+1]-M[j]*M[i+1]for i,j in combinations(range(3),2)]
    def det(A):
        return int(S.Matrix(A).det())%p
    def val(F):
        r=F.as_expr() if isinstance(F,S.Poly) else F
        r=S.sympify(r)
        assert not r.free_symbols
        return int(r)%p
    def h3(ro):
        H=[mom(ro,j)for j in range(5)]
        return det([[val(H[i+j])for j in range(3)]for i in range(3)])
    fv=[1-g*v,1-g*w];av=[g+i*u for i in range(3)];R3=[*fv,g];H5=[*fv,*av]
    ans={}
    ans['no-pins-no-repeat-finite']=unit(M([*H5,c])+[Q],g,u,c)
    R3M=[mom(R3,j)for j in range(4)]
    ans['no-pins-infinity-u-c']=gc(R3M[:3])
    ans['no-pins-infinity-u-only']=gc(aff(R3M))
    for k in [1,2]:
        ans[('no-pins-infinity-c-only',k)]=gc(M([*R3,(k+1)*g,(2*k+1)*g]))
    for j in range(3):
        Qj=F(Q.subs(c,av[j])).as_expr()
        ans[('no-pins-repeat-finite',j)]=unit(M([*H5,d])+[Qj],g,u,d)
        ans[('no-pins-repeat-infinity-d',j)]=unit(M(H5)+[Qj],g,u)
    for pin,po in enumerate([v,w]):
        for i in range(3):
            if not i:
                assert (1+po)%p
                sub={g:pow(1+po,-1,p)}
                tt=u
            else:
                sub={u:pow(i,-1,p)*(1-(1+po)*g)}
                tt=g
            R4=[F(z.subs(sub)).as_expr() for z in [*fv,*(z for j,z in enumerate(av)if j!=i)]]
            fQ=F(Q.subs(sub)).as_expr()
            if not i:
                ans[('one-pin-infinity-u',pin,i)]=bool(h3(R4[:2]))
                aa=[S.Poly(F(z).as_expr(),u,modulus=p) for z in aff([mom(R4,j)for j in range(4)])]
                ans[('one-pin-no-late-infinity',pin,i)]=reduce(lambda q,r:q.gcd(r),aa).degree()==0
            else:
                # Nonzero coefficients ensure that the fourth known site
                # diverges whenever g diverges, besides the two ports and g.
                ans[('one-pin-no-early-infinity',pin,i)]=bool(S.Poly(R4[3],g,modulus=p).coeff_monomial(g))
                ans[('one-pin-no-late-infinity',pin,i)]=gc(aff([mom(R4,j)for j in range(4)]))
            ans[('one-pin-no-repeat-finite',pin,i)]=unit(M([*R4,c,d])+[fQ],tt,c,d)
            for j in range(3):
                if j==i:continue
                ff=F(fQ.subs(c,F(av[j].subs(sub)).as_expr())).as_expr()
                ans[('one-pin-repeat-finite',pin,i,j)]=unit(M([*R4,d,e])+[ff],tt,d,e)
    for i,j in permutations(range(3),2):
        # i -> v-port, j -> w-port
        b0=((1+v)*j-(1+w)*i)%p
        assert b0
        g0=(j-i)*pow(b0,-1,p)%p
        u0=(v-w)*pow(b0,-1,p)%p
        sub={g:g0,u:u0}
        k=next(h for h in range(3)if h not in [i,j])
        R3=[F(z.subs(sub)).as_expr()for z in [*fv,av[k]]]
        H=[val(mom(R3,j))for j in range(6)]
        M3=[[H[i+j]for j in range(3)]for i in range(3)]
        delta=det(M3); ans[('two-pin-dense-scalar',i,j)]=bool(delta)
        if delta:
            ff=[]
            for k0 in range(3):
                col=[row[:]for row in M3]
                for l in range(3):col[l][k0]=-H[l+3]
                ff.append(det(col)*pow(delta,-1,p)%p)
            ZZ=S.Poly(c**3+ff[2]*c*c+ff[1]*c+ff[0],c,modulus=p)
            JJ=S.Poly(F(Q.subs(sub)).as_expr(),c,modulus=p)
            ans[('two-pin-no-repeat-finite',i,j)]=ZZ.gcd(JJ).degree()==0
        val0=val(F(Q.subs(sub).subs(c,R3[-1])))
        ans[('two-pin-repeat',i,j)]=bool(val0)
    return ans
