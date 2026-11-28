"""Exact algebraic unbounded lift check for the fixed-q F29 tableau."""
import sympy as S
import origin_polynomial as op

def main():
    h0,f0,k0,j0,origin=op.coefficients()
    c0=op.c
    num,den=S.fraction(origin)
    fs=S.factor_list(num,c0)[1]
    p=next(P for P,m in fs if P.subs(c0,2)%29==0)
    assert S.degree(p,c0)==10 and S.diff(p,c0).subs(c0,2)%29 and den.subs(c0,2)%29
    assert S.Poly(p,c0).LC()%29
    print("origin polynomial degree 10 and 29-unit leading term / derivative",flush=True)
    K=S.QQ.algebraic_field(S.CRootOf(p,0))
    c=K.unit
    y0=S.Symbol("y")
    T=K.poly_ring(y0); y=T.gens[0]
    g,R,d=map(K.convert,(6,15,26))
    def ce(fn):
        def value(z):
            a=K.zero
            for co in S.Poly(z,c0).all_coeffs():
                a=a*c+K.convert(co)
            return a
        u,v=S.fraction(fn);return value(u)/value(v)
    def eval(p,x):
        t=K.zero
        for j in range(int(p.degree()),-1,-1):
            t=t*x+p[(j,)] if (j,) in p else t*x
        return t
    def I(p,j=0):
        return sum((u/K.convert(k[0]+j+1) for k,u in p.items()),K.zero)
    def C(x):return T.ring.ground_new(x)
    def prod(s):
        q=T.one
        for u in s:q*=u
        return q
    h,f,k,j=map(ce,(h0,f0,k0,j0))
    l=j-2*k/c
    assert k+l==K.zero
    print("exact A(1)=0 in Q[c]",flush=True)
    om=210*c**3-336*c*c+168*c-28
    e=c*(c-d)/(c+c*om*d)
    tau=e*d
    Qc,Ql=tau*k,tau*l
    T3=prod((y-C(f),y-C(g),y-C(h)))
    B=prod((y-C(c),y-C(d),y-C(e),T3))
    p3=y*(y-1)*(y-C(c))
    E0,E1=I(y*(y-1)*B),I(y*(y-1)*B,1)
    V=sum((C(w)*y**i for i,w in enumerate([
        75*c**3-108*c*c+45*c-5,
        -3*(175*c**3-244*c*c+97*c-10),
        3*(350*c**3-476*c*c+183*c-18),
        -15*(42*c**3-56*c*c+21*c-2),
    ])),T.zero)
    beta=eval(V,K.zero)/eval(T3,K.zero)
    Phi=prod((y-1,y-C(c),y-C(d),y-C(e),V-C(beta)*T3))
    u=E0*R*c*c-2*Qc*c
    v=-E0*R*c-E0*c*c+E1*c+2*Qc-Ql*c
    w=-E1*R*c*c+Qc*c*c
    uu,vv,ww=-I(Phi,1),I(Phi),I(Phi,2)
    delta=u*vv-v*uu
    s=(v*ww-w*vv)/delta
    q=(w*uu-u*ww)/delta
    D7=prod((y*y-C(s)*y+C(q),y-C(d),y-C(e),T3))
    assert D7.degree()==7
    print("exact symmetric scalar spectrum reconstructed",flush=True)
    mu=T.zero
    mp=[I(p3,j) for j in range(7)]
    for i in range(7):
        mu+=C(sum((D7[(j,)]*mp[j-1-i] for j in range(i+1,8) if (j,) in D7),K.zero))*y**i
    Cnu=(1-R)*eval(V,R)
    def phase(z):return -eval(mu,z)*eval(V,z)/(z*Cnu)
    af,ag,ah=map(phase,(f,g,h))
    slope=(ag-af)/(g-f); intercept=af-slope*f
    assert slope*h+intercept==ah
    q1=C(intercept)+C(slope)*y
    print("all three late physical cofactor contacts exact in Q[c]",flush=True)
    # U=-η is degree ≤4 exactly when this explicit quartic fits
    # every scored label. The host value is built in as U(R)=-1.
    U0=(y-1)*V/C(Cnu)
    T4=(y-C(R))*T3
    E=(mu*U0-y*(1-y)*q1)%D7
    B=(mu*T4)%D7
    assert B
    i=next(iter(B))
    for j in range(7):
        assert E.get((j,),K.zero)*B[i]==B.get((j,),K.zero)*E.get(i,K.zero)
    sig=-E.get(i,K.zero)/B[i]
    U=U0+C(sig)*T4
    assert U.degree()<=4 and eval(U,R)==-K.one
    print("all three unused nonlinear eta-u moments exact: deg U ≤ 4 and U(R) = -1",flush=True)

if __name__=="__main__":main()
