from projection_folded import *
CZk=fmpz_mpoly_ctx.get(('H','s','z'),'lex')
def build_odd_rank():
    F0,P,guards,Zs=build()
    Dax,Aan,Ban,m0,m1,m2,m3,U,V,r0,r1,r2=Zs
    del0=a-b
    J=(r1/del0+r2)
    assert J.d.is_constant()
    assert not (2*del0*F(J.n.compose(Cq.constant(0),a.n,b.n),J.d)
                 -(N(a/2)*D(b/2)-N(b/2)*D(a/2)))
    W=(U*V-4*L4(Z)*r2*r2)
    A=m2+del0*m3
    B=m1+del0*A
    J0=m0*m3-A*B
    J1=m3*r0-B*r2
    assert J0.d.is_constant() and J1.d.is_constant() and W.d.is_constant()
    Gs=ip(J.n)
    A0=shape(Gs)
    P0=shape(strip(ip(W.n),guards))
    P1=shape(strip(ip(J0.n)/ (CZ.gens()[1]-CZ.gens()[2]),guards))
    P2=shape(strip(ip(J1.n),guards))
    print('odd-rank degrees before H recovery',[i.degrees() for i in [A0,P0,P1,P2]],flush=True)
    assert [x.degrees() for x in (A0,P0,P1,P2)]==[(1,4,4),(6,8,8),(14,8,7),(9,9,8)]
    out=[P0,P1,P2,*F0]
    R=[]
    for f in out:
        g=A0.resultant(f,'H')
        assert g and not g.degrees()[0]
        R.append(g)
    return [A0,*out],R,guards+[ip((U-V).n)]
def odd_project():
    rows,R,guards=build_odd_rank()
    J=rows[0]
    lead=CZk.from_dict({(0,s,z):c for (i,s,z),c in J.to_dict().items() if i==1})
    T=[lead]
    for Q in guards:
        X=shape(Q*swap(Q))
        U=J.resultant(X,'H')
        assert U
        T.append(U)
    R=[strip(r,T) for r in R]
    print('after true projected guard stripping',[p.degrees() for p in R],flush=True)
    pure=[e for e in T if not e.degrees()[2]]
    Q=R[0]
    rs=[]
    for P,want in zip((R[2],R[4],R[6],R[7],R[1]),(592,576,464,448,1024),strict=True):
        Y=strip(Q.resultant(P,'z'),pure)
        assert Y.degrees()==(0,want,0)
        print('outer univariate s degree',want,flush=True)
        if not Y:continue
        rs.append(Y)
        ans=Y if len(rs)==1 else ans.gcd(Y)

    return ans,R,T,rows

if __name__=='__main__':odd_project()
