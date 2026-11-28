"""Exact finite field reconstructions after the shared-center rank-two projection."""
import sympy as S
from sympy.polys.rings import ring
from shared_split_fullrank import *
mm=S.Symbol('m')

def rec():
    g=C.resultant(F,'p').gcd(C.resultant(V,'p'))
    for Q,i in g.factor()[1]:
        M0=S.Poly.from_dict({(int(a),):int(c) for (a,b),c in Q.to_dict().items()},mm,domain=S.QQ)
        assert M0.is_irreducible
        K=S.QQ if M0.degree()==1 else S.QQ.algebraic_field((M0,mm))
        m0=K.convert(-M0.nth(0)/M0.nth(1)) if M0.degree()==1 else K.unit
        RR,X=ring('p',K)
        def im(P):
            return sum(RR(K.convert(int(c))*m0**int(i))*X**int(j) for (i,j),c in P.to_dict().items())
        G=im(C).gcd(im(F)).gcd(im(V))
        guards=[N,p,J,E,DD,35*M*M-3*N*N,Wprod,Dprod]
        print('m projected degree',M0.degree(),str(M0.as_expr()) if M0.degree()<=3 else '>3','p-gcd degree',G.degree(),flush=True)
        for nn in guards:
            f=im(nn)
            if not f:
               G=RR.one
               break
            while (h:=G.gcd(f)).degree()>0:G=G.exquo(h)
        print('  after p guards degree',G.degree(),flush=True)
        assert G.degree()==0
        yield M0,K,m0,RR,X,G.monic(),im

if __name__=='__main__':
    ans=list(rec())
    assert len(ans)==4
    print('excluded every true rank-two fibre')
