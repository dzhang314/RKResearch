"""Check every retained nominal/leading-drop six-peg arithmetic-tail component."""
from functools import lru_cache
from h567_arithmetic_projection import project,signed_model,exact_tail,model,Co,g
from h567_star_modular import minors
from h5_star_modular import unit,rry
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from unequal_finite import E

def norm(G):
    return G.a*G.a-G.b*G.b/2

@lru_cache(None)
def exact_gamma(cubic):
    A=project(cubic,False);B=project(cubic,True)
    assert len(A)==len(B)
    out=[]
    for (M,P,Q,a),(N,P0,R,b) in zip(A,B):
        assert P==P0 and a==b
        if not M.b and not N.b:
            D=M.a.gcd(N.a)
        else:
            D=norm(M).gcd(norm(N))
        D=D//D.gcd(D.derivative()) # preserve every characteristic-zero distinct gamma
        D=E(D).monic()
        assert D.degree()==(27 if cubic else 3 if a=="degenerate" else 30)
        print('arithmetic six-peg exact gamma gcd',cubic,a,M.degree(),N.degree(),D.degree(),flush=True)
        out.append((D,P,Q,R,a))
    return tuple(out)

def test(cubic,p,t):
    H,D,A,B,J,Zf,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    C,N,F,_=signed_model()
    xa=exact_tail()[3]
    out=[]
    for M,P,Q,R,kind in exact_gamma(cubic):
        d0=Bfield(nmod_poly([0,1],p),p,t).cast(M)
        assert d0.degree()==M.degree() and d0.leading_coefficient()==1
        parts=d0.factor()[1]
        chk=nmod_poly([1],p)
        for h,e in parts:chk*=h**e
        assert chk==d0
        done=[];bad=[]
        for f,e in parts:
            N0=Bfield(f,p,t)
            key=(kind,f.degree(),e);fp=str(f)
            Yp=[lcmo(N0,Co(T)) for T in (P,Q,R)]
            if not any(len(U)==T.degrees()[0]+1 for U,T in zip(Yp,(P,Q,R))):
                bad.append(('Y leading',key,fp));continue
            E0=gcdp(gcdp(Yp[0],Yp[1]),Yp[2])
            assert E0 and E0[-1]==1
            key+=(len(E0)-1,)
            if len(E0)==1:
                done.append(('no_Y',key));continue
            U,y,I=extend(N0,E0)
            cvy=lambda P:rry(N0,P,y,I)
            if cubic:
                J0=[cvy(j) for j in Co(J,1)]
                if not unit(J0[-1]):
                    bad.append(('s leading',key,fp,[unit(cvy(q)) for q in gs]));continue
                V,s,I0=extend(U,mon(J0))
            else:
                V,s,I0=U,(2*y+1)/3,lambda a:a
            cv=lambda P:I0(cvy(P))
            F0=[cv(q) for q in Co(F,1)]
            if not unit(F0[-1]):
                bad.append(('u leading',key,fp,[unit(cv(q)) for q in gs]));continue
            assert len(F0)==6
            W,u,I1=extend(V,mon(F0))
            q0=I1(s);cc=lambda T:I1(cv(T))
            uu=lambda P:horner(list(map(cc,Co(P,1))),u)
            ex=[horner(list(map(uu,P)),q0) for P in (C,N)]
            c,d,k=map(uu,xa)
            a0,b0,g0,r0,x0,be=map(cc,(a,b,g,r,x,B))
            pegs=[a0,b0,g0*q0,d,c,x0]
            H0=list(map(cc,H))
            gates=minors(W,H0,be,r0,pegs)
            try:span_unit(W,*ex,*gates)
            except ArithmeticError:
                bad.append(('signed',key,fp,[unit(cc(q)) for q in gs],[unit(z) for z in ex+gates]));continue
            done.append(('signed',key))
        assert len(done)+len(bad)==len(parts)
        print('arith six-peg complete local',cubic,p,t,kind,'kept',M.degree(),'done',done,'bad',bad,flush=True)
        out.append((len(done),bad))
    return out
