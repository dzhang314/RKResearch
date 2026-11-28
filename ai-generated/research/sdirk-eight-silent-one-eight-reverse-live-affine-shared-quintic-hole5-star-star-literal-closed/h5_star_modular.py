"""Complete local components for the star-front/star-rear literal hole5 case."""
from h5_star_branches import branches,model,edges,Co,g,gpoly
from h5_rank_check import signed_rows
from aq_modular import lcmo,mon,horner,Bfield,nmod_poly,gcdp,det
from aq_modular import ev as peval
from arith_ordinary_reconstruction import extend
from gauss_separate import span_unit
from itertools import combinations

def unit(a):
    try: return a.inv()*a==1
    except (ArithmeticError,ZeroDivisionError): return False

def rry(B,P,y,I):
    return horner([I(B(gpoly(v))) for v in Co(P,0)],y)

def test(slot,cubic,p,t0):
    H,D,A,B,J,Z,gs,dat=model(True)
    a,b,r,x=dat[-4:]
    F,E,O=edges(True,slot)
    out=[];count=0
    for M,P,Q,kind in branches(slot,cubic):
        R=Bfield(nmod_poly([0,1],p),p,t0).cast(M)
        assert R.degree()==M.degree() and R.leading_coefficient()==1
        facs=R.factor()[1]
        rr=nmod_poly([1],p)
        for f,e in facs:rr*=f**e
        assert rr==R
        done=[];bad=[]
        for q,e in facs:
            N=Bfield(q,p,t0); key=(kind,q.degree(),e); qp=str(q)
            P0,Q0=[lcmo(N,Co(T)) for T in (P,Q)]
            if len(P0)!=P.degrees()[0]+1 and len(Q0)!=Q.degrees()[0]+1:
                bad.append(('Y leading',key,qp));continue
            G=gcdp(P0,Q0)
            assert G and G[-1]==1
            key+= (len(G)-1,)
            if len(G)==1:
                done.append(('no_Y',key));continue
            U,y,I=extend(N,G)
            cvy=lambda T:rry(N,T,y,I)
            if cubic:
                J0=[cvy(v) for v in Co(J,1)]
                if not unit(J0[-1]):
                    bad.append(('s leading',key,qp,[unit(cvy(d)) for d in gs]));continue
                V,s,I0=extend(U,mon(J0))
            else:
                V,s,I0=U,(2*y+1)/3,lambda z:z
            cv=lambda T:I0(cvy(T))
            F0,F1=map(cv,Co(F,1))
            if not unit(F1):
                bad.append(('w leading',key,qp,[unit(cv(d)) for d in gs]));continue
            w=-F0/F1
            try:
                span_unit(V,*(horner(list(map(cv,Co(T,1))),w) for T in (O,E)))
                done.append(('no_w',key));continue
            except ArithmeticError: pass
            W,v,I1=extend(V,[-w,V(0),V(1)])
            cv2=lambda T:I1(cv(T))
            a0,b0,g0,r0,x0,be=map(cv2,(a,b,g,r,x,B))
            c,d=x0-g0*(1+v),x0-g0*(1-v)
            p4=g0*I1(s)
            pegs=[b0 if slot==2 else a0,p4,x0,c,d]
            H0=list(map(cv2,H))
            rows,En=signed_rows(W,H0,be,r0,pegs)
            Ac=peval(H0,c)*peval(En,c);Ax=peval(H0,x0)*peval(En,x0)
            rows.append([Ac*c**j-Ax*x0**j for j in range(3)])
            try:span_unit(W,*[det(list(M)) for M in combinations(rows,3)])
            except ArithmeticError:
                bad.append(('signed',key,qp,[unit(cv2(d)) for d in gs]));continue
            done.append(('weight',key))
        assert len(done)+len(bad)==len(facs)
        print('star corrected hole5 complete',slot,cubic,p,t0,kind,'kept',M.degree(),'done',done,'bad',bad,flush=True)
        out+=bad;count+=len(done)
    return count,out
