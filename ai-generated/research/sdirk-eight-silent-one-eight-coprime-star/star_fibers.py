"""Reduced conditional fifth and homogeneous literal-sixth gates in the exact star projection."""
from eight_star_projection import *
from off8_fibers import multicol

def all_coeffs(field,y,v):return [eval_E(field,y,s) for s in v]
def eval_E(F,g,h):return ev([F(h.coeff(i)) for i in range(h.degree()+1)],g)

def sixth_gate(U,A,B,m,ha,hb,H4,q,C,y):
    S,AA,e,TA,QA=context(U,A,B,m,ha,hb,None,H4)
    Qy,Py=ev(q,y),ev(C,y)
    j0,t0,_=front5(U,A,B,S,e,TA,QA,y,U(0))
    j1,t1,_=front5(U,A,B,S,e,TA,QA,y,U(1))
    J,T=Qy*j0+Py*(j1-j0),Qy*t0+Py*(t1-t0)
    moments=[
      add(mul(q,[U(-1),U(1)]),sc(C,-2)),
      add(mul(q,[U(0),U(-1),U(1)/2]),sc(C,-2)),
      add(mul(q,[U(0),U(0),U(-1),U(1)/3]),sc(C,-U(4)/3)),
      add(mul(q,[U(0),U(0),U(0),U(-1),U(1)/4]),mul(add(TA,[U(-2)]),C))]
    def gate(z):
        H2=add(S,sc(AA,ev(e,z)))
        F3=nodal([A,B,z])
        DA=add(mul(add(QA,[U(-1)]),C),
               sc(sum_poly([sc(q0,h) for q0,h in zip(moments,H2)]),-1))
        V0=sum_poly([sc(q0,w) for q0,w in zip(moments,F3)])
        return add(sc(DA,ev(F3,y)*Qy),sc(V0,ev(H2,y)*Qy-Py))
    z0,zp,zm=gate(U(0)),gate(U(1)),gate(U(-1))
    first=sc(add(zp,sc(zm,-1)),U(1)/2)
    second=add(sc(add(zp,zm),U(1)/2),sc(z0,-1))
    L=sum_poly([sc(z0,J*J),sc(first,-J*T),sc(second,T*T)])
    return L

def verify(front,p,t,verbose=False):
    G,ds,YY,E5,guards,_,_=data(front)
    B0=Bfield(nmod_poly([0,1],p),p,t)
    M=B0.cast(G)
    assert M.degree()==G.degree() and M.leading_coefficient()==1
    counts=[0,0,0]
    for M0,_ in M.factor()[1]:
        F=Bfield(M0,p,t);ga=F(nmod_poly([0,1],p))
        counts[0]+=1
        # True nonzero at all characteristic-zero candidates of this chart.
        for h in guards:eval_E(F,ga,h).inv()
        Y=mon(all_coeffs(F,ga,YY)); assert len(Y)==4
        T=gcdp(Y,all_coeffs(F,ga,E5))
        if len(T)<=1:continue
        counts[1]+=1
        if verbose:print('candidate degree',front,p,t,M0.degree(),len(T)-1,flush=True)
        U=Tower(T); y=U.gen()
        a,b,q0,q1,A,B,m,ha,hb,H4=ds
        Q=[U(eval_E(F,ga,q0)),U(eval_E(F,ga,q1))]
        ca=lambda j:U(eval_E(F,ga,j))
        A,B,m,ha,hb=map(ca,(A,B,m,ha,hb))
        H4=list(map(ca,H4))
        C=[U(v)*U(ga)**j for j,v in enumerate(Lco)]
        Y=list(map(U,Y))
        W=[Y[1]+Y[2]*y+y*y,Y[2]+y,U(1)]
        assert ev(Y,y)==0
        multicol(W,sixth_gate(U,A,B,m,ha,hb,H4,Q,C,y)).inv()
        counts[2]+=1
    return tuple(counts)
