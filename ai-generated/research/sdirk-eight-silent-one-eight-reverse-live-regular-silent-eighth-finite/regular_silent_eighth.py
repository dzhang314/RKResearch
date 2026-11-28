"""Regular physical eighth ordinarily silent: Padé then literal fifth finite witness."""
from regular_arith_projection import *
import exception_final as EF
from reverse_live_quartic import literal_fifth
from unequal_finite import Bfield,Tower
from equal_undetected_front import Nested
from off8_fibers import multicol
from gauss_separate import span_unit

@lru_cache(None)
def silent8_system(front):
    h,P,V,den,(a,b,q,La,Lb,A0,B0)=profile(front)
    x=1-g;u=v;c=x-g*u
    k=1+2*u-u*u;J=2*u+k*(u-2)
    Hx,Hc=map(lambda y:ev(h,y),(x,c))
    R,rem=divmod(red((u-2)*Hc-J*Hx),u);assert not rem
    F=red(R);assert F.degrees()[0]==5
    E=nodal([a,b,q,x,c]);X=W(h);M=[]
    for j in range(4):
        Y=[Z]*j+E;U=W(Y)
        M.append([red(cof(h,U,i)-cof(Y,X,i)) for i in range(1,5)])
    N=det(M);assert N.degrees()[0]==4
    V0,_=remove(V,[g,La,Lb])
    F,SF=remove(F,[g,La,Lb,V0])
    N,SN=remove(N,[g,La,Lb,V0])
    assert SF==[1,1,1,0] and SN==[6,4,4,2]
    print('regular silent eighth primitive',front,F.degrees(),N.degrees(),SF,SN,flush=True)
    start=perf_counter()
    D=red(F.resultant(N,0));assert D
    print('regular silent eighth exact F/N raw',front,D.degrees(),round(perf_counter()-start,1),flush=True)
    V0,_=remove(V,[g,La,Lb])
    h5,_=remove(h[-1],[g,La,Lb,V0])
    hx,_=remove(Hx,[g,La,Lb,V0])
    guards=[g,La,Lb,V0,s-A0,s-B0,x-a,x-b,x-q,h5,hx]
    D0,ss=remove(D,guards);assert D0
    assert D0.degrees()[1:3]==(32,90)
    assert ss==[12,0,0,0,0,0,0,0,0,3,4]
    print('regular silent eighth exact guarded',front,D0.degrees(),ss,flush=True)
    return D0,F,N,h,red(den*V),guards

def test_at(front,p,t0,g0):
    D,F,N,h,den,_=silent8_system(front)
    DD=evs(D,p,t0,g0)
    assert DD.degree()==D.degrees()[1]
    A,B,m=map(lambda w:cv(F2,w),ends(front,1));ha,hb=(A-1)/2,(B-1-m)/2
    H4=list(map(lambda w:cv(F2,w),pol(h4(front),lambda x:x)))
    f,n=[specialize_g(x,p,t0,g0) for x in (F,N)]
    h=[specialize_g(x,p,t0,g0) for x in h]
    _den=specialize_g(den,p,t0,g0)
    counts=[0,0]
    for M,e in DD.factor()[1]:
       K=Bfield(M,p,t0);s0=K(nmod_poly([0,1],p))
       FF,NN=map(lambda z:specialize_s(z,K,s0),(f,n))
       assert len(FF)==6 and FF[-1],('lead drop',M.degree())
       SS=gcdp(FF,NN)
       counts[0]+=1
       if len(SS)<=1:continue
       B0=Tower(SS);u=B0.gen();g=B0(K(g0));x=1-g;c=x-g*u
       A0,B1,m0,ha0,hb0=map(lambda x:B0(K(x)),(A,B,m,ha,hb))
       s=B0(s0);hs=EF.ev(list(map(lambda x:B0(K(x)),H4)),s)
       Qs=specialize_s(_den,K,s0);assert len(Qs)==1
       vv=B0(Qs[0]).inv()
       hscol=[specialize_s(xx,K,s0) for xx in h]
       assert all(len(y)<=1 for y in hscol)
       H=[B0(y[0])*vv if y else B0(0) for y in hscol]
       L=[z*g**j for j,z in enumerate(H)]
       assert EF.ev(L,A0)==ha0 and EF.ev(L,B1)==hb0 and EF.ev(L,s)==hs
       E=[[g*A0],[g*B1],[g*s],[x],[c]]
       J=EF.ordinary_cols([[v] for v in H],E,B0)
       J=[[v[0] if v else B0(0) for v in row] for row in J]
       try:T=EF.solve_minor(J,3,B0)+[B0(1)]
       except ArithmeticError as exc:
           print('silent regular potential degenerate pivot',front,p,t0,g0,M.degree(),len(SS)-1,flush=True);raise
       assert all(sum(T[j]*J[j][i] for j in range(4))==0 for i in range(4))
       Yn=[z*g**j/g**3 for j,z in enumerate(T)]
       Y5=literal_fifth(B0,A0,B1,m0,ha0,hb0,s,hs,L)
       multicol(Yn,Y5).inv()
       counts[1]+=1
    print('regular silent eighth finite witness',front,p,t0,g0,counts,flush=True)
    return counts
