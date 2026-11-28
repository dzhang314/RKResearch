"""Independent exact expansion of the four actual quadratic-cofactor determinants."""
from h58_af_shape import shape
from h58_star_projection import arrdet
from h5_arthfront_projection import model
from h567_arithmetic_projection import sc,remove_common,combine
from h567_af_ar_shape import I
from aq_rear import g,s as U,red,ev
from regular_star_projection import nodal,W,cof,Z

def audit():
    H,D,A,B,J,Zfront,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    gates,F,(c,x0,z,k,ph)=shape()
    assert x0==x
    E4=nodal([a,b,c,x]);WH=W(H);hr=ev(H,r)
    cols=[[],[]]
    for s0,D0 in enumerate(([Z]+E4,sc(-g,E4))):
        for j in range(3):
            E=[Z]*j+D0;WI=W(E);ID=I(E,0)
            def bez(j):
                return cof(H,WI,j)-cof(E,WH,j)
            Pi=[red((bez(j-1) if j else Z)-r*bez(j)
                    -(B*E[j] if j<len(E) else Z)+(H[j]*ID if j<len(H) else Z))
                for j in range(12)]
            assert not any(Pi[4:])
            cols[s0].append([red(hr*ID-B*ev(E,r)),Pi[3],Pi[2]])
    rows=[[[cols[i][j][k] for i in range(2)] for j in range(3)] for k in range(3)]
    term=[]
    for j in range(3):
        term.append([red(ph*c**j*(c-a)*(c-b)*c+(U-2)*x**j*(x-a)*(x-b)*x),
                     red(-g*(ph*c**j*(c-a)*(c-b)+(U-2)*x**j*(x-a)*(x-b)))])
    expect=[rows,[rows[0],rows[1],term],[rows[0],rows[2],term],[rows[1],rows[2],term]]
    assert tuple(remove_common(arrdet(r0),gs)[0] for r0 in expect)==gates
    assert red(c-x)==-g*U and red(x-c)==g*U
    assert red(U*F-(U-2)*ev(H,c)+ph*ev(H,x))==0
    print('independent exact audit: all four signed/actual terminal determinants and literal rear factors',flush=True)

if __name__=='__main__':audit()
