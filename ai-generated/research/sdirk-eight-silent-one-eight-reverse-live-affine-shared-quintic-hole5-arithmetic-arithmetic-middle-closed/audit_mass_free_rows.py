"""Symbolic coefficient audit independent of the scalar mass-free formulas."""
from h567_af_ar_shape import shape,I,det2
from h5_arthfront_projection import model
from h567_arithmetic_projection import sc
from aq_rear import red,g,s as U
from regular_star_projection import cof,nodal,W,Z

def audit():
    H,D,A,B,J,Zfront,gs,dat=model(False)
    a,b,r,x=dat[-4:]
    C,T,N,F,(c,d,k)=shape()
    E5=nodal([a,b,x,c,d])
    WH=W(H)
    cols=[]
    for D0 in ([Z]+E5,sc(-g,E5)):
        rows=[]
        for E in (D0,[Z]+D0):
            WE=W(E);ID=I(E,0)
            def bez(j):
                return cof(H,WE,j)-cof(E,WH,j)
            Pi=[red((bez(j-1) if j else Z)-r*bez(j)
                    -(B*E[j] if j<len(E) else Z)+(H[j]*ID if j<len(H) else Z))
                for j in range(12)]
            assert all(not p for p in Pi[4:])
            rows.append(Pi[2:4])
        cols.append(rows)
    r3=[[cols[i][j][1] for i in range(2)] for j in range(2)]
    r2=[[cols[i][j][0] for i in range(2)] for j in range(2)]
    assert det2(r3,r2)==C
    assert red((c-d)*(c-x))==-(g*U)**2
    assert red((x-c)*(x-d))==2*(g*U)**2
    print('exact polynomial coefficient audit passes for both s-basis columns and terminal factors',flush=True)

if __name__=='__main__':audit()
