"""Exact leading certificate for the padded arithmetic projection at 1103."""
from infinity_certificate import *

def val(a,p,t):
 def rat(x):return int(x.p)*pow(int(x.q),-1,p)
 assert a.degree()==0
 return (rat(a.a[0])+t*rat(a.b[0]))%p

def leading(f,i,p=1103,t=161):
 X=run(f,i,1);Y=run(f,i,1,p,t)
 assert X is not None and Y is not None
 h,a,b,e=X
 hh,aa,bb,ee=Y
 assert (h,e)==(hh,ee) and val(a,p,t)==aa and val(b,p,t)==bb
 R,Ph,J,dp,dj=inputs(f,i)
 assert max(map(len,Ph))<=4 and max(map(len,J))<=10
 m=len(J)-1
 D=3*m+27
 ell=R[-1];lc=ell.lc();d=ell.degree()
 C=lc**D*a/(b**e)
 cp=val(C,p,t)
 assert cp and val(lc,p,t)
 N=h+d*D
 assert N==(2040 if f else 2176)
 print('exact leading coefficient survives:',f,i,'degree',N,'tail leading degree',d,
       'unit leading mod',cp,flush=True)
 return True

if __name__=='__main__':
 for f,i in product((True,False),(0,1)):assert leading(f,i)
