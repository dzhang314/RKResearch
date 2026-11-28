"""Recover first-eight causal pivots from the actual fixed-q seed (mod 29)."""
from pathlib import Path
import sys
root=Path(sys.argv[1]).resolve()
spectrum=root/"erk10-fifteen-split-fixed-q-spectrum"
sys.path.insert(1,str(root/"erk10-fifteen-fixedq-29adic"))
sys.argv[1]=str(spectrum)
import lift as L
assert L.residual(L.seed,29)==[0]*6
S=L.S
S.F=L.literal.F=L.Z
c,g,R,d,a,b=map(L.Z,L.seed)
head=S.head(c,d,g,R,a,b,S.late(c,d,g,R),origin=True)
phys=S.nonlinear(head)
ys,w,u=[phys[k] for k in ("ys","w","u")]
params=L.literal.host_system(1-R,1-ys[9],1-ys[8],phys["eta"][9],phys["eta"][8])[-1]
Z=[wi*S.val(head["M"],y)-(y-c)*S.val(head["N"],y)*ui for y,wi,ui in zip(ys,w,u)]
H=[(y-d)*(wi*S.val(S.scale(S.derivative(head["M"]),L.Z(1,4)),y)+(2-c/a)*(y-c)*ui)
   for y,wi,ui in zip(ys,w,u)]
ins=[[int(v) for v in (wi,y*wi,y*y*wi,y**3*wi,ui,y*ui,gg,zz)]
     for y,wi,ui,zz,gg in zip(ys,w,u,Z,H)]
L.literal.lin=L.unit_lin
K=L.literal.high_reverse(head,phys,params)
print("physical input rows",ins,sep="\n")
for k in range(1,9):
    _,d=L.inv_and_det([row[:k] for row in ins[:k]])
    assert d
    print("leading physical prefix",k,"det",d)
print("raw K seed, no adjustment of physical rows", [list(map(int,row)) for row in K],sep="\n")
print("Z and G",list(map(int,Z)),list(map(int,H)))
