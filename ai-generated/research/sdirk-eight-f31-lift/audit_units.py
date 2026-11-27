#!/usr/bin/env python3
"""Audit every executed quotient in the literal finite assembly at its 31-adic ingress."""
import ast
from pathlib import Path
from collections import defaultdict

file=Path(__file__).resolve().with_name('lift_assembly.py')
data=defaultdict(set)
class Denominator(ast.NodeTransformer):
    active=False
    def visit_FunctionDef(self,node):
        previous=self.active
        self.active=previous or node.name in ("moment","assemble")
        self.generic_visit(node)
        self.active=previous
        return node
    def visit_BinOp(self,node):
        self.generic_visit(node)
        if self.active and isinstance(node.op,ast.Div):
            node.right=ast.Call(func=ast.Name('guard',ast.Load()),
                       args=[ast.Constant(node.lineno),node.right],keywords=[])
        return node
def guard(lineno,q):
    res=int(q)%31
    assert res != 0
    data[lineno].add(res)
    return q
tree=ast.fix_missing_locations(Denominator().visit(ast.parse(file.read_text())))
env={'__file__':str(file),'__name__':'quotient_unit_audit','guard':guard}
exec(compile(tree,str(file),'exec'),env)
A,b,seed=env['assemble'](31,(11,17,4))
assert seed==[11,17,4,2,11]
assert A and b
assert data
print('all executed quotient denominators are units at 31:',len(data),'literal code lines; residues',sorted(set.union(*data.values())))
