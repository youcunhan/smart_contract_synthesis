import lib.bmc
import z3

x0 = z3.Const('x0', z3.BitVecSort(4))
x1 = z3.Const('x1', z3.BitVecSort(4))
y0 = z3.Const('x0', z3.BitVecSort(4))
y1 = z3.Const('x1', z3.BitVecSort(4))
x3 = z3.BitVec('x3', 4)


print(lib.bmc.bmc(z3.And(x0 == 0, y0 == 0), z3.Or(x1 == x0 + 1, y1 == y0 + 1), z3.And(x0 == 5, y0 == 2), [x3], [x0,y0], [x1,y1]))