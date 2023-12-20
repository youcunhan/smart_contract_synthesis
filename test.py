import z3

amount = z3.BitVec('amount',256)

raised = z3.BitVec('raised',256)
raisedOut = z3.BitVec('raisedOut',256)

p = z3.And(raised == 0, raisedOut == raised)
print(p)
print(z3.simplify(p))