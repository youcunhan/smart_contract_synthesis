import itertools
result_guards = [[("r1tr1", "r1g1"), ("r1tr2", "r1g2")], [("r2tr1", "r2g1"), ("r2tr2", "r2g2"), ("r2tr3", "r2g3")], [("r3tr1", "r3g1"), ("r3tr2", "r3g2")]]
result_guards_cartesian = list(itertools.product(*result_guards))
print(result_guards_cartesian)