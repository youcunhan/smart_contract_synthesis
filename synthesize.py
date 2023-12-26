import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.states import *
from crowfunding.transaction import *
from crowfunding.trace import *
from crowfunding.property import *


statemachine.clear_guards()

possible_guards = [
    state == OPEN, 
    state == SUCCESS, 
    state == REFUND, 
    now > CLOSETIME, 
    now < CLOSETIME, 
    raised >= GOAL, 
    raised < GOAL, 
]

iter = 0
# while True:
while iter < 100:
    print("iter", iter)
    iter += 1
    ntrace = statemachine.bmc(z3.Not(r2))
    if ntrace == None:
        print("no more counter example")
        break
    print("find counter example:")
    print(ntrace)
    result_guard = statemachine.synthesize_one_guard(possible_guards, ntrace, positive_traces)
    tr, g = result_guard[0]
    print("synthesized guard:")
    print(result_guard)
    statemachine.add_guard(tr, g)
    print()

print("Final guards:")
print(statemachine.condition_guards)