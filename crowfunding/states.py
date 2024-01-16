import z3
from lib.state_machine import smart_contract_state_machine


statemachine = smart_contract_state_machine('Crowdsale')
state, stateOut = statemachine.add_state("state", z3.BitVecSort(2))
deposits, depositsOut = statemachine.add_state("deposits", z3.ArraySort(z3.BitVecSort(256), z3.BitVecSort(256)))
totalDeposits, totalDepositsOut = statemachine.add_state("totalDeposits", z3.BitVecSort(256))
raised, raisedOut = statemachine.add_state("raised", z3.BitVecSort(256))

GOAL = 10000
CLOSETIME = 998877


OPEN = 0
SUCCESS = 1
REFUND = 2

statemachine.constants.append(GOAL)
statemachine.constants.append(CLOSETIME)
# statemachine.constants.append(OPEN)
# statemachine.constants.append(SUCCESS)
# statemachine.constants.append(REFUND)