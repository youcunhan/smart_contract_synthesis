import z3
from lib.state_machine import smart_contract_state_machine


statemachine = smart_contract_state_machine('Crowdsale')
state, stateOut = statemachine.add_state("state", z3.BitVecSort(2))
deposits, depositsOut = statemachine.add_state("deposits", z3.ArraySort(z3.BitVecSort(256), z3.BitVecSort(256)))
totalDeposits, totalDepositsOut = statemachine.add_state("totalDeposits", z3.BitVecSort(256))
raised, raisedOut = statemachine.add_state("raised", z3.BitVecSort(256))
aux_claimrefund, aux_claimrefundOut = statemachine.add_state("aux_claimrefund", z3.BoolSort())
aux_withdraw, aux_withdrawOut = statemachine.add_state("aux_withdraw", z3.BoolSort())

GOAL = 10000
CLOSETIME = 10000


OPEN = 0
SUCCESS = 1
REFUND = 2