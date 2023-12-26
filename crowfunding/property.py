import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.states import *

r2 = z3.Not(z3.And(aux_withdraw, aux_claimrefund))