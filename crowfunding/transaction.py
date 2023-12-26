import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.states import *

p = z3.BitVec('p',256)
now = statemachine.nowOut

statemachine.set_init(z3.And(
    z3.ForAll(p, deposits[p]==0),
    raised == 0,
    totalDeposits == 0,
    state == OPEN,
    aux_claimrefund == False,
    aux_withdraw == False
))


sender = z3.BitVec('sender',256)
value = z3.BitVec('amount',256)

statemachine.add_tr(
    tr_name = "invest",
    parameters = (value, sender),
    guard = z3.And(# now <= CLOSETIME,
                   raised < GOAL,
                   ),
    transfer_func = z3.And(raisedOut == raised + value,
                           depositsOut == z3.Update(deposits,sender,deposits[sender]+value),
                           totalDepositsOut == totalDeposits+value,
                        )
)

statemachine.add_tr(
    tr_name = "close_success",
    parameters = None,
    guard = z3.And(raised >= GOAL,
                   ),
    transfer_func = z3.And(
                           stateOut == SUCCESS,
                        )
)

statemachine.add_tr(
    tr_name = "close_refund",
    parameters = None,
    guard = z3.And(now > CLOSETIME,
                   raised < GOAL,
                   ),
    transfer_func = z3.And(stateOut == REFUND,
                        )
)

p = z3.BitVec('p',256)
statemachine.add_tr(
    tr_name = "claimrefund",
    parameters = (p, ),
    guard = z3.And(state == REFUND,
                   raised < GOAL,
                   ),
    transfer_func = z3.And(depositsOut == z3.Update(deposits,p,0),
                           totalDepositsOut == totalDeposits - deposits[p],
                           aux_claimrefundOut == True,
                        )
)


statemachine.add_tr(
    tr_name = "withdraw",
    parameters = None,
    guard = z3.And(state == SUCCESS,
                   ),
    transfer_func = z3.And(totalDepositsOut == 0,
                           aux_withdrawOut == True,
                        )
)
