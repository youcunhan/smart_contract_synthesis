import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.states import *

def prev(state):
    return statemachine.prev(state)[0]

def func(name):
    return statemachine.func == name

def once(funcname):
    return statemachine.once[funcname][0]

properties = []

r2 = z3.Not(z3.And(once('withdraw'), once('claimrefund')))

r3 = z3.Implies(prev(raised) >= GOAL, z3.Not(func("invest")))

properties.append(r2)
properties.append(r3)