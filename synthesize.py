import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.states import *
from crowfunding.transaction import *
from crowfunding.trace import *
from crowfunding.property import *
import time

# print("no strategy:")
# statemachine.clear_guards()
# T1 = time.time()
# statemachine.generate_candidate_guards(["<", "<=", ">", ">=", "="], positive_traces, drop_unreasonable=False)
# T2 = time.time()
# print("Time cost:%ss" % (T2 - T1))
# guard = statemachine.synthesize(properties, positive_traces, simulate_before_bmc=False)
# T3 = time.time()
# print('Time cost:%ss' % (T3 - T2))


# print("drop unreasonable candidate guards:")
# statemachine.clear_guards()
# T1 = time.time()
# statemachine.generate_candidate_guards(["<", "<=", ">", ">=", "="], positive_traces, drop_unreasonable=True)
# T2 = time.time()
# print("Time cost:%ss" % (T2 - T1))
# guard = statemachine.synthesize(properties, positive_traces, simulate_before_bmc=False)
# T3 = time.time()
# print('Time cost:%ss' % (T3 - T2))


# print("simulate before bmc:")
# statemachine.clear_guards()
# T1 = time.time()
# statemachine.generate_candidate_guards(["<", "<=", ">", ">=", "="], positive_traces, drop_unreasonable=False)
# T2 = time.time()
# print("Time cost:%ss" % (T2 - T1))
# guard = statemachine.synthesize(properties, positive_traces, simulate_before_bmc=True)
# T3 = time.time()
# print('Time cost:%ss' % (T3 - T2))


print("both:")
statemachine.clear_guards()
T1 = time.time()
statemachine.generate_candidate_guards(["<", "<=", ">", ">=", "="], positive_traces, drop_unreasonable=True)
T2 = time.time()
print("Time cost:%ss" % (T2 - T1))
guard = statemachine.synthesize(properties, positive_traces, simulate_before_bmc=True)
T3 = time.time()
print('Time cost:%ss' % (T3 - T2))