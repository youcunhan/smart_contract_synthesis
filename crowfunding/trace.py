import z3
from lib.state_machine import smart_contract_state_machine
from crowfunding.transaction import *

positive_traces = []
positive_traces.append(
    [
        ('invest', now == 1, sender == 0x114514, value == 100),
        ('invest', now == 2, sender == 0x114515, value == 100),
        ('invest', now == 3, sender == 0x114516, value == 100),
        ('invest', now == 4, sender == 0x114517, value == 100),
        ('invest', now == 5, sender == 0x114518, value == 100),
        ('invest', now == 6, sender == 0x114519, value == 100),
        ('invest', now == 7, sender == 0x114520, value == 100),
    ]
)

positive_traces.append(
    [
        ('invest', now == 1, sender == 0x114514, value == 100),
        ('invest', now == 2, sender == 0x114515, value == GOAL),
        ('close_success', now == 3),
        ('withdraw', now == 4)
    ]
)

positive_traces.append(
    [
        ('invest', now == 1, sender == 0x114514, value == 100),
        ('invest', now == 2, sender == 0x114515, value == GOAL),
        ('close_success', now == CLOSETIME + 1),
        ('withdraw', now == CLOSETIME + 2)
    ]
)

positive_traces.append(
    [
        ('invest', now == 1, sender == 0x114514, value == 100),
        ('invest', now == 2, sender == 0x114515, value == 100),
        ('close_refund', now == CLOSETIME + 1),
        ('claimrefund', now == CLOSETIME + 2, p == 0x114514)
    ]
)

positive_traces.append(
    [
        ('invest', now == 1, sender == 0x114514, value == 100),
        ('invest', now == 2, sender == 0x114515, value == GOAL),
        ('close_success', now == 3),
    ]
)