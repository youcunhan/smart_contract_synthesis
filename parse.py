import z3
import re
from lib.state_machine import smart_contract_state_machine
import time


# Define the contract input
contract_input = """
contract:
    crowdfunding

states:
    address owner, beneficiary;
    mapping(address => uint256) deposits;
    enum State {OPEN, SUCCESS, REFUND} state;
    uint256 raised;
    uint256 goal;
    uint256 closeTime;

transactions:
    init():
    {
        state <- OPEN;
        raised <- 0;
        goal <- 10000;
        closeTime <- 10000;
    }
    invest(value: uint256):
    {
        raised <- raised + value;
        deposits[sender] <- deposits[sender] + value;
    }
    close():
    {
        state <- SUCCESS if (raised >= goal) else REFUND
    }
    claimrefund(p: address):
    {
        p.balance <- p.balance + deposits[p]
        deposits[p] <- 0;
    }
    withdraw():
    {
        beneficiary.balance <- beneficiary.balance + raised;
        raised <- 0;
    }

traces:
    {
        invest(now = 1, sender = 0x114514, value = 100);
        invest(now = 2, sender = 0x114515, value = 10000);
        close(now = 3, sender = 0x20);
        withdraw(now = 4, sender = 0x20);
    }
    {
        invest(now = 1, sender = 0x114514, value = 100);
        invest(now = 2, sender = 0x114515, value = 10000);
        close(now = 10001, sender = 0x20);
        withdraw(now = 10002, sender = 0x20);
    }
    {
        invest(now = 1, sender = 0x114514, value = 100);
        invest(now = 2, sender = 0x114515, value = 100);
        close(now = 10001, sender = 0x20);
        claimrefund(now = 10002, sender = 0x20, p = 0x114514);
    }
    
properties:
    (raised >= goal) => !once(invest());
    !(once(claimrefund()) and once(withdraw()));
"""

# Define regular expressions for parsing
transaction_pattern = re.compile(r'\s+(\w+)\(([^)]*)\):\s*{([^}]*)}', re.DOTALL)
trace_pattern = re.compile(r'\s+{([^}]*)}')

# Parse transactions
trs = transaction_pattern.findall(contract_input)
trans = []
for tr in trs:
    name = tr[0]
    parameters = tr[1].split(',')
    content = tr[2].split('\n')
    n_content = []
    for c in content:
        if c.strip() != '':
            n_content.append(c.strip())
    trans.append([name, parameters, n_content])
print(trans)
# Parse traces
after_trace_pattern = re.compile(r'traces:(.*?)properties:', re.DOTALL)
after_trace_match = after_trace_pattern.search(contract_input)
after_trace = after_trace_match.group(1).strip() if after_trace_match else None
print(after_trace)
traces = trace_pattern.findall(contract_input)


print(traces)

# Define regular expressions for parsing
contract_name_pattern = re.compile(r'contract:\s+(\w+)', re.DOTALL)
states_pattern = re.compile(r'states:(.*?)transactions:', re.DOTALL)

# Extract contract name
contract_name_match = contract_name_pattern.search(contract_input)
contract_name = contract_name_match.group(1) if contract_name_match else None

# Extract states
states_match = states_pattern.search(contract_input)
states_content = states_match.group(1).strip() if states_match else None

print(f"Contract Name: {contract_name}")
print("States Content:")
print(states_content)