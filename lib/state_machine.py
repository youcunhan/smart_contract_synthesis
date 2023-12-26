from lib.bmc import extract_model
from lib.ts import Ts
import z3

def contains(x, e):
    return x.__repr__() == e.__repr__() or any([contains(x, c) for c in e.children()])


class smart_contract_state_machine:
    def __init__(self, name):
        self.name = name
        self.states = {}
        self.transitions = []
        self.condition_guards = {}
        self.tr_parameters = {}
        self.transfer_func = {}
        self.ts = Ts(name)
        self.now_state = None
        self.now, self.nowOut = self.add_state('now', z3.BitVecSort(256))
        self.func, self.funcOut = self.add_state('func', z3.StringSort())

    def add_state(self, state_name, type):
        state, stateOut = self.ts.add_var(type, name = state_name)
        self.states[state_name] = (state, stateOut)
        return state, stateOut

    def add_tr(self, tr_name, parameters, guard, transfer_func):
        self.transitions.append(tr_name)
        self.tr_parameters[tr_name] = parameters
        self.condition_guards[tr_name] = guard
        transfer_func = z3.And(transfer_func, self.funcOut == tr_name)
        for state in self.states:
            if state == 'now' or state == 'func':
                continue
            if not contains(self.states[state][1], transfer_func):
                transfer_func = z3.simplify(z3.And(transfer_func, self.states[state][1] == self.states[state][0]))
        
        self.transfer_func[tr_name] = transfer_func

    def clear_guards(self):
        for i in self.condition_guards.keys():
            self.condition_guards[i] = z3.BoolVal(True)

    def change_guard(self, tr_name, *new_guard):
        if tr_name not in self.transitions:
            print("Transition not found!")
            return False
        else:
            self.condition_guards[tr_name] = z3.simplify(z3.And(*new_guard))
            return True
        
    def add_guard(self, tr_name, *new_guard):
        if tr_name not in self.transitions:
            print("Transition not found!")
            return False
        else:
            self.condition_guards[tr_name] = z3.simplify(z3.And(self.condition_guards[tr_name], *new_guard))
            return True

    def set_init(self, init_state):
        self.ts.Init = z3.And(init_state, self.now == 0, self.func == 'init')

    def transfer(self, tr_name, show_log, *parameters):
        success = z3.And(self.now_state, self.condition_guards[tr_name], self.nowOut > self.now, z3.And(*parameters))
        # print(success)
        s = z3.Solver()
        s.add(success)
        result = s.check()
        if result == z3.unsat:
            if show_log:
                print("Transfer failed: ", tr_name, "with parameters", parameters)
            return False
        else:
            if show_log:
                print("Transfer success: ", tr_name, "with parameters", parameters)
            s = z3.Solver()
            s.add(z3.And(self.now_state, self.transfer_func[tr_name], z3.And(*parameters)))
            # print(z3.And(self.now_state, self.transfer_func[tr_name], z3.And(*parameters)))
            result = s.check()
            m = s.model()
            self.now_state = z3.BoolVal(True)
            for v in self.states.values():
                self.now_state = z3.And(self.now_state, v[0] == m[v[1]])
            self.now_state = z3.simplify(self.now_state)
            if show_log:
                print("Now state: ")
                print(self.now_state)
            return True
    
    def simulate(self, trace, show_log=False):
        self.now_state = self.ts.Init
        if show_log:
            print("Initialize success!: ")
            print(self.now_state)
        for tr_name, *parameters in trace:
            if not self.transfer(tr_name, show_log, parameters):
                if show_log:
                    print("reject")
                return "reject"
        if show_log:
            print("accept")
        return "accept"
        
    def bmc(self, property):
        import lib.bmc
        lib.bmc.index = 0
        self.ts.Tr = z3.BoolVal(False)
        for tr in self.transitions:
            self.ts.Tr = z3.simplify(z3.Or(self.ts.Tr, z3.And(self.transfer_func[tr], self.condition_guards[tr], self.nowOut > self.now)))
        xs = [v[0] for v in self.states.values()]
        xns = [v[1] for v in self.states.values()]
        fvs = []
        for p in self.tr_parameters.values():
            if p != None:
                for v in p:
                    if v not in fvs:
                        fvs.append(v)
        # print(fvs)
        # print(self.ts.Init)
        # print(self.ts.Tr)
        # print(property)
        model = lib.bmc.bmc(self.ts.Init, self.ts.Tr, property, fvs, xs, xns)
        if model != None:
            # print(model)
            rd = extract_model(model,'func')
            # print(rd)
            trace = []
            for i in range(1, len(rd)-2):
                # print(rd[i])
                tr = rd[i]['func'].__str__()[1:-1]
                rule = [tr, self.nowOut == rd[i]['now']]
                # print(tr)
                if self.tr_parameters[tr] != None:
                    for j in self.tr_parameters[tr]:
                        if j.__str__() in rd[i].keys():
                            rule.append(j == rd[i][j.__str__()])
                        else:
                            # print("Error: parameter not found!", i, j.__str__())
                            rule.append(j == rd[i-1][j.__str__()])
                trace.append(tuple(rule))
            return trace
        else:
            # print("No model found!")
            return None
    def synthesize_one_guard(self, possible_guards, negative_trace, positive_traces):
        old_guard = self.condition_guards.copy()
        self.clear_guards()
        result_guard = []
        for tr in self.transitions:
            for g in possible_guards:
                self.add_guard(tr, g)
                # print(tr, g)
                # print(statemachine.condition_guards)
                if self.simulate(negative_trace, show_log=False) == 'reject':
                    all_accept = True
                    for ptrace in positive_traces:
                        if self.simulate(ptrace, show_log=False) == 'reject':
                            all_accept = False
                            break
                    if all_accept:
                        result_guard.append([tr, g])
                self.clear_guards()
        self.condition_guards = old_guard
        # print('1', self.condition_guards)
        return result_guard
    
def synthesize(self, properties, possible_guards, positive_traces):
    while iter < 100:
        print("iter", iter)
        iter += 1
        ntraces = []
        for r in properties:
            ntrace = self.bmc(z3.Not(r))
            if ntrace == None:
                print("property", r, "verified")
                continue
            else:
                print("property", r, "not verified")
                print("find counter example:")
                print(ntrace)
                ntraces.append(ntrace)
        for ntrace in ntraces:
            result_guard = self.synthesize_one_guard(possible_guards, ntrace, positive_traces)
            tr, g = result_guard[0]
            print("synthesized guard:")
            print(result_guard)
            self.add_guard(tr, g)
            print()