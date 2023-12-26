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
        guard = z3.simplify(z3.And(guard, self.nowOut > self.now))
        self.condition_guards[tr_name] = guard
        transfer_func = z3.And(transfer_func, self.funcOut == tr_name)
        print(transfer_func)
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
        if parameters == None:
            success = z3.And(self.now_state, self.condition_guards[tr_name])
            s = z3.Solver()
            s.add(success)
            result = s.check()
            if result == z3.unsat:
                if show_log:
                    print("Transfer failed: ", tr_name, " with no parameters")
                return False
            else:
                if show_log:
                    print("Transfer success: ", tr_name, " with no parameters")
                s = z3.Solver()
                s.add(z3.And(self.now_state, self.transfer_func[tr_name]))
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
        else:
            success = z3.And(self.now_state, self.condition_guards[tr_name], z3.And(*parameters))
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
        self.ts.Tr = z3.BoolVal(False)
        for tr in self.transitions:
            self.ts.Tr = z3.simplify(z3.Or(self.ts.Tr, z3.And(self.transfer_func[tr],self.condition_guards[tr])))
        xs = [v[0] for v in self.states.values()]
        xns = [v[1] for v in self.states.values()]
        fvs = []
        for p in self.tr_parameters.values():
            if p != None:
                for v in p:
                    if v not in fvs:
                        fvs.append(v)
        print(fvs)
        print(self.ts.Init)
        print(self.ts.Tr)
        print(property)
        model = lib.bmc.bmc(self.ts.Init, self.ts.Tr, property, fvs, xs, xns)
        if model != None:
            extract_model(model,'func')
        else:
            print("No model found!")
    # def synthesis_guard(self, operator, negative_trace, positive_traces):
    #     #generate predicate of states to guard
    #     pass