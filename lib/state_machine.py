from lib.ts import Ts
import z3

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

    def add_state(self, state_name, type):
        state, stateOut = self.ts.add_var(type, name = state_name)
        self.states[state_name] = (state, stateOut)
        return state, stateOut

    def add_tr(self, tr_name, parameters, guard, transfer_func):
        self.transitions.append(tr_name)
        self.tr_parameters[tr_name] = parameters
        self.condition_guards[tr_name] = guard
        self.transfer_func[tr_name] = transfer_func

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
        self.ts.Init = init_state

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
                print("reject")
                return
        print("accept")
        
    def synthesis_guard(self, operator, negative_traces):
        #generate predicate of states to guard
        pass