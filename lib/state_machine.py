from lib.bmc import extract_model
from lib.ts import Ts
import z3
import itertools
import time

def contains(x, e):
    return x.__repr__() == e.__repr__() or any([contains(x, c) for c in e.children()])


class smart_contract_state_machine:
    def __init__(self, name):
        self.name = name
        self.states = {}
        self.prev_states = {}
        self.once = {}
        self.transitions = []
        self.condition_guards = {}
        self.candidate_condition_guards = {}
        self.tr_parameters = {}
        self.transfer_func = {}
        self.constants = []
        self.ts = Ts(name)
        self.now_state = None
        self.now, self.nowOut = self.add_state('now', z3.BitVecSort(256))
        self.func, self.funcOut = self.add_state('func', z3.StringSort())

    def add_state(self, state_name, type):
        state, stateOut = self.ts.add_var(type, name = state_name)
        prev_state, prev_stateOut = self.ts.add_var(type, name = "prev_" + state_name)
        if state_name != 'func' and state_name[:5] != "once_":
            self.states[state_name] = (state, stateOut)
            self.prev_states[state_name] = (prev_state, prev_stateOut)
        return state, stateOut

    def prev(self, state):
        return self.prev_states[state.__str__()]

    def add_tr(self, tr_name, parameters, guard, transfer_func):
        self.transitions.append(tr_name)
        self.once[tr_name] = self.add_state("once_"+tr_name, z3.BoolSort())
        self.tr_parameters[tr_name] = parameters
        self.condition_guards[tr_name] = guard
        self.candidate_condition_guards[tr_name] = []
        transfer_func = z3.And(transfer_func, self.funcOut == tr_name, self.once[tr_name][1] == True)
        for state in self.states:
            if state == 'now' or state == 'func':
                continue
            transfer_func = z3.simplify(z3.And(transfer_func, self.prev(self.states[state][0])[1] == self.states[state][0]))
            if not contains(self.states[state][1], transfer_func):
                transfer_func = z3.simplify(z3.And(transfer_func, self.states[state][1] == self.states[state][0]))
        # print(transfer_func)
        self.transfer_func[tr_name] = transfer_func

    def add_once(self):
        for tr in self.transitions:
            for once in self.once:
                if once != tr:
                    # print(once, self.once[once][0])
                    self.transfer_func[tr] = z3.And(self.transfer_func[tr], self.once[once][1] == self.once[once][0])

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
        for once in self.once.values():
            self.ts.Init = z3.simplify(z3.And(self.ts.Init, once[0] == False))

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
        xs = [v[0] for v in self.states.values()] + [v[0] for v in self.prev_states.values()] + [v[0] for v in self.once.values()] + [self.func]
        xns = [v[1] for v in self.states.values()] + [v[1] for v in self.prev_states.values()] + [v[1] for v in self.once.values()] + [self.funcOut]
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
        

    def generate_candidate_guards(self, predicates, positive_traces, drop_unreasonable = True):
        candidate_guards = []
        for state_lvalue in self.states.values():
            statel = state_lvalue[0]
            if statel.__str__() =='state':
                continue
            for state_rvalue in self.states.values():
                stater = state_rvalue[0]
                if statel.__str__() == stater.__str__() or statel.__str__() =='state' or stater.__str__() =='state':
                    continue
                # print(statel, stater)
                for predicate in predicates:
                    try:
                        if predicate == "<":
                            g = statel < stater
                        elif predicate == "<=":
                            g = statel <= stater
                        elif predicate == ">":
                            g = statel > stater
                        elif predicate == ">=":
                            g = statel >= stater
                        elif predicate == "=":
                            g = statel == stater
                        else:
                            print("predicate not supportted")
                    except:
                        continue
                    candidate_guards.append(g)
            
            for constantr in self.constants:
                for predicate in predicates:
                    try:
                        if predicate == "<":
                            g = statel < constantr
                        elif predicate == "<=":
                            g = statel <= constantr
                        elif predicate == ">":
                            g = statel > constantr
                        elif predicate == ">=":
                            g = statel >= constantr
                        elif predicate == "=":
                            g = statel == constantr
                        else:
                            print("predicate not supportted")
                    except:
                        continue
                    candidate_guards.append(g)
        candidate_guards.append(self.states['state'][0]==0)
        candidate_guards.append(self.states['state'][0]==1)
        candidate_guards.append(self.states['state'][0]==2)
        self.clear_guards()
        for tr in self.candidate_condition_guards:
            self.candidate_condition_guards[tr] = []
        for tr in self.transitions:
            for candidates in candidate_guards:
                if not drop_unreasonable:
                    self.candidate_condition_guards[tr].append(candidates)
                else:
                    can_pass = False
                    self.add_guard(tr, candidates)
                    for trace in positive_traces:
                        if self.simulate(trace, show_log=False) == 'accept':
                            can_pass = True
                            break
                    self.clear_guards()
                    if can_pass:
                        self.candidate_condition_guards[tr].append(candidates)
        print(self.candidate_condition_guards)
    
    def synthesize_one_guard(self, negative_trace, positive_traces):
        self.clear_guards()
        result_guard = []
        for tr in self.transitions:
            for g in self.candidate_condition_guards[tr]:
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
        return result_guard
    
    def synthesize(self, properties, positive_traces, simulate_before_bmc = True):
        possible_guards = [[]]
        iter = 0
        sum_verify_time = 0
        sum_synthesize_time = 0
        while iter < 100:
            print("iter", iter)
            iter += 1
            best_guard = None
            max_verified_num = -1
            negative_traces = None
            print("verifying......")
            T1 = time.time()
            all_ntraces = []
            for guards in possible_guards:
                self.clear_guards()
                for g in guards:
                    self.add_guard(g[0], g[1])
                if simulate_before_bmc:
                    reject_all_ntraces = True
                    if all_ntraces != []:
                        for ntrace in all_ntraces:
                            if self.simulate(ntrace, show_log=False) == 'accept':
                                reject_all_ntraces = False
                                break
                    if not reject_all_ntraces:
                        continue
                ntraces = []
                verifiedpnum = 0
                print("|",end='')
                for r in properties:
                    ntrace = self.bmc(z3.Not(r))
                    if ntrace == None:
                        print("√",end='')
                        verifiedpnum += 1
                        continue
                    else:
                        print("×",end='')
                        ntraces.append(ntrace)
                        if simulate_before_bmc:
                            all_ntraces.append(ntrace)
                if verifiedpnum == len(properties):
                    print("|")
                    print("all properties verified!")
                    print("average verify time:%ss" % (sum_verify_time/iter))
                    print("average synthesize time:%ss" % (sum_synthesize_time/(iter-1)))
                    return guards
                if verifiedpnum > max_verified_num:
                    max_verified_num = verifiedpnum
                    best_guard = guards
                    negative_traces = ntraces
            print("|")
            print("best guard:", end="")
            print(best_guard)
            print("negative_traces:", end="")
            print(negative_traces)
            T2 = time.time()
            sum_verify_time += T2 - T1
            print("synthsizing......")
            result_guards = []
            num = 0
            for ntrace in negative_traces:
                result_guard = self.synthesize_one_guard(ntrace, positive_traces)
                result_guards.append(result_guard)
            result_guards_cartesian = list(itertools.product(*result_guards))
            print("synthesized guard:")
            print(result_guards_cartesian)
            possible_guards = []
            for guards in result_guards_cartesian:
                possible_guards.append(best_guard + list(guards))
            T3 = time.time()
            sum_synthesize_time += T3 - T2
            print("----------------------------------------------")
