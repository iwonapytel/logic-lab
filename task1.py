from z3 import *
from sys import stdin

class State():
    """
    Boolean representing state after reading k symbols.
    """
    str = "state_{i}_{s}"

    def __init__(self, state, step):
        self.state = state
        self.step = step

    def bool(self):
        return Bool(str(self))

    def __str__(self):
        return State.str.format(i=self.step, s=self.state)

class Symbol():
    """
    Boolean representing k-th symbol in word.
    """
    str = "sym_{i}_{s}"

    def __init__(self, symbol, step):
        self.symbol = symbol
        self.step = step

    def bool(self):
        return Bool(str(self))

    def __str__(self):
        return Symbol.str.format(i=self.step, s=self.symbol)


class SATGenerator():

    def __init__(self, symbols, states, initial_states, final_states,
                 transitions, n):
        self.symbols = symbols
        self.states = states
        self.initial = initial_states
        self.final = final_states
        self.transitions = transitions
        self.n = n

    def trans_formula(self):
        """
        For every transition (p, a, q) in step s makes formulas:
        p_s && a_s => q_(s+1)
        """
        trans_formula = []

        for step in range(n):
            for (p, a, q) in self.transitions:
                prev = State(step, p).bool()
                symbol = Symbol(step, a).bool()
                next = State(step+1, q).bool()
                trans = Implies(And(prev, symbol), next)
                trans_formula.append(trans)
        return And(trans_formula)

    def corectness_formula(self):
        """
        Ensures, that:
        - there is exactly one symbol in every step
        - at least one state in step
        - initial states in step 0 are true
        - final states in step n are false
        """
        symbol_corectness = []
        for step in range(n):
            exclude_symbols = []
            alph_length = len(self.symbols)
            for i in range(alph_length):
                for j in range(i+1, alph_length):
                    s1 = Symbol(step, self.symbols[i]).bool()
                    s2 = Symbol(step, self.symbols[j]).bool()
                    exclude_symbols.append(Not(And(s1, s2)))
            curr_symbols = [Symbol(step, i).bool() for i in self.symbols]
            symbol_corectness.append(And(And(exclude_symbols), Or(curr_symbols)))

        state_corectness = []

        for step in range(n):
            curr_states = [State(step, i).bool() for i in self.states]
            state_corectness.append(Or(curr_states))

        initial_corectness = And([State(0, s).bool() for s in self.initial])
        final_corectness = And([Not(State(self.n, s).bool()) for s in self.final])

        return And(And(symbol_corectness), And(state_corectness), initial_corectness,
                    final_corectness)

    def solve_sat(self):
        trans_fomula = self.trans_formula()
        corectness_formula = self.corectness_formula()
        formula = And(trans_fomula, corectness_formula)

        sat_solver = Solver()
        sat_solver.add(formula)
        sat_model = sat_solver.model() if sat_solver.check() == sat else []
        return sat_model

if __name__ == '__main__':
    k, l, l_i, l_f, m = map(int, stdin.readline().split())
    symbols = stdin.readline().split()
    states = stdin.readline().split()
    initial_states = stdin.readline().split()
    final_states = stdin.readline().split()

    transitions = []
    for i in range(m):
        p, a, q = stdin.readline().split()
        transitions.append((p, a, q))

    n = int(stdin.readline())

    sat_generator = SATGenerator(symbols, states, initial_states, final_states,
                 transitions, n)
    solution = sat_generator.solve_sat()

    if solution == []:
        print("YES")
    else:
        print("NO\n")
        word = []
        for step in range(n):
            for s in symbols:
                sym = Symbol(step, s).bool()
                if solution[sym] == True:
                    word.append(s)
        print(" ".join(word))
