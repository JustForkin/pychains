import os.path
import string
import enum
import sys

import taintedstr as tainted
from taintedstr import Op, tstr
from . import config

import random
random.seed(config.RandomSeed)

All_Characters = list(string.ascii_letters + string.digits + string.punctuation) \
        if config.No_CTRL else list(string.printable)

CmpSet = [Op.EQ, Op.NE, Op.IN, Op.NOT_IN]

def log(var, i=1):
    if config.Debug >= i: print(repr(var), file=sys.stderr, flush=True)

def o(d='', var=None, i=1):
    if config.Debug >= i:
        print(d, repr(var) if var else '', file=sys.stdout, flush=True)

import pudb
brk = pudb.set_trace

class QState:
    def __init__(self, key):
        self.key = key
        self._policy = QPolicy()

    @staticmethod
    def get_key(chars):
        my_chars = []
        for c in chars:
            if c in string.ascii_letters:
                if my_chars and my_chars[-1] == 'a':
                    continue
                else:
                    my_chars.append('a')
            elif c in string.digits:
                if my_chars and my_chars[-1] == '1':
                    continue
                else:
                    my_chars.append('1')
            elif c in string.whitespace:
                if my_chars and my_chars[-1] == ' ':
                    continue
                else:
                    my_chars.append(' ')
            else:
                my_chars.append(c)
        return ''.join(my_chars)


class Reward:
    MidWay = -1
    StackDrop = 1
    EndPoint = 500
    Timedout = -500


# our particular state representation.
class Q:
    def __init__(self):
        self.chars, self._q = All_Characters, {}

    def __getitem__(self, val):
        key = self.to_key(val)
        if key not in self._q: self._q[key] = 0
        return self._q[key]

    def __setitem__(self, val, value):
        self._q[self.to_key(val)] = value

    def to_key(self, val):
        return str(val)

    def max_a(self):
        # best next char for this state.
        c = self.chars[0]
        maxq = self[c]
        for char in self.chars:
           q = self[char]
           if q > maxq:
               maxq, c = q, char
        return c


Alpha = 0.1 # Learning rate
Beta = 1    # Discounting factor

class QPolicy:
    def __init__(self):
        self._q, self._time_step = Q(), 0

    def q(self):
        return self._q

    def next_char(self):
        s = random.randint(0, self._time_step)
        self._time_step += 1
        if s == 0:
            return None
        else:
            return self._q.max_a()

    def max_a_val(self):
        a_char = self._q.max_a()
        return self._q[a_char]

    def update(self, a_char, last_max_q, reward):
        # Q(a,s)  = (1-alpha)*Q(a,s) + alpha(R(s) + beta*max_a(Q(a_,s_)))
        q_now = self._q[a_char]
        q_new = (1 - Alpha) * q_now + Alpha*(reward + Beta*last_max_q)
        self._q[a_char] = q_new



# TODO: Any kind of preprocessing -- space strip etc. distorts the processing.

def create_arg(s):
    return tainted.tstr(s)

class EState(enum.Enum):
    # A char comparison made using a previous character
    Trim = enum.auto()
    # End of string as found using tainting or a comparison with the
    # empty string
    Append = enum.auto()
    # -
    Unknown = enum.auto()

    # Python Specific
    Char = enum.auto()

    # A string token comparison
    String = enum.auto()

    # End of string as found using tainting or a comparison with the
    # empty string
    EOF = enum.auto()

class Prefix:
    def __init__(self, myarg):
        self.my_arg = tainted.tstr(str(myarg))

    def __repr__(self):
        return repr(self.my_arg)

    def solve(self, my_traces, i, seen):
        raise NotImplemnted

    def create_prefix(self, myarg):
        # should be overridden in child classes
        raise NotImplemnted

    def continue_valid(self):
        return []

class Search(Prefix):

    def continue_valid(self):
        if  random.uniform(0,1) > config.Return_Probability:
            return [self.create_prefix(str(self.my_arg) +
                random.choice(All_Characters))]

    def parsing_state(self, h, arg_prefix):
        if h.op_A.x() == len(arg_prefix): return EState.Append
        elif len(h.op_A) == 1 and h.op_A.x() == arg_prefix[-1].x(): return EState.Trim
        elif len(h.op_A) == 0: return EState.Trim
        else: return EState.Unknown

    def predicate_compare(self, t1, tx):
        if t1.op in [Op.IN, Op.NOT_IN]:
            x = t1.op_A in t1.op_B
            y = tx.op_A in tx.op_B
            return x == y and t1.op_B == tx.op_B
        elif t1.op in [Op.EQ, Op.NE]:
            x = t1.op_A == t1.op_B
            y = tx.op_A == tx.op_B
            return x == y and t1.op_B == tx.op_B
        assert False

    def comparisons_at(self, x, cmp_traces):
        return [(i,t) for i,t in enumerate(cmp_traces) if x == t.op_A.x()]

    def comparisons_on_given_char(self, h, cmp_traces):
        return self.comparisons_at(h.op_A.x(), cmp_traces)

    def get_previous_fixes(self, h, sprefix, seen):
        end = h.op_A.x()
        similar = [i for i in seen if sprefix[:end] in i and
                   len(i) > len(sprefix[:end])]
        return [i[end] for i in similar]

    def get_comparison_len(self, traces):
        # how many of the last characters added had same comparisons?
        arg_prefix = self.my_arg
        sols = []
        while traces:
            h, *ltrace = traces
            k = self.parsing_state(h, arg_prefix)
            if k == EState.Append or EState.EOF:
                cmp0 = self.comparisons_at(arg_prefix[-1].x(), traces)
                end = h.op_A.x()-2
                for i in range(end, 0, -1):
                    cmpi = self.comparisons_at(arg_prefix[i].x(), traces)
                    if len(cmp0) != len(cmpi): return end - i
                    for (_,p1), (_,p2) in zip(cmp0, cmpi):
                        if not self.predicate_compare(p1, p2):
                            return end - i
                return end
            elif k == EState.Trim:
                return 1
            elif k == EState.Unknown:
                traces = ltrace
                continue
            else:
                assert False
        return -1


class DeepSearch(Search):

    def create_prefix(self, myarg): return DeepSearch(myarg)

    def extract_solutions(self, elt, lst_solutions, flip=False):
        fn = tainted.COMPARE_OPERATORS[elt.op]
        result = fn(str(elt.op_A), str(elt.op_B))
        if isinstance(elt.op_B, str) and len(elt.op_B) == 0:
            assert Op(elt.op) in [Op.EQ, Op.NE]
            return lst_solutions
        else:
            myfn = fn if not flip else lambda a, b: not fn(a, b)
            fres = lambda x: x if result else not x
            return [c for c in lst_solutions
                    if fres(myfn(str(c), str(elt.op_B)))]

    def get_lst_solutions_at_divergence(self, cmp_stack, v):
        # if we dont get a solution by inverting the last comparison, go one
        # step back and try inverting it again.
        stack_size = len(cmp_stack)
        while v < stack_size:
            # now, we need to skip everything till v
            diverge, *satisfy = cmp_stack[v:]
            lst_solutions = All_Characters
            for i,elt in reversed(satisfy):
                lst_solutions = self.extract_solutions(elt, lst_solutions, False)
            # now we need to diverge here
            i, elt = diverge
            lst_solutions = self.extract_solutions(elt, lst_solutions, True)
            if lst_solutions:
                return lst_solutions
            v += 1
        return []

    def get_corrections(self, cmp_stack, constraints):
        """
        cmp_stack contains a set of comparions, with the last comparison made
        at the top of the stack, and first at the bottom. Choose a point
        somewhere and generate a character that conforms to everything until
        then.
        """
        if not cmp_stack or config.Dumb_Search:
            return [[l] for l in All_Characters if constraints(l)]

        stack_size = len(cmp_stack)
        lst_positions = list(range(stack_size-1,-1,-1))
        solutions = []

        for point_of_divergence in lst_positions:
            lst_solutions = self.get_lst_solutions_at_divergence(cmp_stack,
                    point_of_divergence)
            lst = [l for l in lst_solutions if constraints(l)]
            if lst:
                solutions.append(lst)
        return solutions

    def solve(self, traces, i, seen):
        arg_prefix = self.my_arg
        sprefix = str(arg_prefix)
        append = False
        # add the prefix to seen.
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        while traces:
            append = False
            h, *ltrace = traces
            k = self.parsing_state(h, arg_prefix)
            log((config.RandomSeed, i, k, "is tainted", isinstance(h.op_A, tainted.tstr)), 1)
            end =  h.op_A.x()
            new_prefix = sprefix[:end]
            fixes = self.get_previous_fixes(h, sprefix, seen)

            if k == EState.Trim:
                # A character comparison of the *last* char.
                # This was a character comparison. So collect all
                # comparisons made using this character. until the
                # first comparison that was made otherwise.
                # Now, try to fix the last failure
                cmp_stack = self.comparisons_on_given_char(h, traces)
                # Now, try to fix the last failure
                corr = self.get_corrections(cmp_stack, lambda i: i not in fixes)
                if not corr: raise Exception('Exhausted attempts: %s' % fixes)
                # check for line cov here.
                chars = sorted(set(sum(corr, [])))

            elif k == EState.Append:
                assert new_prefix == sprefix
                #assert len(fixes) == 0
                # An empty comparison at the EOF
                chars = All_Characters
                append = True
            else:
                assert k == EState.Unknown
                # Unknown what exactly happened. Strip the last and try again
                # try again.
                traces = ltrace
                continue

            return append, [self.create_prefix("%s%s" % (new_prefix, new_char))
                    for new_char in chars]

        return append, []

class Chain:

    def __init__(self):
        self.initiate_bfs = False
        self._my_args = []
        self.seen = set()
        self.states = {}

    def add_sys_args(self, var):
        if type(var) is not tainted.tstr:
            var = create_arg(var)
        else:
            var = create_arg(str(var))
        self._my_args.append(var)

    def sys_args(self):
        return self._my_args[-1]

    def apply_prefix(self, prefix):
        self.current_prefix = prefix
        self.add_sys_args(prefix.my_arg)

    def log_comparisons(self):
        if config.Log_Comparisons:
            for c in tainted.Comparisons: print("%d,%s" % (c.op_A.x(), repr(c)))

    def prune(self, solutions):
        # never retry an argument.
        solutions = [s for s in solutions if repr(s.my_arg) not in self.seen]
        if self.initiate_bfs:
            if hasattr(self.current_prefix, 'first'):
                return  solutions
            else:
                return  solutions
                # return  [s for s in solutions if not s.comparison_chain_equal(self.traces)]
        else:
            return [random.choice(solutions)]

    # entry
    def exec_argument(self, fn):
        self.start_i = 0
        # replace interesting things
        arg = config.MyPrefix if config.MyPrefix else random.choice(All_Characters)
        solution_stack = [DeepSearch(arg)]
        skey = QState.get_key(arg)
        self.states[skey] = QState(skey)
        last_state = None

        for i in range(self.start_i, config.MaxIter):
            my_prefix, *solution_stack = solution_stack
            self.apply_prefix(my_prefix)
            skey = QState.get_key(self.sys_args())
            if skey not in self.states:
                self.states[skey] = QState(skey)
            last_state = state
            state = self.states[skey]
            char = self.sys_args()[-1]
            last_state.next_state[char] = state
            state.prev_state[char] = last_state

            self.start_i = i
            tainted.Comparisons = []
            try:
                log(">> %s -- %s" % (self.sys_args(), state.key), 1)
                v = fn(self.sys_args())
                self.log_comparisons()
                solution_stack = my_prefix.continue_valid()
                if not solution_stack:
                    return (self.sys_args(), v)
            except Exception as e:
                self.seen.add(str(self.current_prefix.my_arg))
                log('Program Exception %s' % e)
                self.traces = list(reversed(tainted.Comparisons))
                sim_len = self.current_prefix.get_comparison_len(self.traces)
                self.current_prefix.sim_length = sim_len
                c = state._policy.next_char()
                if c:
                    new_solutions = [self.sys_args() + c]
                else:
                    append, new_solutions = self.current_prefix.solve(self.traces, i, self.seen)
                    if append:
                        # reward for current state.
                        last_max_q = 0 # TODO
                        reward = 0 # TODO
                        state.policy.update(self.sys_args()[-1], last_max_q, reward)
                my_len = float('Inf')
                choice = self.prune(new_solutions)
                for i in choice + solution_stack:
                    sim_len = i.sim_length if hasattr(i, 'sim_length') else float('Inf')
                    if sim_len < my_len:
                        my_len = sim_len
                        choice = [i]
                solution_stack = choice

                if not solution_stack:
                    if not self.initiate_bfs:
                        # remove one character and try again.
                        new_arg = self.sys_args()[:-1]
                        if not new_arg:
                            raise Exception('DFS: No suitable continuation found')
                        solution_stack = [self.current_prefix.create_prefix(new_arg)]
                    else:
                        raise Exception('BFS: No suitable continuation found')
