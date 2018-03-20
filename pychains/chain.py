import os.path
import string
import enum
import sys

import taintedstr as tainted
from taintedstr import Op, tstr
from . import config

import random
random.seed(config.RandomSeed)

All_Characters = list(string.printable)

CmpSet = [Op.EQ, Op.NE, Op.IN, Op.NOT_IN]

def log(var, i=1):
    if config.Debug >= i: print(repr(var), file=sys.stderr, flush=True)

def o(d='', var=None, i=1):
    if config.Debug >= i:
        print(d, repr(var) if var else '', file=sys.stdout, flush=True)

import pudb
brk = pudb.set_trace

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

Seen_Prefixes = set()

class Prefix:
    def __init__(self, myarg):
        self.my_arg = tainted.tstr(str(myarg))

    def __repr__(self):
        return repr(self.my_arg)

    def solve(self, my_traces, i):
        raise NotImplemnted

    def create_prefix(self, myarg):
        # should be overridden in child classes
        raise NotImplemnted

    def continue_valid(self):
        return []

class DFPrefix(Prefix):

    def continue_valid(self):
        if  random.uniform(0,1) > config.Return_Probability:
            return [self.create_prefix(str(self.my_arg) +
                random.choice(All_Characters))]

    def create_prefix(self, myarg):
        return DFPrefix(myarg)

    def parsing_state(self, h, arg_prefix):
        if h.op_A.x() == len(arg_prefix): return EState.Append
        elif len(h.op_A) == 1: return EState.Trim
        else: return EState.Unknown

    def comparisons_on_given_char(self, h, cmp_traces):
        return [(i,t) for i,t in enumerate(cmp_traces)
                if h.op_A.x() == t.op_A.x()]

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

    def solve(self, my_traces, i):
        traces = list(reversed(my_traces))
        arg_prefix = self.my_arg
        # add the prefix to seen.
        Seen_Prefixes.add(str(arg_prefix))
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        while traces:
            h, *ltrace = traces
            k = self.parsing_state(h, arg_prefix)
            log((config.RandomSeed, i, k, "is tainted", isinstance(h.op_A, tainted.tstr)), 1)
            sprefix = str(arg_prefix)

            if k == EState.Trim:
                end =  h.op_A.x()
                similar = [i for i in Seen_Prefixes
                        if str(arg_prefix[:end]) in i and
                           len(i) > len(arg_prefix[:end])]
                fixes = [i[end] for i in similar]

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
                chars = sum(corr, [])
                chars = chars if config.WeightedGeneration else sorted(set(chars))
                new_prefix = sprefix[:-1]
                sols = [self.create_prefix("%s%s" % (new_prefix, new_char))
                        for new_char in chars]
                return sols

            elif k == EState.Append:
                # An empty comparison at the EOF
                sols = [self.create_prefix("%s%s" % (sprefix, new_char))
                        for new_char in All_Characters]

                return sols
            else:
                assert k == EState.Unknown
                # Unknown what exactly happened. Strip the last and try again
                # try again.
                traces = ltrace
                continue

        return []

class BFPrefix(DFPrefix):

    def create_prefix(self, myarg):
        return BFPrefix(myarg)

    def solve(self, my_traces, i):
        # Fast predictive solutions. Use only known characters to fill in when
        # possible.
        traces = list(reversed(my_traces))
        arg_prefix = self.my_arg
        Seen_Prefixes.add(str(arg_prefix))
        sols = []
        while traces:
            h, *ltrace = traces
            k = self.parsing_state(h, arg_prefix)
            log((config.RandomSeed, i, k, "is tainted",
                isinstance(h.op_A, tainted.tstr)), 1)
            sprefix = str(arg_prefix)
            end =  h.op_A.x()
            similar = [i for i in Seen_Prefixes if str(arg_prefix[:end]) in i
                       and len(i) > len(arg_prefix[:end])]
            fixes = [i[end] for i in similar]

            cmp_stack = self.comparisons_on_given_char(h, traces)
            opBs = [[t.opB] if t.op in [Op.EQ, Op.NE] else t.opB
                    for i, t in cmp_stack]
            corr = [i for i in sum(opBs, []) if i and i not in fixes]

            if k == EState.Trim:
                if not corr:
                    return sols
            elif k == EState.Append:
                if not corr:
                    # last resort. Use random fill in
                    sols.append(self.create_prefix("%s%s" %
                        (sprefix,random.choice(All_Characters))))
                    traces = [i for i in traces if len(i.opA) == 1]
                    continue

            chars = corr if config.WeightedGeneration else sorted(set(corr))
            new_prefix = sprefix[:end]
            for new_char in chars:
                sols.append(self.create_prefix("%s%s" % (new_prefix, new_char)))
            return sols

        return []

class Chain:

    def __init__(self):
        self.initiate_bfs = False
        self._my_args = []
        self.seen = set()

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
        return solutions if self.initiate_bfs else [random.choice(solutions)]

    def exec_argument(self, fn):
        self.start_i = 0
        # replace interesting things
        solution_stack = [DFPrefix(config.MyPrefix if config.MyPrefix
            else random.choice(All_Characters))]

        for i in range(self.start_i, config.MaxIter):
            my_prefix, *solution_stack = solution_stack
            self.apply_prefix(my_prefix)
            self.start_i = i
            tainted.Comparisons = []
            try:
                log(">> %s" % self.sys_args(), 1)
                v = fn(self.sys_args())
                self.log_comparisons()
                o('Arg:', self.sys_args(), 0)
                solution_stack = my_prefix.continue_valid()
                if not solution_stack:
                    return v
            except Exception as e:
                self.seen.add(repr(self.current_prefix.my_arg))
                log('Exception %s' % e)
                if i == config.MaxIter//100 and config.InitiateBFS:
                    print('BFS: %s' % repr(self.current_prefix.my_arg), flush=True)
                    self.arg_at_bfs = self.current_prefix.my_arg
                    self.current_prefix = BFPrefix(str(self.current_prefix.my_arg))
                    self.initiate_bfs = True
                self.traces = tainted.Comparisons
                solution_stack.extend(self.current_prefix.solve(self.traces, i))

                # prune works on the complete stack
                solution_stack = self.prune(solution_stack)

                if not solution_stack:
                    if not self.initiate_bfs:
                        # remove one character and try again.
                        new_arg = self.sys_args()[:-1]
                        if not new_arg:
                            raise Exception('DFS: No suitable continuation found')
                        solution_stack = [self.current_prefix.create_prefix(new_arg)]
                    else:
                        raise Exception('BFS: No suitable continuation found')
