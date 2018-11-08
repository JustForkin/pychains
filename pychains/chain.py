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
        # add the prefix to seen.
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        while traces:
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
            else:
                assert k == EState.Unknown
                # Unknown what exactly happened. Strip the last and try again
                # try again.
                traces = ltrace
                continue

            return [self.create_prefix("%s%s" % (new_prefix, new_char))
                    for new_char in chars]

        return []

class PythonSpecificDeepSearch(DeepSearch):

    def create_prefix(self, myarg): return PythonSpecificDeepSearch(myarg)

    def best_matching_str(self, elt, lst):
        largest, lelt = '', None
        for e in lst:
            common = os.path.commonprefix([elt, e])
            if len(common) > len(largest):
                largest, lelt = common, e
        return largest, lelt

    def parsing_state(self, h, arg_prefix):
        last_char_added = arg_prefix[-1]
        o = h.op

        if o in [Op.EQ, Op.NE] and isinstance(h.op_B, str) and len(h.op_B) > 1 and h.op_A.x() == last_char_added.x():
            # Dont add IN and NOT_IN -- '0' in '0123456789' is a common
            # technique in char comparision to check for digits
            # A string comparison rather than a character comparison.
            return (1, EState.String, h)

        elif o in CmpSet and isinstance(h.op_B, list) and max([len(opB) in h.op_B]) > 1 and h.op_A.x() == last_char_added.x():
            # A string comparison rather than a character comparison.
            return (1, EState.String, h)

        elif h.op_A.x() == last_char_added.x():
            # A character comparison of the *last* char.
            return (1, EState.Char, h)

        elif h.op_A.x() == len(arg_prefix):
            # An empty comparison at the EOF
            return (1, EState.EOF, h)

        elif len(h.op_A) == 1 and h.op_A.x() != last_char_added.x():
            # An early validation, where the comparison goes back to
            # one of the early chars. Imagine when we use regex /[.0-9+-]/
            # for int, and finally validate it with int(mystr)
            return (1, EState.Trim, h)

        else:
            return (-1, EState.Unknown, (h, last_char_added))


    def solve(self, traces, i, seen):
        arg_prefix = self.my_arg
        # add the prefix to seen.
        sprefix = str(arg_prefix)
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        last_char_added = arg_prefix[-1]


        while traces:
            h, *ltrace = traces
            o = h.op

            idx, k, info = self.parsing_state(h, arg_prefix)
            log((config.RandomSeed, i, idx, k, info, "is tainted", isinstance(h.op_A, tainted.tstr)), 1)

            if k == EState.Char:
                # A character comparison of the *last* char.
                # This was a character comparison. So collect all
                # comparisons made using this character. until the
                # first comparison that was made otherwise.
                # Now, try to fix the last failure
                fixes = self.get_previous_fixes(h, sprefix, seen)
                cmp_stack = self.comparisons_on_given_char(h, traces)
                if str(h.op_A) == last_char_added and o in CmpSet:
                    # Now, try to fix the last failure
                    corr = self.get_corrections(cmp_stack, lambda i: i not in fixes)
                    if not corr: raise Exception('Exhausted attempts: %s' % fixes)
                else:
                    corr = self.get_corrections(cmp_stack, lambda i: True)
                    fixes = []

                # check for line cov here.
                prefix = sprefix[:-1]
                sols = []
                chars = [new_char for v in corr for new_char in v]
                chars = chars if config.WeightedGeneration else sorted(set(chars))
                for new_char in chars:
                    arg = "%s%s" % (prefix, new_char)
                    sols.append(self.create_prefix(arg))

                return sols
            elif k == EState.Trim:
                # we need to (1) find where h.op_A._idx is within
                # sys_args, and trim sys_args to that location, and
                # add a new character.
                fix =  [sprefix[h.op_A.x()]]
                args = sprefix[:h.op_A.x()] + random.choice([i for i in All_Characters if i != fix[0]])
                # we already know the result for next character
                sols = [self.create_prefix(args)]
                return sols # VERIFY - TODO

            elif k == EState.String:
                if o in [Op.IN, Op.NOT_IN]:
                    opB = self.best_matching_str(str(h.op_A), [str(i) for i in h.op_B])
                elif o in [Op.EQ, Op.NE]:
                    opB = str(h.op_B)
                else:
                    assert False
                common = os.path.commonprefix([str(h.op_A), opB])
                assert str(h.op_B)[len(common)-1] == last_char_added
                arg = "%s%s" % (sprefix, str(h.op_B)[len(common):])
                sols = [self.create_prefix(arg)]
                return sols
            elif k == EState.EOF:
                # An empty comparison at the EOF
                sols = []
                for new_char in All_Characters:
                    arg = "%s%s" % (sprefix, new_char)
                    sols.append(self.create_prefix(arg))

                return sols
            elif k == EState.Unknown:
                # Unknown what exactly happened. Strip the last and try again
                # try again.
                traces = ltrace
                continue
            else:
                assert False

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
        if self.initiate_bfs:
            if hasattr(self.current_prefix, 'first'):
                return  solutions
            else:
                return  solutions
                # return  [s for s in solutions if not s.comparison_chain_equal(self.traces)]
        else:
            return [random.choice(solutions)]

    def exec_argument(self, fn):
        self.start_i = 0
        # replace interesting things
        arg = config.MyPrefix if config.MyPrefix else random.choice(All_Characters)
        if config.Python_Specific:
            solution_stack = [PythonSpecificDeepSearch(arg)]
        else:
            solution_stack = [DeepSearch(arg)]

        for i in range(self.start_i, config.MaxIter):
            my_prefix, *solution_stack = solution_stack
            self.apply_prefix(my_prefix)
            self.start_i = i
            tainted.Comparisons = []
            try:
                log(">> %s" % self.sys_args(), 1)
                v = fn(self.sys_args())
                self.log_comparisons()
                solution_stack = my_prefix.continue_valid()
                if not solution_stack:
                    return (self.sys_args(), v)
            except Exception as e:
                self.seen.add(str(self.current_prefix.my_arg))
                log('Exception %s' % e)
                self.traces = list(reversed(tainted.Comparisons))
                sim_len = self.current_prefix.get_comparison_len(self.traces)
                self.current_prefix.sim_length = sim_len
                new_solutions = self.current_prefix.solve(self.traces, i, self.seen)
                if self.initiate_bfs:
                    solution_stack = solution_stack + self.prune(new_solutions)
                else:
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
