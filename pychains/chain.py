import pickle
import os.path
import string
import enum
import sys

import tainted
from tainted import Op, tstr

RandomSeed = int(os.getenv('R') or '0')
import random
random.seed(RandomSeed)

#  Maximum iterations of fixing exceptions that we try before giving up.
MaxIter = 10000

# When we get a non exception producing input, what should we do? Should
# we return immediately or try to make the input larger?
Return_Probability = 1.0

# The sampling distribution from which the characters are chosen.
Distribution='U'

# We can choose to load the state at some iteration if we had dumped the
# state in prior execution.
Load = 0

# Dump the state (a pickle)
Dump = False

# Where to pickle
Pickled = '.pickle/ExecFile-%s.pickle'

Track = True

InitiateBFS = True

Debug=1

Log_Comparisons = 0

WeightedGeneration=False

All_Characters = list(string.printable + string.whitespace)

CmpSet = [Op.EQ, Op.NE, Op.IN, Op.NOT_IN]

Comparison_Equality_Chain = 3

def log(var, i=1):
    if Debug >= i: print(repr(var), file=sys.stderr, flush=True)

def brk(v=True):
    if not v: return None
    import pudb
    pudb.set_trace()

# TODO: Any kind of preprocessing -- space strip etc. distorts the processing.

def create_arg(s):
    if Track:
        return tainted.tstr(s, idx=0)
    else:
        return s

class EState(enum.Enum):
    # A character comparison using the last character
    Char = enum.auto()

    # A char comparison made using a previous character
    Trim = enum.auto()

    # A string token comparison
    String = enum.auto()

    # End of string as found using tainting or a comparison with the
    # empty string
    EOF = enum.auto()

    # -
    Unknown = enum.auto()

def save_trace(traces, i, file='trace'):
    if not Debug: return None
    with open('.t/%s-%d.txt' % (file,i), 'w+') as f:
        for i in traces: print(i, file=f)

class Prefix:
    def __init__(self, myarg, fixes=[]):
        if type(myarg) is not tainted.tstr:
            self.my_arg = create_arg(myarg)
        else:
            self.my_arg = myarg
        self.fixes = fixes

    def __repr__(self):
        return repr(self.my_arg)

    def solve(self, my_traces, i):
        raise NotImplemnted

    def prune(self, solutions, n):
        raise NotImplemnted

    def create_prefix(self, myarg, fixes=[]):
        # should be overridden in child classes
        raise NotImplemnted

    def continue_valid(self):
        return []

class DFPrefix(Prefix):

    def continue_valid(self):
        if  random.uniform(0,1) > Return_Probability:
            return [self.create_prefix(self.my_arg + random.choice(All_Characters))]

    def prune_similar_parents(self, solutions):
        # say we have two parents with the following last char children
        # '{"abcd' ['x', 'y', 'z']
        # '{"abcf' ['x', 'y', 'z']
        # where the comparison op and opB for 'abcd' and 'abcf' are exactly the
        # same (except for different opA), in such case, we need to preserve
        # only one set of children
        new_sol = []
        seen = set()
        for s in solutions:
            if s.cmp_key in seen: continue
            seen.add(s.cmp_key)
            new_sol.append(s)
        return new_sol


    def prune_repeating_chars(self, solutions, n):
        new_sol = []
        for s in solutions:
            if len(s.my_arg) - n < 2:
                new_sol.append(s)
                continue
            if s.cmp_vals[-1].strip() == 'eq' and s.cmp_vals[-2] == s.cmp_vals[-3]:
                continue
            if s.cmp_vals[-1].strip() != 'eq' and s.cmp_vals[-1] == s.cmp_vals[-2]:
                continue
            new_sol.append(s)
        return new_sol

    def prune(self, solutions0, n):
        if not n:
            return [random.choice(solutions0)]
        solutions1 = self.prune_similar_parents(solutions0)
        solutions2 = self.prune_repeating_chars(solutions1, n)
        return solutions2

    def simple_key(self, myarg, traces):
        v = ["(%s @%d %s)" % (i.o(), i.opA.x(), i.opB) for i in traces]
        cmp_key = ''.join(v) +'<'+ myarg[-1] + '>'
        return cmp_key

    # alternative to simple_key
    def squished_key(self, cmp_vals, myarg):
        new_key = []
        prev = None
        for sv in cmp_vals:
            if sv == prev: continue
            prev = sv
            new_key.append(sv)

        return ' '.join(new_key) + '<' + myarg[-1] + '>'

    def get_cmp_vals(self, myarg, traces):
        res = {}
        for t in traces:
            i = t.opA.x()
            if i not in res: res[i] = []
            res[i].append("%s %s" % (t.o(), t.opB))

        vals = []
        for k in sorted(res.keys()):
            sv = ','.join(res[k])
            vals.append(sv)
        return vals


    def create_prefix(self, myarg, fixes=[]):
        d = DFPrefix(myarg, fixes)
        d.cmp_vals = self.get_cmp_vals(myarg, self.traces)
        d.cmp_key = self.squished_key(d.cmp_vals, myarg)
        return d

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

        if o in [Op.EQ, Op.NE] and isinstance(h.opB, str) and len(h.opB) > 1 and h.opA.x() == last_char_added.x():
            # Dont add IN and NOT_IN -- '0' in '0123456789' is a common
            # technique in char comparision to check for digits
            # A string comparison rather than a character comparison.
            return (1, EState.String, h)

        elif o in CmpSet and isinstance(h.opB, list) and max([len(opB) in h.opB]) > 1 and h.opA.x() == last_char_added.x():
            # A string comparison rather than a character comparison.
            return (1, EState.String, h)

        elif h.opA.x() == last_char_added.x():
            # A character comparison of the *last* char.
            return (1, EState.Char, h)

        elif h.opA.x() == len(arg_prefix):
            # An empty comparison at the EOF
            return (1, EState.EOF, h)

        elif len(h.opA) == 1 and h.opA.x() != last_char_added.x():
            # An early validation, where the comparison goes back to
            # one of the early chars. Imagine when we use regex /[.0-9+-]/
            # for int, and finally validate it with int(mystr)
            return (1, EState.Trim, h)

        else:
            return (-1, EState.Unknown, (h, last_char_added))

    def comparisons_on_last_char(self, h, cmp_traces):
        """
        The question we are answering is simple. What caused the last
        error, and how one may fix the error and continue.
        Fixing the last error is the absolute simplest one can go. However,
        that may not be the best especially if one wants to generate multiple
        strings. For that, we need get all the comparisons made on the last
        character -- let us call it cmp_stack. The correct way to
        generate test cases is to ensure that everything until the point
        we want to diverge is satisfied, but ignore the remaining. That is,
        choose a point i arbitrarily from cmp_stack, and get
        lst = cmp_stack[i:] (remember cmp_stack is reversed)
        and satisfy all in lst.
        """
        cmp_stack = []
        check = False
        for i, t in enumerate(cmp_traces):
            if not len(t.opA) == 1: continue
            if h.opA.x() != t.opA.x(): break
            cmp_stack.append((i, t))
        return cmp_stack

    def extract_solutions(self, elt, lst_solutions, flip=False):
        fn = tainted.COMPARE_OPERATORS[elt.op]
        result = fn(str(elt.opA), str(elt.opB))
        if isinstance(elt.opB, str) and len(elt.opB) == 0:
            if Op(elt.op) in [Op.EQ, Op.NE]:
                return lst_solutions
            else:
                assert False
        else:
            myfn = fn if not flip else lambda a, b: not fn(a, b)
            if result:
                lst = [c for c in lst_solutions if myfn(str(c), str(elt.opB))]
            else:
                lst = [c for c in lst_solutions if not myfn(str(c), str(elt.opB))]
            return lst

    def get_lst_solutions_at_divergence(self, cmp_stack, v):
        # if we dont get a solution by inverting the last comparison, go one
        # step back and try inverting it again.
        stack_size = len(cmp_stack)
        while v < stack_size:
            # now, we need to skip everything till v
            diverge, *satisfy = cmp_stack[v:]
            lst_solutions = All_Characters
            for i,elt in reversed(satisfy):
                # assert elt.opA == self.last_char_added()
                lst_solutions = self.extract_solutions(elt, lst_solutions, False)
            # now we need to diverge here
            i, elt = diverge
            # assert elt.opA == self.last_char_added()
            lst_solutions = self.extract_solutions(elt, lst_solutions, True)
            if lst_solutions:
                return lst_solutions
            v += 1
        return []

    def get_corrections(self, cmp_stack, constraints):
        """
        cmp_stack contains a set of comparions, with the last comparison made
        at the top of the stack, and first at the bottom. Choose a point
        somewhere and generate a character that conforms to everything until then.
        """
        stack_size = len(cmp_stack)
        lst_positions = list(range(stack_size-1,-1,-1))
        solutions = []

        for point_of_divergence in lst_positions:
            lst_solutions = self.get_lst_solutions_at_divergence(cmp_stack, point_of_divergence)
            lst = [l for l in lst_solutions if constraints(l)]
            if lst:
                solutions.append(lst)
        return solutions

    def solve(self, my_traces, i):
        traces = list(reversed(my_traces))
        arg_prefix = self.my_arg
        fixes = self.fixes
        last_char_added = arg_prefix[-1]
        self.traces = traces
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        while traces:
            h, *ltrace = traces
            o = h.op

            idx, k, info = self.parsing_state(h, arg_prefix)
            log((RandomSeed, i, idx, k, info, "is tainted", isinstance(h.opA, tainted.tstr)), 1)

            if k == EState.Char:
                # A character comparison of the *last* char.
                # This was a character comparison. So collect all
                # comparisons made using this character. until the
                # first comparison that was made otherwise.
                # Now, try to fix the last failure
                cmp_stack = self.comparisons_on_last_char(h, traces)
                if str(h.opA) == last_char_added and o in CmpSet:
                    # Now, try to fix the last failure
                    corr = self.get_corrections(cmp_stack, lambda i: i not in fixes)
                    if not corr: raise Exception('Exhausted attempts: %s' % fixes)
                else:
                    corr = self.get_corrections(cmp_stack, lambda i: True)
                    fixes = []

                # check for line cov here.
                prefix = arg_prefix[:-1]
                sols = []
                chars = [new_char for v in corr for new_char in v]
                chars = chars if WeightedGeneration else sorted(set(chars))
                for new_char in chars:
                    arg = "%s%s" % (prefix, new_char)
                    sols.append(self.create_prefix(arg, fixes))

                return sols
            elif k == EState.Trim:
                # we need to (1) find where h.opA._idx is within
                # sys_args, and trim sys_args to that location, and
                # add a new character.
                args = arg_prefix[:h.opA.x()] + random.choice(All_Characters)
                # we already know the result for next character
                fix =  [arg_prefix[h.opA.x()]]
                sols = [self.create_prefix(args, fix)]
                return sols # VERIFY - TODO

            elif k == EState.String:
                if o in [Op.IN, Op.NOT_IN]:
                    opB = self.best_matching_str(str(h.opA), [str(i) for i in h.opB])
                elif o in [Op.EQ, Op.NE]:
                    opB = str(h.opB)
                else:
                    assert False
                common = os.path.commonprefix([str(h.opA), opB])
                assert str(h.opB)[len(common)-1] == last_char_added
                arg = "%s%s" % (arg_prefix, str(h.opB)[len(common):])
                sols = [self.create_prefix(arg)]
                return sols
            elif k == EState.EOF:
                # An empty comparison at the EOF
                sols = []
                for new_char in All_Characters:
                    arg = "%s%s" % (arg_prefix, new_char)
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
        self.initiate_bfs = 0
        self._my_args = []

    def add_sys_args(self, var):
        if type(var) is not tainted.tstr:
            var = create_arg(var)
        else:
            var = create_arg(str(var))
        self._my_args.append(var)

    def sys_args(self):
        return self._my_args[-1]

    # Load the pickled state and also set the random set.
    # Used to start execution at arbitrary iterations.
    # requires prior dump
    def load(self, i):
        with open(Pickled % i, 'rb') as f:
            self.__dict__ = pickle.load(f)
            random.setstate(self.rstate)

    # Save the execution states at each iteration.
    def dump(self):
        with open(Pickled % self.start_i, 'wb') as f:
            self.rstate = random.getstate()
            pickle.dump(self.__dict__, f, pickle.HIGHEST_PROTOCOL)

    def choose_prefix(self, solutions):
        prefix = random.choice(solutions)
        return prefix

    def apply_prefix(self, prefix):
        self.current_prefix = prefix
        self.add_sys_args(prefix.my_arg)

    def log_comparisons(self):
        if Log_Comparisons:
            for c in tainted.Comparisons: print(c.opA._idx, c)

    def exec_argument(self, fn):
        self.start_i = 0
        if Load: self.load(Load)

        # replace interesting things
        solution_stack = [DFPrefix(random.choice(All_Characters))]

        for i in range(self.start_i, MaxIter):
            my_prefix, *solution_stack = solution_stack
            self.apply_prefix(my_prefix)
            self.start_i = i
            if Dump: self.dump()
            tainted.Comparisons = []
            try:
                log(">> %s" % self.sys_args(), 1)
                v = fn(self.sys_args())
                print('Arg: %s' % repr(self.sys_args()))
                self.log_comparisons()
                solution_stack = my_prefix.continue_valid()
                if not solution_stack:
                    return v
            except Exception as e:
                if i == MaxIter//100 and InitiateBFS:
                    print('with BFS', flush=True)
                    self.initiate_bfs = len(self.current_prefix.my_arg)
                traces = tainted.Comparisons
                solution_stack.extend(self.current_prefix.solve(traces, i))

                # prune works on the complete stack
                solution_stack = self.current_prefix.prune(solution_stack, self.initiate_bfs)

                if not solution_stack:
                    if not self.initiate_bfs:
                        # remove one character and try again.
                        new_arg = self.sys_args()[:-1]
                        if not new_arg:
                            raise Exception('No suitable continuation found')
                        solution_stack = [self.current_prefix.create_prefix(new_arg)]
                    else:
                        raise Exception('No suitable continuation found')


if __name__ == '__main__':
    import imp
    arg = sys.argv[1]
    _mod = imp.load_source('mymod', arg)
    e = Chain()
    e.exec_argument(_mod.main)
