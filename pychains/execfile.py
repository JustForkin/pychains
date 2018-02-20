import random
import pickle
import os.path
import string
import bytevm.sys as sys
import argparse
import logging
import bytevm.execfile as bex
import enum

import dataparser as dp
from .vm import TrackerVM, Op
from .tstr import tstr
from .exec_bfs import exec_code_object_bfs

RandomSeed = os.getenv('R')

#  Maximum iterations of fixing exceptions that we try before giving up.
MaxIter = 1000

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

Debug=0

All_Characters = list(string.printable + string.whitespace)
CmpSet = [Op.EQ, Op.NE, Op.IN, Op.NOT_IN]

def log(var, i=1):
    if Debug >= i: print(repr(var), file=sys.stderr, flush=True)

def brk(v=True):
    if not v: return None
    import pudb
    pudb.set_trace()

# TODO: Any kind of preprocessing -- space strip etc. distorts the processing.

def my_int(s):
    return dp.parse_int(s)

def my_float(s):
    return dp.parse_float(s)

def my_type(x):
    if '.tstr'in type(x):
        import pudb; pudb.set_trace()
        return 'str'
    return type(x)

def create_arg(s):
    if Track:
        return tstr(s, idx=0)
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
    def __init__(self, myarg, fixes):
        self.my_arg = myarg
        self.fixes = fixes

    def matching(self, elt, lst):
        largest, lelt = '', None
        for e in lst:
            common = os.path.commonprefix([elt, e])
            if len(common) > len(largest):
                largest, lelt = common, e
        return largest, lelt

    def parsing_state(self, h, arg_prefix):
        last_char_added = arg_prefix[-1]
        o = Op(h.opnum)

        if type(h.opA) is tstr:
            if o in [Op.EQ, Op.NE] and isinstance(h.opB, str) and len(h.opB) > 1:
                # Dont add IN and NOT_IN -- '0' in '0123456789' is a common
                # technique in char comparision to check for digits
                # A string comparison rather than a character comparison.
                return (1, EState.String, h)

            elif o in CmpSet and isinstance(h.opB, list) and max([len(opB) in h.opB]) > 1:
                # A string comparison rather than a character comparison.
                return (1, EState.String, h)

            if h.opA.x() == last_char_added.x():
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

        # Everything from this point on is a HACK because the dynamic tainting
        # failed.
        elif h.opA == last_char_added and isinstance(h.opB, str) and len(h.opB) == 1:
            # A character comparison of the *last* char.
            return (2, EState.Char, h)

        elif h.opA == last_char_added and isinstance(h.opB, str) and len(h.opB) != 1:
            # A character comparison of the *last* char.
            return (2, EState.String, h)

        elif h.opA == last_char_added:
            # A character comparison of the *last* char.
            return (3, EState.Char, h)

        elif o in [Op.EQ, Op.NE] and isinstance(h.opB, str) and h.opA == '':
            # What fails here: Imagine
            # def peek(self):
            #    if self.pos == self.len: return ''
            # HACK
            return (2, EState.EOF, h)

        elif o in [Op.IN, Op.NOT_IN] and isinstance(h.opB, (list, set)) and h.opA == '':
            # What fails here: Imagine
            # def peek(self):
            #    if self.pos == self.len: return ''
            # HACK
            return (2, EState.EOF, h)

        # elif o in CmpSet and isinstance(h.opB, str) and len(h.opB) > 1:
        # # Disabling this unless we have no other choice because too many
        # string version comparisons in source loading.
        #     # what fails here: Imagine
        #     #    ESC_MAP = {'true': 'True', 'false': 'false'}
        #     #    t.opA = ESC_MAP[s]
        #     # HACK
        #     brk()
        #     return (1, EState.String, h)

        # elif o in CmpSet and isinstance(h.opB, list) and max([len(opB) in h.opB]) > 1:
        #     # A string comparison rather than a character comparison.
        #     brk()
        #     return (1, EState.String, h)

        # elif len(h.opA) == 1 and h.opA != last_char_added:
        # We cannot do this unless we have tainting. Use Unknown instead
        #    return (1, EState.Trim, h)
        else:
            return (0, EState.Unknown, (h, last_char_added))

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
            if not isinstance(t.opA, str): continue
            if not len(t.opA) == 1: continue

            if type(t.opA) is tstr:
                if h.opA.x() != t.opA.x(): check = True
            else:
                # what fails here: Imagine
                #    ESC_MAP = {'n': '\n', 't': '\t'}
                #    t.opA = ESC_MAP[sys.argv[-1]]
                # HACK- fails on consecutive same char
                if h.opA != t.opA: check = True
            if not check:
                cmp_stack.append((i, t))
            else:
                pass
                # see microjson.py: decode_escape: ESC_MAP.get(c) why we cant always
                # transfer tstr

        return cmp_stack

    def extract_solutions(self, elt, lst_solutions, flip=False):
        fn = TrackerVM.COMPARE_OPERATORS[elt.opnum]
        result = fn(elt.opA, elt.opB)
        if isinstance(elt.opB, str) and len(elt.opB) == 0:
            if Op(elt.opnum) in [Op.EQ, Op.NE]:
                return lst_solutions
            else:
                assert False
        else:
            myfn = fn if not flip else lambda a, b: not fn(a, b)
            if result:
                lst = [c for c in lst_solutions if myfn(c, elt.opB)]
            else:
                lst = [c for c in lst_solutions if not myfn(c, elt.opB)]
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

    def solve(self, traces, i):
        arg_prefix = self.my_arg
        fixes = self.fixes
        last_char_added = arg_prefix[-1]
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        while traces:
            h, *ltrace = traces
            o = Op(h.opnum)

            idx, k, info = self.parsing_state(h, arg_prefix)
            log((RandomSeed, i, idx, k, info, "is tstr", isinstance(h.opA, tstr)), 0)

            if k == EState.Char:
                # A character comparison of the *last* char.
                # This was a character comparison. So collect all
                # comparisons made using this character. until the
                # first comparison that was made otherwise.
                cmp_stack = self.comparisons_on_last_char(h, traces)
                # Now, try to fix the last failure
                if h.opA == last_char_added and o in CmpSet:
                    # Now, try to fix the last failure
                    corr = self.get_corrections(cmp_stack, lambda i: i not in fixes)
                    if not corr: raise Exception('Exhausted attempts: %s' % fixes)
                else:
                    corr = self.get_corrections(cmp_stack, lambda i: True)
                    fixes = []

                # check for line cov here.
                prefix = arg_prefix[:-1]
                sols = []
                chars = {new_char for v in corr for new_char in v}
                for new_char in chars:
                    arg = "%s%s" % (prefix, new_char)
                    sols.append(Prefix(arg, fixes))

                return sols
            elif k == EState.Trim:
                # we need to (1) find where h.opA._idx is within
                # sys_args, and trim sys_args to that location
                args = arg_prefix[h.opA.x():]
                sols = [Prefix(args, [])]
                return sols # VERIFY - TODO

            elif k == EState.String:
                if o in [Op.IN, Op.NOT_IN]:
                    opB = self.matching(h.opA, h.opB)
                elif o in [Op.EQ, Op.NE]:
                    opB = h.opB
                else:
                    assert False
                common = os.path.commonprefix([h.opA, opB])
                assert h.opB[len(common)-1] == last_char_added
                arg = "%s%s" % (arg_prefix, h.opB[len(common):])
                sols = [Prefix(arg, [])]
                return sols
            elif k == EState.EOF:
                # An empty comparison at the EOF
                sols = []
                for new_char in All_Characters:
                    arg = "%s%s" % (arg_prefix, new_char)
                    sols.append(Prefix(arg, []))

                return sols
            elif k == EState.Unknown:
                # Unknown what exactly happened. Strip the last and try again
                # try again.
                traces = ltrace
                continue
            else:
                assert False

        return []

class ExecFile(bex.ExecFile):

    def add_sys_args(self, var):
        if type(var) is not tstr: var = create_arg(var)
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

    def add_new_char(self, fix):
        self.add_sys_args(fix)
        if len(sys.argv) < 2: sys.argv.append([])
        sys.argv[1] = self.sys_args()

    def last_char_added(self):
        return self.sys_args()[-1]

    def choose_char(self, lst):
        if Distribution=='C':
            # A cumulative distribution where characters that have not
            # appeared until now are given equally higher weight.
            myarr = {i:1 for i in All_Characters}
            for i in self.sys_args(): myarr[i] += 1
            my_weights = [1/myarr[l] for l in lst]
            return random.choices(lst, weights=my_weights, k=1)[0]
        elif Distribution=='X':
            # A cumulative distribution where characters that have not
            # appeared in last 100 are given higher weight.
            myarr = {i:1 for i in All_Characters}
            for i in set(self.sys_args()[-100:]):
                myarr[i] += 10
            my_weights = [1/myarr[l] for l in lst]
            return random.choices(lst, weights=my_weights, k=1)[0]

        else:
            return random.choice(lst)

    def exec_code_object(self, code, env):
        self.start_i = 0
        if Load: self.load(Load)

        # replace interesting things
        # env['type'] = my_type
        env['int'] = my_int
        env['float'] = my_float

        fix = self.choose_char(All_Characters)
        self.add_new_char(fix)

        for i in range(self.start_i, MaxIter):
            self.start_i = i
            if Dump: self.dump()
            vm = TrackerVM()
            try:
                log(">> %s" % self.sys_args(), 0)
                v = vm.run_code(code, f_globals=env)
                print('Arg: %s' % repr(self.sys_args()))
                if random.uniform(0,1) > Return_Probability:
                    self._fixes = []
                    self.add_sys_args("%s%s" % (sys.argv[1], self.last_char_added()))
                    sys.argv[1] = self.sys_args()
                else:
                    return v
            except Exception as e:
                if i == MaxIter -1 and InitiateBFS:
                    self.initiate_bfs = True
                    return exec_code_object_bfs(code, env, self.sys_args())
                traces = list(reversed(vm.get_trace()))
                my_arg = self.sys_args()
                # fixes are characters that have been tried at that particular
                # position already.
                fixes = self.fixes()

                prefix = Prefix(my_arg, fixes)
                solutions = prefix.solve(traces, i)

                if not solutions:
                    # remove one character and try again.
                    self.add_sys_args(self.sys_args()[:-1])
                    sys.argv[1] = self.sys_args()
                    self._fixes = fixes
                    if not self.sys_args():
                        # we failed utterly
                        raise Exception('No suitable continuation found')
                    return

                # use this prefix
                prefix = random.choice(solutions)
                self.add_sys_args(prefix.my_arg)
                sys.argv[1] = self.sys_args()
                self._fixes = prefix.fixes

    def fixes(self):
        return self._fixes + [self.last_char_added()]

    def reinit(self):
        self.initiate_bfs = False
        self._my_args = []
        self._fixes = []

    def cmdline(self, argv):
        parser = argparse.ArgumentParser(
            prog="pychains",
            description="Find valid inputs for the given program.",
        )
        parser.add_argument(
            '-m', dest='module', action='store_true',
            help="prog is a module name, not a file name.",
        )
        parser.add_argument(
            '-v', '--verbose', dest='verbose', action='store_true',
            help="trace the execution of the bytecode.",
        )
        parser.add_argument(
            'prog',
            help="The program to run.",
        )
        parser.add_argument(
            'args', nargs=argparse.REMAINDER,
            help="Arguments to pass to the program.",
        )
        args = parser.parse_args()

        level = logging.DEBUG if args.verbose else logging.WARNING
        logging.basicConfig(level=level)

        self.reinit()
        self.run_python_file(args.prog, [args.prog] + args.args)
