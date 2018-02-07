import random
import dis
import os.path
import string
import sys
import argparse
import logging
import bytevm.execfile as bex
import bytevm.pyvm2 as pvm
import enum

MaxIter = 1000
def set_maxiter(i):
    global MaxIter
    MaxIter = i

Debug=0
def set_debug(i):
    global Debug
    Debug = i

def log(var, i=1):
    if Debug >= i:
        print(var)

# TODO: Any kind of preprocessing -- space strip etc. distorts the processing.

from .vm import TrackerVM, Op
from .tstr import tstr

class EState(enum.Enum):
    Last = enum.auto()
    EOF = enum.auto()
    String = enum.auto()
    Char = enum.auto()
    Skip = enum.auto()
    Unknown = enum.auto()

All_Characters = list(string.printable + string.whitespace)

def save_trace(traces, i, file='trace'):
    if Debug > 0:
        with open('.t/%s-%d.txt' % (file,i), 'w+') as f:
            [print(i, file=f) for i in traces]

class ExecFile(bex.ExecFile):
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
        others = []
        if self.last_fix != self.checked_char:
            for i, t in enumerate(cmp_traces):
                if h.opA == t.opA:
                    cmp_stack.append((i, t))
                else:
                    others.append((i, t))
        else:
            # Now, this is heuristics. What we really need is a tainting package
            # so that we can exactly track the comparisons on the last character
            # for now, we assume that the last successful match was probably
            # made on the last_fix
            assert False # to be disabled after verification.
            for i, t in enumerate(cmp_traces):
                success = False
                if h.opA == t.opA:
                    if t.result: success = True
                    if success:
                        others.append((i, t))
                    else:
                        cmp_stack.append((i, t))
                else:
                    others.append((i, t))

        return (cmp_stack, others)

    def extract_solutions(self, elt, lst_solutions, flip=False):
        fn = TrackerVM.COMPARE_OPERATORS[elt.opnum]
        result = fn(elt.opA, elt.opB)
        myfn = fn if not flip else lambda a, b: not fn(a, b)
        if result:
            lst = [c for c in lst_solutions if myfn(c, elt.opB)]
        else:
            lst = [c for c in lst_solutions if not myfn(c, elt.opB)]
        return lst


    def get_correction(self, cmp_stack):
        """
        cmp_stack contains a set of comparions, with the last comparison made
        at the top of the stack, and first at the bottom. Choose a point
        somewhere and generate a character that conforms to everything until then.
        """
        stack_size = len(cmp_stack)
        point = random.randrange(0, stack_size)
        # point = stack_size - 1
        # now, we need to skip everything
        diverge, *satisfy = cmp_stack[point:]
        lst_solutions = All_Characters
        for i,elt in reversed(satisfy):
            assert elt.opA == self.checked_char
            lst_solutions = self.extract_solutions(elt, lst_solutions, False)
        # now we need to diverge here
        i, elt = diverge
        assert elt.opA == self.checked_char
        lst_solutions = self.extract_solutions(elt, lst_solutions, True)
        return lst_solutions

    def is_same_op(self, a, b):
        return a.opnum == b.opnum and a.opA == b.opA and a.opB == b.opB

    def kind(self, h):
        if h.opA == self.checked_char and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) == False:
            return (1, EState.Char)
        elif Op(h.opnum) in [Op.EQ, Op.IN] and h.opA == '' and h.opB != '' and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) == False:
            # if opA is empty, and it is being compared to non empty then
            # the last char added matched
            return (1, EState.EOF)
        elif Op(h.opnum) in [Op.NE, Op.NOT_IN] and h.opA == '' and (h.opB == '' or '' in h.opB) and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) == True:
            # if opA is empty, and it is being compared to non empty then
            # the last char added matched
            return (1.1, EState.EOF)
        elif Op(h.opnum) == Op.EQ and h.opA == '' and h.opB == ''  and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) == True:
            return (2, EState.EOF)
        elif Op(h.opnum) == Op.EQ and type(h.opB) is str and len(h.opB) > 1 and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) == False:
            return (1, EState.String)
        elif h.opA == self.last_fix and Op(h.opnum) in [Op.IN, Op.EQ] and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) != self.last_result:
            # if the comparison is eq or in and it succeeded and the character
            # compared was equal to last_fix, then this is the last match.
            return (3, EState.Last)
        elif h.opA == self.checked_char and Op(h.opnum) in [Op.IN, Op.EQ] and \
            TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB) != self.last_result:
            return (4 ,EState.EOF)
        else:
            return (0, EState.Unknown)

    def on_trace(self, i, vm, traces):
        # we are assuming a character by character comparison.
        # so get the comparison with the last element.
        h, *ltrace = traces
        self.last_iter_top = h
        self.result_of_last_op = TrackerVM.COMPARE_OPERATORS[h.opnum](h.opA, h.opB)

        idx, k = self.kind(h)
        log((i, idx, k, vm.steps), 2)
        if k == EState.Char:
            # This was a character comparison. So collect all
            # comparisions made using this character. until the
            # first comparison that was made otherwise.
            cmp_stack, _ = self.comparisons_on_last_char(h, ltrace)
            # Now, try to fix the last failure
            self.next_opts = self.get_correction(cmp_stack)
            new_char = random.choice(self.next_opts)
            self.next_opts = [i for i in self.next_opts if i != new_char]
            arg = "%s%s" % (sys.argv[1][:-1], new_char)

            self.last_fix = new_char
            self.checked_char = None
            self.last_result = self.result_of_last_op
            self.saved_last_iter_top = self.last_iter_top
            return tstr(arg, idx=0)
        elif k == EState.Skip:
            # this happens when skipwhitespaces and similar are used.
            # the parser skips whitespaces, and compares the last
            # non-whitespace which may not be the last character inserted
            # if we had inserted a whitespace.
            # So the solution (for now) is to simply assume that the last
            # character matched.
            new_char = random.choice(All_Characters)
            arg = "%s%s" % (sys.argv[1], new_char)

            self.checked_char = new_char
            self.last_fix = None
            return tstr(arg, idx=0)
        elif k == EState.String:
            #assert h.opA == self.last_fix or h.opA == self.checked_char
            common = os.path.commonprefix(h.oargs)
            if self.checked_char:
                # if checked_char is present, it means we passed through
                # EState.EOF
                assert h.opB[len(common)-1] == self.checked__char
                arg = "%s%s" % (sys.argv[1], h.opB[len(common):])
            elif self.last_fix:
                assert h.opB[len(common)-1] == self.last_fix
                arg = "%s%s" % (sys.argv[1], h.opB[len(common):])

            self.last_fix = None
            self.checked_char = None
            return tstr(arg, idx=0)
        elif k == EState.EOF:
            new_char = random.choice(All_Characters)
            arg = "%s%s" % (sys.argv[1], new_char)

            self.checked_char = new_char
            self.last_fix = None
            self.last_result = self.result_of_last_op
            self.saved_last_iter_top = self.last_iter_top
            return tstr(arg, idx=0)
        elif k == EState.Last:
            # try other alternatives
            new_char = random.choice(self.next_opts)
            self.next_opts = [i for i in self.next_opts if i != new_char]

            arg = "%s%s" % (sys.argv[1][:-1], new_char)

            self.last_fix = new_char
            self.checked_char = None
            self.last_result = self.result_of_last_op
            self.saved_last_iter_top = self.last_iter_top
            return tstr(arg, idx=0)
        else:
            assert False

    def exec_code_object(self, code, env):
        self.last_fix = sys.argv[1][-2] if len(sys.argv[1]) > 1 else None
        # The last_character assignment made is the first character assigned
        # when starting.
        self.checked_char = sys.argv[1][-1]
        last_vm_step = 0

        for i in range(0, MaxIter):
            vm = TrackerVM()
            try:
                log(">> %s" % sys.argv, 0)
                res = vm.run_code(code, f_globals=env)
                log("Result: %s" % sys.argv)
                return res
            except Exception as e:
                vm_step = vm.steps
                vm_step = last_vm_step
                traces = list(reversed(vm.get_trace()))
                save_trace(traces, i)
                save_trace(vm.byte_trace, i, file='byte')
                sys.argv[1] = self.on_trace(i, vm, traces)

    def cmdline(self, argv):
        parser = argparse.ArgumentParser(
            prog="bytevm",
            description="Run Python programs with a Python bytecode interpreter.",
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

        # making it easy!. We start with a space
        self.checked_char = tstr(random.choice(All_Characters), idx=0)
        new_argv = [args.prog] + [self.checked_char]
        if args.module:
            self.run_python_module(args.prog, new_argv)
        else:
            self.run_python_file(args.prog, new_argv)
