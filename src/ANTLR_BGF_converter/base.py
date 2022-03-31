import os
import re
from enum import IntEnum


class FBG:

    def __init__(self):
        self.start_nonterminal = None
        self.nt_name_to_nt_obj = { }
        self.__all_nonterminals = []
        self.skip = ""
        self.not_nonterminals = []
        self.__used_nonterminals = set()

        self.print_unused = False
        self.abort_if_used_but_not_defined = True


    def import_fbl(self, fbg):
        self.nt_name_to_nt_obj = { **fbg.nt_name_to_nt_obj, **self.nt_name_to_nt_obj }


    def create_nonterminal_from_expression_lst(self, exp_lst):
        nt_name = ""
        for e in exp_lst:
            assert isinstance(e, Element)
            nt_name += e.get_name() + "|"

        assert len(nt_name) > 2
        nt_name = nt_name[:-1]

        (nt, known) = self.create_nonterminal(nt_name, False)
        nt_wrp = self.create_nonerminal_wrapper(nt)

        for e in exp_lst:
            nt_wrp.add_expression(e)

        return nt_wrp


    def create_nonterminal_from_char_lst(self, lst, name = None):
        nt_name = ""

        if name:
            nt_name = name
        else:
            for c in lst:
                nt_name += c.get_name() + "|"

            nt_name = nt_name[:-1]

        (nt, known) = self.create_nonterminal(nt_name, False)
        wrap = self.create_nonerminal_wrapper(nt)

        if known:
            return wrap

        for c in lst:
            nt.add_expression(Expression([Terminal(c)]))

        return wrap


    def __print_expression(self, nt):
        skip = ""
        if self.skip and self.skip != nt:
            skip = f"(<{self.skip.get_name()}>)*"

        output = ""

        content = nt.get_body()
        if len(content) == 0:
            return "   \"\"\n    ],\n\n\n"
        line = "\n        "
        for expressions in content:
            assert not isinstance(expressions, list)
            exp = str(expressions.print(skip))
            if len(line) + len(exp) > 125:
                if len(line) > 0:
                    output += line + "\n        "
                line = ""
            line += f'"{exp}", '

        output += line[:-len(", ")]
        output += "\n    ],\n\n\n"
        return output


    def print(self):
        if not self.start_nonterminal:
            return ""

        if self.print_unused:
            lst = self.__all_nonterminals
        else:
            lst = self.travel_tree(self.start_nonterminal)
            lst.add(self.start_nonterminal)
            if self.skip:
                lst.add(self.skip)
                lst = lst.union(self.travel_tree(self.skip))

        lst = self.creat_not_list(lst)

        #######################################################


        fbl = "{\n"
        for nt in lst:
            name = nt.print()
            fbl += f'    "{name}":\n    ['
            exp = self.__print_expression(nt)
            fbl += exp

        if len(fbl) > 2:
            fbl = fbl[:-2]
        fbl += "}"

        return fbl


    def get_all_nts_from_nt(self, nt):
        all_nts_used = []
        checked = set()
        for e in nt.get_body():
            if isinstance(e, Expression):
                a = self.getAllFromExp(e, checked)
            elif isinstance(e, Nonterminal):
                a = self.getAllFromNT(e, checked)
            else:
                assert False
            all_nts_used.extend(a)
        return all_nts_used


    def getAllFromExp(self, exp, checked):
        all = []
        for e in exp:
            if isinstance(e, Expression):
                all.extend(self.getAllFromExp(e, checked))
            elif isinstance(e, Nonterminal):
                all.append(e)
                all.extend(self.getAllFromNT(e, checked))
            elif isinstance(e, Brackets):
                c = e.get_child()
                if isinstance(c, Expression):
                    all.extend(self.getAllFromExp(c, checked))
                elif isinstance(c, Nonterminal):
                    all.append(c)
                    all.extend(self.getAllFromNT(c, checked))
            else:
                pass
        return all


    def getAllFromNT(self, nt, checked):
        if nt in checked:
            return []
        checked.add(nt)
        all = []
        for e in nt.get_body():
            if isinstance(e, Nonterminal):
                all.append(nt)
                used = self.getAllFromNT(e, checked)
                all.extend(used)
            if isinstance(e, Expression):
                all.extend(self.getAllFromExp(e, checked))

        return all


    def travel_tree(self, nt, all_used = None) -> set:

        if not all_used:
            all_used = set()

        nts_in_nt = self.get_all_nts_from_nt(nt)

        for nts in nts_in_nt:
            if nts not in all_used:
                all_used.add(nts)
                all_used.update(self.travel_tree(nts, all_used))

        return all_used


    def creat_not_list(self, lst):

        skipp = ["<start>"]

        for not_nt in self.not_nonterminals:

            expressions = set()
            for nt in lst:

                if not_nt.get_name() == nt.get_name():
                    continue
                elif nt.get_name() in skipp:
                    continue
                elif not_nt.not_nt and not_nt.not_nt.get_name() == nt.get_name():
                    continue
                elif nt.is_not_nt:
                    continue
                elif nt.is_virtual:
                    continue
                elif nt.get_name() in not_nt.not_nts_name:
                    continue
                elif not nt.is_lexer_rule():
                    continue
                elif not_nt in self.get_all_nts_from_nt(nt):
                    continue
                else:
                    expressions.add(nt)

            for e in expressions:
                not_nt.add_expression(e)

        return lst


    def create_nonterminal(self, name, is_reference_only = True, wrapper = False, is_virtual = True,
                           force_check_duplicate = False
                           ):

        if self.abort_if_used_but_not_defined and \
                is_reference_only and name not in self.nt_name_to_nt_obj:

            if name == "EOF":
                pass
            else:
                raise ReferenceError(f"Used but not defined {name}")

        already_known = False
        if name in self.nt_name_to_nt_obj and (is_virtual or force_check_duplicate):
            nt = self.nt_name_to_nt_obj[name]
            already_known = True
        else:
            nt = Nonterminal(name)
            nt.is_virtual = is_virtual
            self.nt_name_to_nt_obj[nt.get_name()] = nt

        if not wrapper and nt not in self.__all_nonterminals:
            self.__all_nonterminals.append(nt)

            if nt.get_name() == "start":
                self.start_nonterminal = nt

        return (nt, already_known)


    def create_nonerminal_wrapper(self, nt):
        printIt("Wrapper for " + nt.get_name(), LogLvl.function_calls)
        name = nt.get_name()  # + "_wrap"
        (wrapper, _) = self.create_nonterminal(name, False, True)
        return wrapper


    # Creating a new terminal of if the string contains problematic characters,
    # split them to terminals and nonterminal and return the expression
    def create_terminal(self, name):
        # check if any chars in the string that can cause problems in FBL
        s = re.findall(r"[+,*,?,<,>]", name)

        # If name is +, * or ? we need to create a new nonterminal.
        # FBL is not able to escape one of theses chars and always thinks its part of EBNFs
        # same for < or >
        if len(s) > 0:
            nt_name = ""
            exp = Expression()
            # if yes we iter over each char and create a new nonterminal out of it if
            # the char can cause problems
            escaped = False
            for c in name:
                if c in ["+", "*", "?", "<", ">"]:
                    escaped = True

                    # first check if the escaped nonterminal already exists.
                    # this can may happens, if a BGF grammar was already converted and
                    # this is the second round.
                    c_escaped = Nonterminal.escape_name(c)
                    same = c_escaped == c
                    (nt_c, known) = self.create_nonterminal(c_escaped, False)

                    if len(nt_c.get_body()) == 0 or not known:
                        nt_c.add_expression(Expression([Terminal(c)]))

                    exp.append(nt_c)
                    nt_name += nt_c.get_name()
                else:
                    nt_name += c
                    exp.append(Terminal(c))

            if not escaped:
                return Terminal(name)

            (nt, known) = self.create_nonterminal(nt_name, False)
            if not known:
                nt.add_expression(exp)

            return self.create_nonerminal_wrapper(nt)

        return Terminal(name)


############################################################################################
############################################################################################
############################################################################################
############################################################################################
############################################################################################

## The Element class is the superclass of every element like nonterminal, terminal, EBNF, expression.
class Element():

    def get_name(self):
        raise NotImplementedError("Superclass not overwritten")


    def print(self):
        raise NotImplementedError("Superclass not overwritten")


class Nonterminal(Element):

    def __init__(self, name, is_reference = False, not_nt = None, is_not_nt = False):
        self.not_nt = not_nt  # object of the inverted NT
        self.not_nts_name = []  # used for BlockSetContext ~, list of all names of nonteminals
        self.is_not_nt = is_not_nt  # is true if this is a NOT nonterminal (~)
        self.is_reference = is_reference  # true if this NT is only a reference and has no content
        self.is_virtual = True  # true, if it just get used by another nonterminal. False, if this is the definiton

        assert len(name) > 0

        self.__is_lexer_rule = name[0].isupper() or \
                               (
                                       (name[0] == "[" or name[0:2] == "~[")
                                       and name[-1] == "]")

        self.__name = name
        self.__body = []
        printIt("CREATED new nonterminal " + self.get_name(), LogLvl.debug)


    def is_lexer_rule(self):
        return self.__is_lexer_rule


    @staticmethod
    def escape_name(name):
        escaped_name = name
        escaped_name = escaped_name.encode("unicode_escape").decode("utf-8")
        # replacing < and > with { and } because < and > are  not allowed in a nt name in FBL
        escaped_name = escaped_name.replace("<", "{").replace(">", "}")
        # escaping " because we later print it all as dict with seperateds elements with "
        escaped_name = escaped_name.replace('\"', "\\\"")
        # whitespaces are also not allowed
        escaped_name = escaped_name.replace(' ', '_')
        # ) and an ebnf is atm not possible in FBG, so just replace ( and ) with [ and ]
        escaped_name = escaped_name.replace("(", "[LB[").replace(")", "]RB]")
        # replacing unicode in nonterminal names. can lead to problems otherwise
        escaped_name = escaped_name.replace("\\\\u", "\\u")
        escaped_name = escaped_name.replace("\\u", "uni")

        # if name != "start":
        #   name = base64.b64encode(name.encode('ascii')).decode('ascii')[:10]
        # escaped_name = hashlib.md5(escaped_name.encode('utf-8')).hexdigest()
        return escaped_name


    def add_expression(self, exp):
        assert not isinstance(exp, list)
        if not isinstance(exp, Expression):
            exp = Expression([exp])
        self.__body.append(exp)


    def get_name(self):
        return self.__name


    def get_body(self):
        return self.__body


    def print(self):
        return f'<{self.escape_name(self.__name)}>'


    def __hash__(self):
        return hash(self.get_name())


class Terminal(Element):

    def __init__(self, name):
        self.name = str(name)
        printIt("CREATED new terminal " + self.name, LogLvl.debug)


    @staticmethod
    def escape_name(name):
        escaped_name = name
        escaped_name = escaped_name.encode("unicode_escape")
        unicode_escaped_name = escaped_name.decode("unicode-escape")
        utf_escaped_name = escaped_name.decode("utf-8")
        escaped_name = unicode_escaped_name
        if len(escaped_name) == 1:
            escaped_name = utf_escaped_name

        escaped_name = escaped_name.replace('"', '\\"')
        escaped_name = escaped_name.replace("\a", "\\a")
        escaped_name = escaped_name.replace("\b", "\\b")
        escaped_name = escaped_name.replace("\t", "\\t")
        escaped_name = escaped_name.replace("\n", "\\n")
        escaped_name = escaped_name.replace("\v", "\\v")
        escaped_name = escaped_name.replace("\f", "\\f")
        escaped_name = escaped_name.replace("\r", "\\r")


        return escaped_name


    def __eq__(self, other):
        if isinstance(other, Terminal):
            return str(self) == str(self)
        return False


    def get_name(self):
        return self.name


    def print(self):
        return self.escape_name(self.name)


class EBNF(Element):

    def __init__(self, name):
        assert name in ["*", "?", "+", "*?", "??", "+?"]
        if name in ["*?", "+?", "??"]:
            printUnimplemented("Non-greedy", None, name, "Using the greedy option here.")
            name = name[:-1]
        self.name = name


    def get_name(self):
        return self.name


    def print(self):
        return self.name


class Brackets(Element):

    def __init__(self, child, ebnf = None):
        assert not isinstance(child, Brackets)
        assert isinstance(child, Element)
        self.child = child
        if ebnf:
            assert isinstance(ebnf, EBNF)
        self.__ebnf = ebnf


    def get_child(self):
        return self.child


    def get_name(self):
        if self.__ebnf:
            return f"({self.child.get_name()}){self.__ebnf.get_name()}"
        return f"({self.child.get_name()})"


    def print(self, skip = ""):
        if self.__ebnf:
            return f"({self.child.print()}){self.__ebnf.print()}"
        return f"({self.child})"


class Expression(Element):

    def __init__(self, lst = None):
        if lst is None:
            lst = list()
        self.__expression = []
        for e in lst:
            self.append(e)


    def append(self, ele):
        if not ele:
            return
        assert isinstance(ele, Element)
        self.__expression.append(ele)


    def get_name(self):
        s = ""
        for i in self.__expression:
            s += i.get_name()

        return s


    def print(self, skip = ""):
        s = ""
        for i in self.__expression:
            content = i.print()
            s += content
            if not content.endswith(str(skip)):
                s += str(skip)

        return s


    def __len__(self):
        return len(self.__expression)


    def __iter__(self):
        return iter(self.__expression)


    def __getitem__(self, item):
        return self.__expression[item]


    def __eq__(self, other):
        if isinstance(other, Expression):
            return str(self) == str(other)
        return False


###################################################################################################
########################################## FBG Stuff ##############################################
###################################################################################################


re_token = re.compile('^<(.|\s)+?>(\+|\*|\?)?$')
re_nonterminal = re.compile("^<.+?>(\+|\*|\?)?$")


# Splitting a string into terminals and nonterminals and put them in a list
def parse_FBG_rule(rule):
    rule = rule.encode("unicode_escape").decode("utf-8")  # needed for \n
    exp_list = re.split('(<.+?>(\+|\*|\?)?)', rule)
    exp_list = [x for x in exp_list if x is not None and x != ""]

    re_nonterminal = re.compile("^<(.|\s)+?>(\+|\*|\?)$")

    parsed_expressions = []
    i = 0
    while i < len(exp_list):
        parsed_expressions.append(exp_list[i])
        if re_nonterminal.match(exp_list[i]):
            i += 1
        i += 1

    for i in range(0, len(parsed_expressions)):
        parsed_expressions[i] = parsed_expressions[i].encode("utf-8").decode("unicode_escape")

    return parsed_expressions


def is_nonterminal(s) -> bool:
    return re_token.match(s) is not None


######################################################################################
######################################################################################
######################################################################################

def read_file_in(input_file):
    with open(input_file, 'r') as f:
        content = f.read()

    return content


def list_equal(l1, l2):
    if len(l1) != len(l2):
        return False
    return sorted(l1) == sorted(l2)


def srange(characters):
    return [c for c in characters]


class LogLvl(IntEnum):
    function_calls = 0
    debug = 1
    info = 2
    warning = 3
    error = 4

    unsupported = 10
    unimplemented = 11
    nothing = 100


currentLogLevel = LogLvl.warning


def get_line_out_of_antlr_obj(obj):
    o = obj
    if isinstance(obj, list):
        if len(obj) > 0:
            o = obj[0]

    try:
        return o.start.line
    except:
        pass

    try:
        return o.parentCtx.start.line
    except:
        pass

    return "?"


def printUnimplemented(feature, line, subfeature = None, comment = None):
    msg = ""

    if line:
        line = get_line_out_of_antlr_obj(line)
        msg += f"Line {line}: "

    msg += f"Feature '{feature}'"

    if subfeature:
        msg += f" with {subfeature}"

    msg += f" is not supported."

    if comment:
        msg += " " + comment

    printIt(msg, LogLvl.unimplemented)


def printIt(msg, loglvl = None, obj = None):
    if currentLogLevel == LogLvl.nothing:
        return

    if not loglvl:
        loglvl = LogLvl.function_calls

    if int(loglvl) == int(loglvl.unsupported):
        print(msg)


    elif int(loglvl) == int(loglvl.unimplemented):
        print(msg)


    elif int(loglvl) >= int(currentLogLevel):
        if obj:
            line = get_line_out_of_antlr_obj(obj)
            msg = f"Line {line}: {msg}"
            try:
                a = obj.start.text
                b = obj.stop.text
                if a and b:
                    msg = f"{msg} | {a} - {b} |"
            except:
                pass
        print(msg)
