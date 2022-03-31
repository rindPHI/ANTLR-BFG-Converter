import ast
import base64
import json
import re
from datetime import datetime
from base import *
from fuzzingbook.Grammars import convert_ebnf_grammar

VERSION = "1.0"

invalid_nonterminal_chars = ["[", "]", "'", "<", ">", "-"]
tokens = list()
# re_token = re.compile('^<.+?>(\+|\*|\?)?$') #breaks when a \n is in the nonterminal name
re_token = re.compile('^<(.|\s)+?>(\+|\*|\?)?$')


class FBG_to_ANTLR:

    def __init__(self, input_file):

        self.grammar_name = os.path.basename(input_file)
        self.grammar_name = self.grammar_name.replace(".", "")
        self.antlr = ANTLR(self.grammar_name)

        content = read_file_in(input_file)
        grammar = ast.literal_eval(content)
        self.content = convert_ebnf_grammar(grammar)


    def convert(self):
        self.parse()


    def is_nonterminal(self, s) -> bool:
        return re_token.match(s) is not None


    def parse_tokens(self, json):
        for key, value in json.items():
            tokens.append(key)


    def antlr_list_to_string(self, lst) -> str:
        return ''.join(map(str, lst))


    def replacer(self, s, lst) -> str:
        for i in lst:
            s = s.replace(i, "")
        return s


    def parse_term(self, value):
        values = parse_FBG_rule(value)
        expressions = Expression()

        for i in values:
            if not self.is_nonterminal(i):
                terminal = Terminal(i)
                expressions.append(terminal)

            else:
                nt_name = i
                (nt, known) = self.antlr.create_nonterminal(nt_name)
                expressions.append(nt)

        return expressions


    def parse_rule(self, value) -> list:

        expressions = list()
        for i in value:
            parsed_term = self.parse_term(i)
            expressions.append(parsed_term)

        return expressions


    def parse(self):
        for rule_name, value in self.content.items():

            (nt, known) = self.antlr.create_nonterminal(rule_name)

            if rule_name == "<start>":
                self.antlr.start = nt

            content = self.parse_rule(value)

            for exp in content:
                nt.add_expression(exp)


    def print(self):
        return self.antlr.print()


class ANTLR:

    def __init__(self, grammar_name):
        self.all_nts = { }
        self.grammar_name = grammar_name
        self.start = None


    def create_nonterminal(self, name):
        if name in self.all_nts:
            return (self.all_nts[name], True)

        nt = Nonterminal(name)
        self.all_nts[name] = nt

        return (nt, False)


    def __print_nt(self, nt):
        output = nt.get_name() + '\n    :'
        content = nt.get_body()
        if len(content) == 0:
            return ""
        line = ""
        for expressions in content:
            exp = " " + str(expressions.print(" "))
            # make sure a line is no longer then 125 chars for better readability
            if len(line) + len(exp) > 125:
                if len(line) > 0:
                    line = line[:-len("  |")]  # remove last |
                    output += line + "\n    |"
                line = ""
            line += f' {exp} |'

        output += line[:-len("  |")]
        output += '\n    ;\n\n'
        return output


    def print(self):

        # recheck all rules for lexer or parser rules:

        while True:
            ok = True
            for _, nt in self.all_nts.items():
                ok = ok and nt.recheck_if_parser_or_lexer()

            if ok:
                break

        dateTimeObj = datetime.now()
        output = f"/*\nThis grammar was automatically converted from the fuzzing book grammar to ANTLR by FB_to_ANTLR converter v{VERSION}\n"
        output += f"Conversion time: {dateTimeObj}\n"
        output += "*/\n\n"
        output += f"grammar {self.grammar_name};\n\n"
        comment_len = 50
        lexer = "\n\n" + "/" * comment_len + "\n"
        lexer += "/" * (int(comment_len / 2) - 7) + " LEXER RULES  " + "/" * (int(comment_len / 2) - 7) + "\n"
        lexer += "/" * comment_len + "\n\n\n\n"

        output += self.__print_nt(self.start)

        # printing all nonterminals
        for name, nt in self.all_nts.items():
            o = self.__print_nt(nt)

            if nt == self.start:
                pass
            elif nt.is_parser_rule:
                output += o
            else:
                lexer += o

        output += lexer

        return output


class Nonterminal(Element):

    def __init__(self, name):
        self.is_parser_rule = True
        self.name = name
        self.used_in_list = set()
        if name[1].isupper():
            self.is_parser_rule = False

        self.__body = []


    def __check_expression_for_parser_rules(self, ex, only_terminals, contains_parser_rule):
        if isinstance(ex, Nonterminal):
            only_terminals = False
            if ex.is_parser_rule:
                contains_parser_rule = True
        elif isinstance(ex, Expression):
            for e in ex:
                (only_terminals1, contains_parser_rule1) = self.__check_expression_for_parser_rules(e, only_terminals,
                                                                                                    contains_parser_rule
                                                                                                    )
                only_terminals = only_terminals and only_terminals1
                contains_parser_rule = contains_parser_rule or contains_parser_rule1

        return (only_terminals, contains_parser_rule)


    # checking it this rule is can be a lexer rule or has to be a parser rule
    # by examine all expressions
    def recheck_if_parser_or_lexer(self):

        current_state = self.is_parser_rule
        only_terminals = True
        contains_parser_rule = False
        for ex in self.__body:
            (only_terminals1, contains_parser_rule1) = self.__check_expression_for_parser_rules(ex, only_terminals,
                                                                                                contains_parser_rule
                                                                                                )
            only_terminals = only_terminals and only_terminals1
            contains_parser_rule = contains_parser_rule or contains_parser_rule1

        if only_terminals and not contains_parser_rule:
            self.is_parser_rule = False

        if contains_parser_rule:
            self.is_parser_rule = True

        if current_state != self.is_parser_rule:
            for nt in self.used_in_list:
                nt.recheck_if_parser_or_lexer()

        return current_state == self.is_parser_rule


    def find_used_nt_in_exp(self, exp, s):
        if isinstance(exp, Nonterminal):
            s.add(exp)
        elif isinstance(exp, Expression):
            for e in exp:
                s.update(self.find_used_nt_in_exp(e, s))

        return s


    def add_expression(self, exp):
        assert not isinstance(exp, list)
        if not isinstance(exp, Expression):
            exp = Expression([exp])
        self.__body.append(exp)

        s = set()
        for ex in exp:
            s.update(self.find_used_nt_in_exp(ex, s))

        self.used_in_list.update(s)


    def escape_char(self, c):
        base64_encoded_data = base64.b64encode(c.encode())
        base64_message = base64_encoded_data.decode('utf-8')
        base64_message = base64_message.replace("=", "1")
        base64_message = base64_message.replace("+", "p")
        base64_message = base64_message.replace("/", "_")
        out = base64_message
        return out


    def escape_range_name(self, name):
        re_token = re.compile('^\[(.|\s)+?]$')
        if re_token.match(name) is None:
            return name

        name = name[1:-1]
        return "range_" + name


    def escape(self, rule_name):

        if rule_name == "jump_modifier_1":
            a = 3

        if not rule_name[1].isalpha():
            pass
            # rule_name = "Lex" + rule_name

        if rule_name[0] == "<":
            rule_name = rule_name[1:]
        if rule_name[-1] == ">":
            rule_name = rule_name[:-1]

        rule_name = rule_name.replace("-", "_")

        allowed_chars = ["_"]

        rule_name = self.escape_range_name(rule_name)

        out = ""
        for c in rule_name:
            if c.isalpha() or ((c.isdigit() or c in allowed_chars) and len(out) > 0):
                out += c
            else:
                out += self.escape_char(c)

        if self.is_parser_rule:
            out = "parser_" + out
        else:
            out = "Lexer_" + out

        escaped_name = out
        escaped_name = escaped_name.encode("unicode_escape").decode("utf-8")
        escaped_name = escaped_name.replace('"', '\\"')
        # escape hex encoded chars like \xb2. otherwise it leads to problems while using grammarinator
        escaped_name = escaped_name.replace("\\x", "x")
        return escaped_name


    def get_name(self):
        return self.print()


    def get_body(self):
        return self.__body


    def print(self):
        name = self.escape(self.name)
        # reduce name to 200 chars, otherwise there could be problems in ANTLR (java max class name length)
        return name[:200]


class Terminal(Element):

    def __init__(self, name):
        self.name = str(name)
        printIt("CREATED new terminal " + self.name, LogLvl.debug)


    def __eq__(self, other):
        if isinstance(other, Terminal):
            return str(self) == str(self)
        return False


    def escape_name(self):
        escaped_name = self.name
        escaped_name = escaped_name.encode("unicode_escape").decode("utf-8")
        lit = "'"
        bs = "\\"
        escaped_name = escaped_name.replace(lit, bs + lit)
        return escaped_name


    def get_name(self):
        return self.name


    def print(self):
        return f"'{self.escape_name()}'"


def main(content, input_file):
    converter = FBG_to_ANTLR(input_file)
    converter.convert()
    antlr = converter.print()
    return antlr
