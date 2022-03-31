import string
import sys
from xml.etree import ElementTree as ET
from base import *
import json

class BGF:

    def __init__(self):
        self.fbg = FBG()
        self.first_rule = None


    def parse_xml(self, xml):

        rules = self.pre_parse(xml)

        if len(rules) == 0:
            (start_nt, known) = self.fbg.create_nonterminal("start", False, False, False)
            assert not known
            self.fbg.start_nonterminal = start_nt

        for nt, exp_xmls in rules.items():

            for exp_xml in exp_xmls:
                exp = self.parse_expression(exp_xml, nt)

                # skipping for epsilon
                sk = ["epsilon", "{", "}", "+", "*", "?"]
                if nt.get_name() in sk and len(nt.get_body()) > 0:
                    continue

                for e in exp:
                    nt.add_expression(e)

        if len(self.fbg.start_nonterminal.get_body()) == 0:
            if isinstance(self.first_rule, str):
                (nt, known) = self.fbg.create_nonterminal(self.first_rule)
                assert known
            else:
                nt = self.first_rule
            self.fbg.start_nonterminal.add_expression(Expression([nt]))

        return self.fbg.print()


    def pre_parse(self, xml):
        rules = { }
        productions = []


        for ele in xml.findall("./"):
            if self.compare_tag(ele, "production"):
                productions.append(ele)
            elif self.compare_tag(ele, "root"):
                self.first_rule = ele.text

        for production in productions:
            t = production.findall("./")

            offset = 0
            if len(t) == 3:
                offset = 1
            prod = t[offset + 0]
            exp = t[offset + 1]

            nt_name = prod.text

            ##### creating nonterminals, adding expressions to list
            (nt, known) = self.fbg.create_nonterminal(nt_name, False, False, False, True)

            if not self.first_rule:
                self.first_rule = nt

            if not self.fbg.start_nonterminal and nt_name == "start":
                self.fbg.start_nonterminal = nt

            if nt in rules:
                rules[nt].append(exp)

            else:
                rules[nt] = [exp]

        if not self.fbg.start_nonterminal:
            (start_nt, known) = self.fbg.create_nonterminal("start", False, False, False)
            assert not known

        return rules


    def compare_tag(self, xml, tag):
        xmlns = "{" + xml.tag.split('}')[0].strip('{') + "}"

        boo = xml.tag == xmlns + tag or xml.tag == tag
        return boo


    def parse_production(self, xml, current_nonterminal = None):
        fnd = "./"

        for production in xml.findall(fnd):
            if self.compare_tag(production, "nonterminal"):
                current_nonterminal = production.text
                self.fbg.create_nonterminal(current_nonterminal, False, False, False)


            elif self.compare_tag(production, "expression"):
                expression = self.parse_expression(production, current_nonterminal)
                assert current_nonterminal is not None

            elif self.compare_tag(production, "label"):
                pass

            else:
                raise AttributeError(f"Unknown production '{production.tag}' ")


    def parse_expression(self, xml, current_nonterminal) -> list:
        expression = []
        for production in xml.findall("./"):

            if self.compare_tag(production, "epsilon"):
                e = self.parse_epsilon(production, current_nonterminal)
                expression.append(e)

            elif self.compare_tag(production, "empty"):
                # value = parse_expression(production, current_nonterminal, parsed_grammar)
                # https://slebok.github.io/zoo/doc/ldf/v20.0-xsd/extracted/index.html
                e = self.parse_epsilon(production, current_nonterminal)
                expression.append(e)

            elif self.compare_tag(production, "value"):
                value = self.parse_value(production, current_nonterminal)
                expression.append(value)

            elif self.compare_tag(production, "any") or self.compare_tag(production, "anything"):
                raise UnicodeError("Feature not implemented, becaus we never found a a grammar using this.")
                # https://slebok.github.io/zoo/doc/ldf/v20.0-xsd/extracted/index.html
                t = Terminal(".")
                expression = [t]


            elif self.compare_tag(production, "terminal"):
                terminal = production.text
                # if <terminal></terminal> then production.text is None
                #  But it should be " "
                #  see: https://slebok.github.io/zoo/markup/textual/csv/bucknall/extracted/index.html
                if terminal is None:
                    terminal = " "

                terminal = terminal.replace("\\a", "\a")
                terminal = terminal.replace("\\b", "\b")
                terminal = terminal.replace("\\t", "\t")
                terminal = terminal.replace("\\n", "\n")
                terminal = terminal.replace("\\v", "\v")
                terminal = terminal.replace("\\f", "\f")
                terminal = terminal.replace("\\r", "\r")

                exp = self.fbg.create_terminal(terminal)
                expression.append(exp)

            elif self.compare_tag(production, "nonterminal"):
                nt_name = production.text
                try:
                    (nt, known) = self.fbg.create_nonterminal(nt_name)
                except ReferenceError as e:
                    (nt, known) = self.fbg.create_nonterminal(nt_name, False)
                    if nt_name == "DQUOTE":
                        nt.add_expression(Expression([Terminal("\"")]))
                    elif nt_name == "TDQUOTE":
                        nt.add_expression(Expression([Terminal("\"")]))
                    elif nt_name == "Double":
                        wrp = self.fbg.create_nonterminal_from_char_lst(string.digits, "lst_DIGITS")
                        if not known:
                            e1 = Expression()
                            e1.append(wrp)
                            e1.append(EBNF("+"))

                            nt.add_expression(e1)
                            e2 = Expression()
                            e2.append(e1)
                            e2.append(Terminal("."))
                            e2.append(e1)
                            nt.add_expression(e2)
                    elif nt_name == "SimpleTextElement":
                        txt = self.fbg.create_nonterminal_from_char_lst(string.ascii_letters + string.digits,
                                                                        "lst_SimpleTextElement"
                                                                        )
                        (do, _) = self.fbg.create_nonterminal("SimpleTextElement", False)
                        if not known:
                            e = Expression()
                            e.append(txt)
                            e.append(EBNF("+"))
                            nt.add_expression(e)

                    else:
                        # nt.add_expression(Expression([Terminal(nt_name)]))
                        raise e  # used but not defined = invalid grammar
                expression = Expression([nt])


            elif self.compare_tag(production, "selectable"):
                value = self.parse_selectable(production, current_nonterminal)
                expression = value


            elif self.compare_tag(production, "sequence"):
                value = self.parse_sequence(production, current_nonterminal)
                expression.append(value)


            elif self.compare_tag(production, "choice"):
                value = self.parse_choice(production, current_nonterminal)
                expression = value


            elif self.compare_tag(production, "allof"):
                raise NotImplementedError("allof is not supported.")
                # https://github.com/slebok/zoo/blob/master/zoo/doc/wiki/mediawiki/bnf/connected/grammar.bgf
                # http://slebok.github.io/zoo/doc/wiki/mediawiki/bnf/connected/index.html
                # value = self.parse_sequence(production, current_nonterminal)
                #expression.append(value)


            elif self.compare_tag(production, "marked") or self.compare_tag(production, "mark"):
                ##### ignore mark, parse rest
                m = production.findall("./")
                assert len(m) == 2  # first is marked, second is expression
                marked = m[0]
                expession = m[1]

                expression = (self.parse_expression(expession, current_nonterminal))


            elif self.compare_tag(production, "optional"):
                value = self.parse_optional(production, current_nonterminal)
                expression.append(value)

            elif self.compare_tag(production, "not"):
                # raise NotImplementedError
                # value = self.parse_not(production, current_nonterminal)
                value = self.parse_optional(production, current_nonterminal)
                expression.append(value)


            elif self.compare_tag(production, "plus"):
                value = self.parse_plus(production, current_nonterminal)
                expression.append(value)

            elif self.compare_tag(production, "star"):
                value = self.parse_star(production, current_nonterminal)
                expression = value

            elif self.compare_tag(production, "seplistplus"):
                value = self.parse_seplistplus(production, current_nonterminal)
                expression = value


            elif self.compare_tag(production, "sepliststar"):
                value = self.parse_sepliststar(production, current_nonterminal)
                expression = value


            else:
                raise SyntaxError(f"Unknown expression '{production.tag}'")

        return expression


    def parse_value(self, xml, current_nonterminal):

        if xml.text == "int":
            nt = self.fbg.create_nonterminal_from_char_lst(string.digits, "[0-9]")
            return Expression([nt, EBNF("+")])
        elif xml.text == "string":
            nt = self.fbg.create_nonterminal_from_char_lst(string.ascii_lowercase, "[a-z]")
            return Expression([nt, EBNF("+")])
        elif xml.text == "boolean":
            nt = self.fbg.create_nonterminal_from_char_lst(["0", "1"], "boolean")
            return Expression([nt])
        else:
            raise Exception(f"No valid value: '{xml.text}'")


    def parse_EBNF_star_und_so_name_todo(self, xml, current_nonterminal, ebnf_char):

        assert (ebnf_char in ["+", "*", "?", "~"])
        assert (len(list(xml)) == 1 and self.compare_tag(list(xml)[0], "expression"))
        exp = list(xml)
        expressions = self.parse_expression(exp[0], current_nonterminal)
        # if len(ex) > 1 then we have multible (non)terminals that must be in brackets. this is not supportet by FBL.
        # So we need to create an new nonterminal to support this feature

        fnd = "./"
        tmp = exp[0].findall(fnd)
        tag = tmp[0].tag

        if isinstance(expressions, Expression):
            expressions = [expressions]

        if isinstance(expressions, list):

            nt_name = "lst_"
            exp = Expression()
            for e in expressions:
                nt_name += e.get_name() + "|"

            nt_name = nt_name[:-1]

            (nt, known) = self.fbg.create_nonterminal(nt_name, False)

            if not known:
                for e in expressions:
                    nt.add_expression(e)

            nt_wrp = self.fbg.create_nonerminal_wrapper(nt)
            e = Expression()
            e.append(nt_wrp)
            e.append(Expression([EBNF(ebnf_char)]))
            e2 = Expression()
            e2.append(e)

            return e2
        else:
            assert False


    def parse_epsilon(self, xml, current_nonterminal):
        (nt, known) = self.fbg.create_nonterminal("epsilon", False)
        if not known or current_nonterminal.get_name() == "epsilon":
            nt.add_expression(Expression([Terminal("")]))

        wrp_nt = self.fbg.create_nonerminal_wrapper(nt)

        return wrp_nt


    # [star]::[expr]::BGFExpression
    def parse_star(self, xml, current_nonterminal):
        return self.parse_EBNF_star_und_so_name_todo(xml, current_nonterminal, "*")


    def parse_plus(self, xml, current_nonterminal):
        return self.parse_EBNF_star_und_so_name_todo(xml, current_nonterminal, "+")


    def parse_optional(self, xml, current_nonterminal):
        return self.parse_EBNF_star_und_so_name_todo(xml, current_nonterminal, "?")


    def parse_not(self, xml, current_nonterminal):
        return self.parse_EBNF_star_und_so_name_todo(xml, current_nonterminal, "?")


    # [sequence]::[exprs]::BGFExprList
    def parse_sequence(self, xml, current_nonterminal):
        output = Expression()
        tmp = ""

        t = list()
        for expression in list(xml):
            t.append(expression)
        for expression in list(xml):
            assert (self.compare_tag(expression, "expression"))
            parsed_expression = self.parse_expression(expression, current_nonterminal)
            sub_sexpression = expression.findall("./")[0]
            assert len(parsed_expression) > 0

            if self.compare_tag(sub_sexpression, "choice"):
                assert len(parsed_expression) > 1
                nt_wrp = self.fbg.create_nonterminal_from_expression_lst(parsed_expression)
                output.append(nt_wrp)

            else:
                for el in parsed_expression:
                    output.append(el)

        return output


    # [selectable]::([selector]::string [expr]::BGFExpression)
    def parse_selectable(self, xml, current_nonterminal):
        tmp = []
        for ele in list(xml):
            if self.compare_tag(ele, "expression"):
                exp = self.parse_expression(ele, current_nonterminal)
            elif self.compare_tag(ele, "selector"):
                # pass because this is only a label
                exp = ""
            else:
                raise Exception("selectable contains an invalid child '" + ele.tag + "'.")

            for xp in exp:
                tmp.append(xp)

        return tmp


    # [choice]::[exprs]::BGFExprList
    def parse_choice(self, xml, current_nonterminal):
        output = list()
        for ele in list(xml):
            assert (self.compare_tag(ele, "expression"))
            exp = self.parse_expression(ele, current_nonterminal)
            for i in exp:
                output.append(i)
        return output


    def parse_seplistplus(self, xml, current_nonterminal):
        lst = xml.findall("./")
        assert (len(lst) == 2)
        assert (self.compare_tag(lst[0], "expression"))
        assert (self.compare_tag(lst[1], "expression"))
        expl1 = self.parse_expression(lst[0], current_nonterminal)
        expl2 = self.parse_expression(lst[1], current_nonterminal)
        assert (len(expl1) == 1)
        assert (len(expl2) == 1)

        new_nonterminal_name = expl1[0].get_name() + "|" + expl2[0].get_name()

        (nt, known) = self.fbg.create_nonterminal(new_nonterminal_name, False)

        if not known:
            e = Expression([expl1[0], expl2[0]])
            nt.add_expression(e)

        e = Expression()
        e.append(nt)
        e.append(Expression([EBNF('+')]))
        e2 = Expression()
        e2.append(e)

        return e2


    def parse_sepliststar(self, xml, current_nonterminal):
        lst = xml.findall("./")
        assert (len(lst) == 2)
        assert (self.compare_tag(lst[0], "expression"))
        assert (self.compare_tag(lst[1], "expression"))
        expl1 = self.parse_expression(lst[0], current_nonterminal)
        expl2 = self.parse_expression(lst[1], current_nonterminal)
        assert (len(expl1) == 1)
        assert (len(expl2) == 1)

        new_nonterminal_name = expl1[0].get_name() + "|" + expl2[0].get_name()

        (nt, known) = self.fbg.create_nonterminal(new_nonterminal_name, False)

        if not known:
            e = Expression([expl1[0], expl2[0]])
            nt.add_expression(e)

        e = Expression()
        e.append(nt)
        e.append(Expression([EBNF('+')]))
        e2 = Expression()
        e2.append(e)

        return e2


def main(content, input_file):
    sys.setrecursionlimit(5000)

    bgf = BGF()
    try:
        tree = ET.parse(input_file)
        root = tree.getroot()
    except Exception as e:
        raise AttributeError("Invalid xml")
    fbl = bgf.parse_xml(root)

    return fbl


# -----------------------------------------------------------------------------------
# -----------------------------DEBUG STUFF-------------------------------------------
# -----------------------------------------------------------------------------------
def debug_print_xml_object(xml):
    print(ET.tostring(xml, encoding = 'utf8').decode('utf8'))


def debug_print_xml_object_list(xml):
    for obj in xml:
        print("------------------BEGIN------------------")
        debug_print_xml_object(obj)
        print("-------------------END-------------------")
