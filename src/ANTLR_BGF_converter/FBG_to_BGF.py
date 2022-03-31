import ast
import re
from xml.etree import ElementTree as ET
from fuzzingbook.Grammars import convert_ebnf_grammar

import base


class Terminal:

    def __init__(self, name):
        name = name.encode("unicode_escape").decode("utf-8")
        self.__name = name

    def get_BFG_xml(self):
        root = ET.Element("terminal")
        root.text = self.__name
        return root


class Nonterminal:

    def __init__(self, name):
        name = name.replace("<", "").replace(">", "")
        name = name.encode("unicode_escape").decode("utf-8")
        self.__name = name

    def get_BFG_xml(self):
        root = ET.Element("nonterminal")
        root.text = self.__name
        return root


def convert(tfbg):
    root = ET.Element("grammar")

    nt = "<start>"
    exp = tfbg["<start>"]

    production = create_production(nt, exp)
    root.append(production)

    for nonterminal, exp in tfbg.items():
        if nonterminal == "<start>":
            continue
        production = create_production(nonterminal, exp)
        root.append(production)

    return root


def create_production(nonterminal, expressions):
    root = ET.Element("production")
    nonterminal_name = nonterminal.replace("<", "").replace(">", "")
    nonterminal_name = nonterminal_name.encode("unicode_escape").decode("utf-8")  # needed for \n
    ET.SubElement(root, "nonterminal").text = nonterminal_name

    if len(expressions) == 1:
        exp = parse_expression(expressions[0])
        root.append(exp)
    else:  # if there are more then 1 expression we have to create a "choice" tag
        choice = ET.Element("choice")

        for exp in expressions:
            exp = parse_expression(exp)
            choice.append(exp)

        expression = ET.Element("expression")
        root.append(expression)
        expression.append(choice)

    return root


def parse_expression(expressions):
    nonterminals_and_terminals = []
    parsed_expressions = base.parse_FBG_rule(expressions)

    i = 0
    while i < len(parsed_expressions):
        non_terminal_object = None
        current_string = parsed_expressions[i]
        i += 1

        # if is nonterminal
        if base.is_nonterminal(current_string):
            name = re.fullmatch(base.re_token, current_string)
            if not name:
                continue
            name = name.string
            non_terminal_object = Nonterminal(name)

        # terminal
        else:
            name = current_string
            non_terminal_object = Terminal(name)

        nonterminals_and_terminals.append(non_terminal_object)

    root = ET.Element("expression")

    # epsilon
    if len(nonterminals_and_terminals) == 0:
        epsilon = ET.Element("epsilon")
        root.append(epsilon)

    # if its only 1 thing, we dont need a sequence
    elif len(nonterminals_and_terminals) == 1:
        root.append(nonterminals_and_terminals[0].get_BFG_xml())

    # if we have multiple things we need a sequence
    else:
        sequence = ET.Element("sequence")
        root.append(sequence)

        for expressions in nonterminals_and_terminals:
            x = ET.Element("expression")
            x.append(expressions.get_BFG_xml())
            sequence.append(x)

    return root


def main(content, input_path):
    dictionary = ast.literal_eval(content)
    bnf = convert_ebnf_grammar(dictionary)
    xml = convert(bnf)

    indent(xml)
    return ET.tostring(xml).decode()


###################################################################################################
###################################################################################################
###################################################################################################

def indent(elem, level = 0):
    # indent function for pretty print
    # source: https://stackoverflow.com/questions/66884296/python-3-save-the-output-of-elementtree-dump-to-xml-file
    i = "\n" + level * "  "
    j = "\n" + (level - 1) * "  "
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + "  "
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for subelem in elem:
            indent(subelem, level + 1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = j
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = j
    return elem
