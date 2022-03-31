import re
import string
import sys
import json
import ast
import copy
import tempfile
import subprocess
import os
import hashlib
# using regex instead of the default re lib to support more unicode features
import regex as reg
from pyparsing import unicode
import unicodedata
from antlr4 import *
from base import *

from bin.ANTLRv4Lexer import ANTLRv4Lexer as MyLexer
from bin.ANTLRv4Parser import ANTLRv4Parser as MyParser


check_if_is_valid_antlr = False


class AntlrG:

    def __init__(self, content, input_file, is_main_grammar = False):
        self.fbg = FBG()
        self.__antlr_options = { }
        self.__working_dir = os.path.dirname(os.path.abspath(input_file))
        self.__file_name = os.path.basename(input_file)
        self.import_chain = []
        self.is_main_grammar = is_main_grammar

        self.__enable_skip = True

        ###
        # if true, ignore all channel features
        # raise no exception and throw all channel stuff away
        # also affects all sub-features:
        # https://github.com/antlr/antlr4/blob/master/doc/lexer-rules.md#mode-pushmode-popmode-and-more
        self.__ignore_channels = True

        # if ture, ignore all unknown options
        # raise no exception, throw them away
        self.__ignore_unknown_options = True

        # if true, ignore all action blocks used by lexer rules.
        # raise no exception and throw the whole action block part away, just using the rule without it
        self.__ignore_lexer_rule_actions = True

        # if true, ignore all action blocks used by parser rules.
        # raise no exception and throw the whole action block part away, just using the rule without it
        self.__ignore_parser_rule_actions = True

        # if true, ignore the type feature https://github.com/antlr/antlr4/blob/master/doc/lexer-rules.md#type
        # raise no exception and throw the feature away
        # THIS IS NOT A LEXER GRAMMAR; its the feautre called type, only unsable in lexer rules.
        self.__ignore_lexer_type = True

        self.__ignore_lexer_more = True

        self.__ignore_unicode_errors = True
        ###

        self.__ignore_pre_action_blocks = True
        self.__warn_about_pre_action_blocks = True
        ###

        # for testing only!
        self.__using_gramminator_logic = False

        printIt(f"Reading in {input_file}...", LogLvl.debug)
        if content:
            code = content
        else:
            code = read_file_in(input_file)

        # create lexer and parser with the help of ANTLR
        (self.lexer, self.parser, self.tree) = self.create_lexer_parser_and_tree(code)

        ###########################################
        using_unicode = False
        if using_unicode:
            # for speedup a pre-generate a list with all unicode chars:
            # skipping surrogates range 0x800 - DFFF
            self.__lst_all_unicode = [chr(x) for x in range(0x0001, 0x0800)]
            self.__lst_all_unicode = [chr(x) for x in range(0x0000, 0x10FFFF)]
            self.__lst_all_unicode.extend([chr(x) for x in range(0xE000, 0x10FFFF)])
            self.__lst_all_unicode = ''.join(self.__lst_all_unicode)
        else:
            self.__lst_all_unicode = string.printable
        ###########################################


    def start_converting(self):
        self.import_chain.append(self.__working_dir + "/" + self.__file_name)
        rule_list = self.explore_NTs(self.tree)
        self.convert(rule_list)


    def convert(self, rule_list):
        self.pre_create_nts(rule_list)
        self.convert_rules(rule_list)


    def get_name_of_first_nonterminal(self):
        self.import_chain.append(self.__working_dir + "/" + self.__file_name)
        rule_list = self.explore_NTs(self.tree)
        (name, _) = self.get_name_from_Rule_Spec_Context(rule_list[0])
        return name


    def explore_NTs(self, tree, is_tokenVocab = False):
        parsedtree = tree.children

        children = copy.copy(parsedtree)
        # if there are doc_comments, skip them first
        _o, children = self._parse_star_token(children, self.lexer.DOC_COMMENT)
        self.parse_DOC_COMMENT_star(_o)
        # get grammar name and check if its lexer, parser or both
        _o, children = self._parse_object(children, self.parser.GrammarDeclContext)
        self.grammar_type, self.grammar_name = self.parse_grammarDecl(_o)
        # parse options
        _o, children = self._parse_star_object(children, self.parser.PrequelConstructContext)
        options = self.parse_prequelConstruct(_o)
        # parse and convet lexer and parser rules
        rules, children = self._parse_object(children, self.parser.RulesContext)
        rule_list, _ = self._parse_star_object(copy.copy(rules.children), self.parser.RuleSpecContext)

        _o, children = self._parse_star_object(children, self.parser.ModeSpecContext)
        mode_rules = self.parse_modeSpec_star(_o)

        rule_list.extend(mode_rules)

        _o, children = self._parse_token(children, self.parser.EOF)
        self.parse_EOF(_o)

        if not is_tokenVocab:
            self.handle_tokenVocab(options)

        return rule_list


    def get_name_from_Rule_Spec_Context(self, rule):
        name = None
        parser_cnt = 0
        lexer_cnt = 0
        is_lexer_rule = False

        if isinstance(rule, self.parser.RuleSpecContext):
            rule = rule.children
            assert len(rule) == 1
            rule = rule[0]

        if isinstance(rule, self.parser.ParserRuleSpecContext):
            # Parser rule
            ch = copy.copy(rule.children)
            _, ch = self._parse_star_token(ch, self.lexer.DOC_COMMENT)
            _, ch = self._parse_question_object(ch, self.parser.RuleModifiersContext)
            assert isinstance(ch[0], tree.Tree.TerminalNodeImpl)
            _o = ch[0]
            assert _o.symbol.type == self.lexer.RULE_REF
            name = self.parse_RULE_REF(_o)

        elif isinstance(rule, self.parser.LexerRuleSpecContext):
            # Lexer rule
            is_lexer_rule = True
            ch = rule.children
            _, ch = self._parse_star_token(ch, self.lexer.DOC_COMMENT)
            _, ch = self._parse_question_token(ch, self.lexer.FRAGMENT)
            assert isinstance(ch[0], tree.Tree.TerminalNodeImpl)
            _o = ch[0]
            assert _o.symbol.type == self.lexer.TOKEN_REF
            name = self.parse_TOKEN_REF(_o)
        else:
            assert False

        return (name, is_lexer_rule)


    def pre_create_nts(self, rule_list):
        for rule in rule_list:

            (name, is_lexer_rule) = self.get_name_from_Rule_Spec_Context(rule)

            start_nt = None
            if self.is_main_grammar and not self.fbg.start_nonterminal and not is_lexer_rule:
                (start_nt, known) = self.fbg.create_nonterminal("start", False, False, False)
                assert not known

            (nt, known) = self.fbg.create_nonterminal(name, False, False, False)
            if start_nt:
                start_nt.add_expression(nt)

        if len(self.__antlr_options) > 0:
            printIt(f'Found options: {self.__antlr_options}', LogLvl.debug)


    def create_lexer_parser_and_tree(self, content):
        lexer = MyLexer(InputStream(content))
        tokenStream = CommonTokenStream(lexer)
        parser = MyParser(tokenStream)
        parser.buildParseTrees = True
        tree = parser.grammarSpec()

        return (lexer, parser, tree)


    def handle_tokenVocab(self, options):
        if not options or "tokenVocab" not in options:
            return

        file_name = f'{options["tokenVocab"]}.g4'

        file_path = self.__working_dir + '/' + file_name

        content = read_file_in(file_path)

        (lexer, parser, tree) = self.create_lexer_parser_and_tree(content)

        rule_list = self.explore_NTs(tree, True)
        self.convert(rule_list)


    def _parse_token(self, children, typ):
        # printIt("_parse_token")
        assert isinstance(children[0], tree.Tree.TerminalNodeImpl)
        tok = children.pop(0)
        assert tok.symbol.type == typ
        return tok, children


    def _parse_object(self, children, typ):
        # printIt("_parse_object")
        assert isinstance(children[0], typ)
        obj = children.pop(0)
        return obj, children


    # checks for each children if the pred is true and returns a list with all positiv objects
    def _parse_list(self, children, pred, atmost = -1, atleast = 0):
        # printIt("_parse_list")
        lst = []
        while children:
            if atmost == 0:
                break
            atmost -= 1
            if pred(children[0]):
                obj = children.pop(0)
                lst.append(obj)
            else:
                break
        assert len(lst) >= atleast
        return lst, children


    def _parse_question(self, children, pred):
        # printIt("_parse_question")
        return self._parse_list(children, pred, atmost = 1)  # a maximum of one


    def _parse_star(self, children, pred):
        # printIt("_parse_star")
        return self._parse_list(children, pred)


    def _parse_star_object(self, children, typ):
        # printIt("_parse_star_object")
        return self._parse_star(children, lambda x: isinstance(x, typ))


    def _parse_list_x(self, children, pred_inside, atmost = -1):
        # printIt("_parse_list_x")
        # eat children in chunks
        res = []
        while children:
            if atmost == 0:
                break
            atmost -= 1
            _children = copy.copy(children)
            _o, _remaining = pred_inside(_children)
            if _o is None:
                break  # children is not touched
            children = _remaining
            res.append(_o)
        return res, children


    def _parse_question_x(self, children, pred_inside):
        # printIt("_parse_question_x")
        return self._parse_list_x(children, pred_inside, atmost = 1)


    def _parse_star_x(self, children, pred_inside):
        # printIt("_parse_star_x")
        return self._parse_list_x(children, pred_inside)


    def _parse_star_token(self, children, typ):
        # printIt("_parse_star_token")
        a = self._parse_list(children, lambda x: isinstance(x, tree.Tree.TerminalNodeImpl) and x.symbol.type == typ)
        return self._parse_list(children, lambda x: isinstance(x, tree.Tree.TerminalNodeImpl) and x.symbol.type == typ)


    def _parse_question_object(self, children, typ):
        # printIt("_parse_question_object")
        return self._parse_question(children, lambda x: isinstance(x, typ))


    def _parse_question_token(self, children, typ):
        # printIt("_parse_question_token")
        return self._parse_question(children,
                                    lambda x: isinstance(x, tree.Tree.TerminalNodeImpl) and x.symbol.type == typ
                                    )


    def parse_DOT(self, obj):
        printIt("parse_DOT", LogLvl.function_calls)
        assert isinstance(obj, tree.Tree.TerminalNodeImpl)
        assert obj.symbol.text == "."
        lst = srange(string.printable)
        return self.fbg.create_nonterminal_from_char_lst(lst, "wildcard_dot")


    def expand_charset_by_loop(self, start_char, end_char, obj):
        # convert unicode ranges from ANTLR like \uxxxxx
        if start_char.find("\\u") != -1:
            start_char = bytes(start_char, 'ascii')
            start_char = start_char.decode('unicode-escape')

        if end_char.find("\\u") != -1:
            end_char = bytes(end_char, 'ascii')
            end_char = end_char.decode('unicode-escape')

        try:
            start = ord(start_char)
            stop = ord(end_char)
        except:
            return [start_char, end_char]

        lst = []
        for i in range(start, stop + 1):
            lst.append(chr(i))

        return lst


    def expand_charset_by_regex(self, charset, obj):

        all = ""
        if charset == ".":
            all = self.__lst_all_unicode
        else:
            all = self.__lst_all_unicode

        try:
            result = reg.findall(charset, all)
        except Exception as E:
            printUnimplemented("Charset", obj, charset)
            raise E
            # return reg.findall(".", string.printable)


        if len(result) == 0:
            result.append("")

        return result


    def parse_LEXER_CHAR_SET(self, obj) -> Nonterminal:
        printIt("parse_LEXER_CHAR_SET", LogLvl.function_calls)

        expression = obj.symbol.text
        assert (expression[0], expression[-1]) == ("[", "]")
        nt_name = expression.encode().decode('unicode-escape')

        range = expression[1:-1]

        try:
            escp = range.replace('\"', '\\\"')
            # replace the sequenc \] with only ] because its a range and in the ANTLR format
            # the ] must be escaped
            # escp = range.replace('\\]', ']')
            range = '{ "c": "' + escp + '"}'

            range = ast.literal_eval(range)
            range = range["c"]

        except SyntaxError as E:

            if "unicode error" in E.msg:
                raise E
                # likely the grammar uses a privat unicode range that we can not convert
            else:
                raise E

        lst = []

        ranges_unicode_class = re.findall(r"\\p\{.*?}", range)
        for r in ranges_unicode_class:
            # re.findall(r'\p{P}+', lst_all_unicode)
            range = range.replace(r, "")
            if self.__ignore_unicode_errors:
                printUnimplemented("Unicode character classes", obj, None, "Ignore it.")
            else:
                raise NotImplementedError("Unicode character classes")

        ranges_ascii = re.findall(r".{1}-.{1}", range)  # is like a-z or 0-9
        for r in ranges_ascii:
            a = r[0:2]
            if r[0:2] == "\\-":
                # skip because - is escaped
                continue
            range = range.replace(r, "")

            assert len(r) == 3 and r[1] == "-"  # like a-z or 0-9
            start = r[0]
            stop = r[-1]
            lst.extend(self.expand_charset_by_loop(start, stop, obj))

        ### ANTLR doc:
        ### DASHBRACK : [\-\]]+ ; // match - or ] one or more times
        range = range.replace("\\-", "-")
        lst.extend(srange(range))

        return self.fbg.create_nonterminal_from_char_lst(lst, nt_name)


    def parse_COMMA(self, obj):
        printIt("parse_COMMA", LogLvl.function_calls)
        assert obj.symbol.text == ','
        return ','


    def parse_QUESTION(self, obj):
        printIt("parse_QUESTION", LogLvl.function_calls)
        assert obj.symbol.text == '?'
        return '?'


    def parse_STAR(self, obj):
        printIt("parse_STAR", LogLvl.function_calls)
        assert obj.symbol.text == '*'
        return '*'


    def parse_PLUS(self, obj):
        assert obj.symbol.text == '+'
        return '+'


    def parse_NOT(self, obj):
        assert obj.symbol.text == '~'
        return '~'


    def parse_RARROW(self, obj):
        assert obj.symbol.text == '->'
        return '->'


    def parse_LPAREN(self, obj):
        assert obj.symbol.text == '('
        return '('


    def parse_RPAREN(self, obj):
        assert obj.symbol.text == ')'
        return ')'


    def parse_EOF(self, obj):
        assert obj.symbol.text == '<EOF>'
        return None


    def parse_prequelConstruct(self, obj):
        """
        prequelConstruct
           : optionsSpec
           | delegateGrammars
           | tokensSpec
           | channelsSpec
           | action_
           ;
        """

        options = None

        if len(obj) == 0:  # no options here
            return
        for o in obj:
            assert isinstance(o, self.parser.PrequelConstructContext)
            children = o.children
            assert len(children) == 1
            o = children[0]

            if isinstance(o, self.parser.OptionsSpecContext):
                # e.g. options { superClass = LexerAdaptor; }
                o, children = self._parse_object(children, self.parser.OptionsSpecContext)
                options = self.parse_optionSpecContect(o)

            elif isinstance(o, self.parser.Action_Context):
                # e.g.
                # @parser::postinclude {
                # #include <PlSqlParserBase.h>
                # }
                o, children = self._parse_object(children, self.parser.Action_Context)
                if not self.__ignore_pre_action_blocks:
                    raise NotImplementedError("action block")
                if self.__warn_about_pre_action_blocks:
                    printUnimplemented("Action_Context", o, None, "Ignore it.")

            elif isinstance(o, self.parser.ChannelsSpecContext):
                # e.g. channels { OFF_CHANNEL , COMMENT }
                o, children = self._parse_object(children, self.parser.ChannelsSpecContext)
                if self.__ignore_channels:
                    printUnimplemented("Channels", o, None, "Ignore it.")
                else:
                    raise NotImplementedError('Channels')

            elif isinstance(o, self.parser.DelegateGrammarsContext):
                # import feature
                o, children = self._parse_object(children, self.parser.DelegateGrammarsContext)
                assert not children
                children = o.children
                o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
                assert o.symbol.text == "import"
                while len(children) >= 2:
                    o, children = self._parse_object(children, self.parser.DelegateGrammarContext)
                    o, ch = self._parse_object(o.children, self.parser.IdentifierContext)
                    assert not ch
                    sep, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
                    assert sep.symbol.text in [",", ";"]

                    o_import_name, c = self._parse_object(o.children, tree.Tree.TerminalNodeImpl)
                    assert not c

                    import_name = o_import_name.symbol.text
                    grammar_file = f'{import_name}.g4'
                    path = self.__working_dir + "/" + grammar_file

                    g = AntlrG(None, path)
                    g.import_chain = self.import_chain
                    if path not in g.import_chain:
                        g.start_converting()
                        self.fbg.import_fbl(g.fbg)
                        # self.fbg = g.fbg

                assert len(children) == 0

            elif isinstance(o, self.parser.TokensSpecContext):
                # e.g. tokens { TOKEN_REF , RULE_REF , LEXER_CHAR_SET }
                o, _ = self._parse_object(children, self.parser.TokensSpecContext)

                o, children = self._parse_object(o.children, tree.Tree.TerminalNodeImpl)
                o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
                tokens = children.pop(0)
                tokens = tokens.children
                o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)

                token_list = []

                while len(tokens) > 1:
                    o, children = self._parse_object(tokens, self.parser.IdentifierContext)
                    name = o.children[0].symbol.text
                    token_list.append(name)
                    o, children = self._parse_object(tokens, tree.Tree.TerminalNodeImpl)

                tokens = children.pop(0)
                name = tokens.children[0].symbol.text
                token_list.append(name)

                for token in token_list:
                    (nt, known) = self.fbg.create_nonterminal(token, False)
                    nt.add_expression(Expression([Terminal("")]))

        return options


    def parse_optionSpecContect(self, obj):
        antlr_options = { }
        children = obj.children
        o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
        assert o.symbol.text == "options"
        o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
        assert o.symbol.text == '{'
        while len(children) > 2:
            o, children = self._parse_object(children, self.parser.OptionContext)
            antlr_options = self.parse_option(o, antlr_options)
            o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
            assert o.symbol.text in [';', '}']
        if len(children) == 1:
            o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
            assert o.symbol.text == '}'
        assert len(children) == 0

        return antlr_options


    def parse_option(self, obj, antlr_options):
        children = copy.copy(obj.children)
        o, children = self._parse_object(children, self.parser.IdentifierContext)
        o = o.children[0]
        assert isinstance(o, tree.Tree.TerminalNodeImpl)
        variable_name = o.symbol.text

        o, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
        assert isinstance(o, tree.Tree.TerminalNodeImpl)
        assert o.symbol.text == '='

        o, children = self._parse_object(children, self.parser.OptionValueContext)
        assert len(children) == 0

        children = o.children
        o, children = self._parse_object(children, self.parser.IdentifierContext)
        assert len(o.children) == 1
        o = o.children[0]
        assert isinstance(o, tree.Tree.TerminalNodeImpl)

        variable_value = o.symbol.text

        if variable_name in antlr_options:
            raise AttributeError(f'Duplicate option name "{variable_name}"')

        if variable_name != "tokenVocab":
            if self.__ignore_unknown_options:
                printUnimplemented("Charset", o, None, f' Ignoring unknown option "{variable_name}"')
            else:
                raise NotImplementedError(f'Option "{variable_name}" is not supported.')

        antlr_options[variable_name] = variable_value

        return antlr_options


    def parse_DOC_COMMENT_star(self, o):
        return None


    def parse_modeSpec_star(self, obj):
        rule_list = []
        try:
            for mode in obj:
                rules = self.parse_modSpec(mode)
                rule_list.extend(rules)
        except:
            pass
        return rule_list


    def parse_modSpec(self, obj):
        # mode
        # $mode_name
        # ;
        # lexer rules*
        assert isinstance(obj, self.parser.ModeSpecContext)
        children = obj.children
        mode, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
        mode_name, children = self._parse_object(children, self.parser.IdentifierContext)

        mode_name, rest = self._parse_object(mode_name.children, tree.Tree.TerminalNodeImpl)
        # assert len(rest) == 0
        mode_name = mode_name.symbol.text

        semicolon, children = self._parse_object(children, tree.Tree.TerminalNodeImpl)
        assert (semicolon.symbol.text == ";")

        return children
        for rule in children:
            self.parse_lexerRuleSpec(rule)


    def parse_grammarType(self, obj):
        '''
        grammarType
           : (LEXER GRAMMAR | PARSER GRAMMAR | GRAMMAR)
          ;
        '''
        children = copy.copy(obj.children)
        if not children:
            return "Unknown"
        kind = 'Both'
        if len(children) == 2:
            c = children.pop(0)
            if isinstance(c, tree.Tree.TerminalNodeImpl):
                if c.symbol.type == self.lexer.LEXER:
                    kind = 'Lexer'
                elif c.symbol.type == self.lexer.PARSER:
                    kind = 'Parser'
                else:
                    assert False
        _o, children = self._parse_token(children, self.lexer.GRAMMAR)
        assert not children
        return kind


    def parse_grammarDecl(self, obj):
        # SKIPPED
        '''
        grammarDecl
           : grammarType identifier SEMI
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_object(children, self.parser.GrammarTypeContext)
        gtype = self.parse_grammarType(_o)
        _o, children = self._parse_object(children, self.parser.IdentifierContext)
        idname = self.parse_identifier(_o)
        _o, children = self._parse_token(children, self.lexer.SEMI)
        assert _o
        assert not children
        return (gtype, idname)


    def convert_rules(self, rules):
        for rule in rules:
            self.parse_ruleSpec(rule)


    def parse_ruleSpec(self, ruleSpec):
        '''
        ruleSpec
           : parserRuleSpec
           | lexerRuleSpec
           ;
        '''
        if isinstance(ruleSpec, self.parser.RuleSpecContext):
            children = ruleSpec.children
            assert len(children) == 1
            ruleSpec = children[0]

        if isinstance(ruleSpec, self.parser.ParserRuleSpecContext):
            return self.parse_parserRuleSpec(ruleSpec)
        elif isinstance(ruleSpec, self.parser.LexerRuleSpecContext):
            return self.parse_lexerRuleSpec(ruleSpec)
        else:
            assert False


    ####################################################################################
    ###############################    PARSER     ######################################
    ####################################################################################

    def parse_parserRuleSpec(self, rspec):
        '''
        parserRuleSpec
           : DOC_COMMENT* ruleModifiers? RULE_REF argActionBlock? ruleReturns? throwsSpec? localsSpec? rulePrequel* COLON ruleBlock SEMI exceptionGroup
           ;
        '''
        expression_list = None
        children = copy.copy(rspec.children)
        # parse and ignore
        _o, children = self._parse_star_token(children, self.lexer.DOC_COMMENT)
        self.parse_DOC_COMMENT_star(_o)

        _o, children = self._parse_question_object(children, self.parser.RuleModifiersContext)  # a maximum of one
        self.parse_ruleModifiers_question(_o)

        _o, children = self._parse_token(children, self.lexer.RULE_REF)
        name = self.parse_RULE_REF(_o)
        (nt, _) = self.fbg.create_nonterminal(name)

        _o, children = self._parse_question_object(children, self.parser.ArgActionBlockContext)
        _o, children = self._parse_question_object(children, self.parser.RuleReturnsContext)
        _o, children = self._parse_question_object(children, self.parser.ThrowsSpecContext)
        _o, children = self._parse_question_object(children, self.parser.LocalsSpecContext)
        _o, children = self._parse_star_object(children, self.parser.RulePrequelContext)

        _o, children = self._parse_token(children, self.lexer.COLON)
        _o, children = self._parse_object(children, self.parser.RuleBlockContext)
        printIt("\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>", LogLvl.debug)
        printIt("PARSING PARSER RULE: " + nt.get_name(), LogLvl.debug)
        ### parserRuleBlock
        r, c = self._parse_object(copy.copy(_o.children), self.parser.RuleAltListContext)
        assert not c
        expression_list = self.parser_parseRule(r)

        if expression_list:
            for e in expression_list:
                nt.add_expression(e)

        else:
            printIt(
                    f"Ignoring nonterminal '{nt.get_name()}' because it has no content. Maybe it contais only non supported features.",
                    LogLvl.warning
                    )

        _o, children = self._parse_token(children, self.lexer.SEMI)
        _o, children = self._parse_object(children, self.parser.ExceptionGroupContext)

        # ExceptionGroupContext is the Catching Exceptions feature, we ignore it


    # ral is the whole expression of 1 rule
    def parser_parseRule(self, obj):
        printIt("parser_parseRule", LogLvl.function_calls, obj)
        '''
        ruleAltList
           : labeledAlt (OR labeledAlt)*
           ;
        '''


        # a define with multiple rules
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.OR)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.LabeledAltContext)
            if not _o:
                return None, children
            return _o[0], children


        children = copy.copy(obj.children)
        first_part = children.pop(0)
        alt_list = [first_part]

        remaining_part, children = self._parse_star_x(children, pred_inside)
        alt_list.extend(remaining_part)

        parsed_expressions = []
        for c in alt_list:
            parsed_part = self.parser_part(c)
            if parsed_part:
                parsed_expressions.append(parsed_part)
        return parsed_expressions


    def parser_part(self, obj):
        printIt("parser_part", LogLvl.function_calls, obj)
        '''
        labeledAlt
           : alternative (POUND identifier)?
           ;
        '''


        # a single production rule
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.POUND)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.IdentifierContext)
            if not _o:
                return None, children
            return _o[0], children


        children = obj.children
        ac, _ = self._parse_object(children, self.parser.AlternativeContext)
        acr = self.parser_alt(ac)

        _, children = self._parse_question_x(children, pred_inside)
        assert not children

        return acr


    def parse_elementOptions(self, obj):
        printIt("parse_elementOptions", LogLvl.function_calls)
        '''
        elementOptions
           : LT elementOption (COMMA elementOption)* GT
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.LT)


        # a single production rule
        def pred_inside(children):
            printIt("pred_inside", LogLvl.function_calls)
            _o, children = self._parse_question_token(children, self.lexer.COMMA)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.ElementOptionContext)
            if not _o:
                return None, children
            return _o[0], children


        eo, children = self._parse_object(children, self.parser.ElementOptionContext)
        res, children = self._parse_star_x(children, pred_inside)
        lst = [eo] + res
        _o, children = self._parse_token(children, self.lexer.GT)
        return lst


    def parser_alt(self, obj):
        printIt("parser_alt", LogLvl.function_calls, obj)
        '''
        alternative
           : elementOptions? element+
           |
           // explicitly allow empty alts
           ;
        '''
        # a single production rule (or empty)
        children = obj.children
        if not children:
            (nt, known) = self.fbg.create_nonterminal("fblEmptyWord", False)
            if not known:
                nt.add_expression(Expression([Terminal("")]))
            return Expression([nt])
        _o, children = self._parse_question_object(children, self.parser.ElementOptionsContext)
        eo = None
        if _o:
            eo = self.parse_elementOptions(_o[0])
        elts, children = self._parse_star_object(children, self.parser.ElementContext)
        assert len(elts) >= 1  # element+

        res = Expression()
        for e in elts:
            r = self.parser_element(e)
            if r:
                res.append(r)
        return res


    def parser_element(self, obj):
        printIt("parser_element", LogLvl.function_calls, obj)
        '''
        element
           : labeledElement (ebnfSuffix |)
           | atom (ebnfSuffix |)
           | ebnf
           | actionBlock QUESTION?
           ;
        '''

        children = copy.copy(obj.children)
        c = children[0]
        assert len(children) <= 3

        if isinstance(c, self.parser.LabeledElementContext):
            # assert False
            parsed_expressi = self.parse_labeledElement(c)
            ebnf = None
            if len(children) > 1:
                ebnf = self.parse_ebnfSuffix(children[1])

                if isinstance(parsed_expressi, Terminal):
                    (nt, known) = self.fbg.create_nonterminal('terminal-' + parsed_expressi.get_name(), False)
                    if not known:
                        nt.add_expression(Expression([parsed_expressi]))
                    parsed_expressi = nt

                e = Expression()
                e.append(parsed_expressi)
                e.append(EBNF(ebnf))
                return e
            return parsed_expressi



        elif isinstance(c, self.parser.AtomContext):
            parsed_element = self.parse_atom(c)
            assert not isinstance(parsed_element, Expression)
            e = Expression()
            e.append(parsed_element)

            if len(children) > 1:  # then ebnfs
                if isinstance(children[1], self.parser.EbnfSuffixContext):

                    ebnf = self.parse_ebnfSuffix(children[1])

                    if isinstance(parsed_element, Terminal):
                        # we need to create a new nonterminal becaus FBL only supports ebnfs for nonterminals
                        # but here we have e terminal

                        name = parsed_element.get_name()

                        # we need to add something to the name
                        name = "t_" + name
                        # otherwise we have duplicate problems.
                        # imagine the following antlr grammar:
                        ###
                        # start: 'a' c;
                        # c: 'c' *;
                        ###
                        # if we dont add something to the name, c would be:
                        # '<c>': ['<c>*']
                        # which then generates errors while parsing with the EarleyParser
                        (nt, known) = self.fbg.create_nonterminal(name, False)
                        if not known:
                            nt.add_expression(e)

                        e = Expression()
                        e.append(self.fbg.create_nonerminal_wrapper(nt))

                    e.append(Expression([EBNF(ebnf)]))
                    e2 = Expression()
                    e2.append(e)
                    return e2

            else:
                return e

        elif isinstance(c, self.parser.EbnfContext):
            blk = self.parser_ebnf(c)
            return blk


        elif isinstance(c, self.parser.ActionBlockContext):
            if self.__ignore_parser_rule_actions:
                printUnimplemented("Parser Rule Actions", c, None, "Ignoring it")
                return None

            raise NotImplementedError("ActionBlockContext parser")
        else:
            assert False


    def parse_setElement(self, obj) -> Element:
        printIt("parse_setElement", LogLvl.function_calls, obj)
        '''
        setElement
           : TOKEN_REF elementOptions?
           | STRING_LITERAL elementOptions?
           | characterRange
           | LEXER_CHAR_SET
           ;
        '''
        children = copy.copy(obj.children)
        c = children.pop(0)
        if isinstance(c, tree.Tree.TerminalNodeImpl):
            if c.symbol.type == self.lexer.TOKEN_REF:
                assert not children
                name = self.parse_TOKEN_REF(c)
                (nt, _) = self.fbg.create_nonterminal(name, True)
                return nt
            elif c.symbol.type == self.lexer.STRING_LITERAL:
                assert not children
                return self.parse_STRING_LITERAL(c)
            elif c.symbol.type == self.lexer.LEXER_CHAR_SET:
                assert not children
                return self.parse_LEXER_CHAR_SET(c)
            else:
                assert False

        elif isinstance(c, self.parser.CharacterRangeContext):
            assert not children
            return self.parse_characterRange(c)
        else:
            assert False


    def parse_characterRange(self, obj) -> Terminal:
        printIt("parse_characterRange", LogLvl.function_calls, obj)
        '''
        characterRange
           : STRING_LITERAL RANGE STRING_LITERAL
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.STRING_LITERAL)
        a = self.parse_STRING_LITERAL(_o)
        _o, children = self._parse_token(children, self.lexer.RANGE)
        _o, children = self._parse_token(children, self.lexer.STRING_LITERAL)
        b = self.parse_STRING_LITERAL(_o)

        # convert the range in the [a-z] notation
        a = a.get_name()
        b = b.get_name()
        expression = f"[{a}-{b}]"
        a = a.replace("\\\\", "\\")
        b = b.replace("\\\\", "\\")

        lst = self.expand_charset_by_loop(str(a), str(b), children)

        return self.fbg.create_nonterminal_from_char_lst(lst, expression)


    def parser_ebnf(self, obj):
        printIt("parser_ebnf", LogLvl.function_calls, obj)
        '''
        ebnf
           : block blockSuffix?
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_object(children, self.parser.BlockContext)
        res = self.parser_block(_o)

        assert isinstance(res, Expression) or isinstance(res, Nonterminal)

        e = Expression()
        e.append(res)

        ebnfs, children = self._parse_question_object(children, self.parser.BlockSuffixContext)
        if ebnfs:
            ebnf = self.parse_blockSuffix(ebnfs[0])
            e = Expression()
            b = Brackets(res, EBNF(ebnf))
            e.append(b)
            return e

        return res


    def parse_blockSuffix(self, obj):
        printIt("parse_blockSuffix", LogLvl.function_calls, obj)
        '''
        blockSuffix
           : ebnfSuffix
           ;
        '''
        children = obj.children
        _o, children = self._parse_object(children, self.parser.EbnfSuffixContext)
        assert not children
        return self.parse_ebnfSuffix(_o)


    def parse_ebnfSuffix(self, obj):
        printIt("parse_ebnfSuffix", LogLvl.function_calls, obj)
        '''
        ebnfSuffix
           : QUESTION QUESTION?
           | STAR QUESTION?
           | PLUS QUESTION?
           ;
        '''
        children = copy.copy(obj.children)
        c = children.pop(0)
        # assert not children
        assert isinstance(c, tree.Tree.TerminalNodeImpl)
        if c.symbol.type == self.lexer.QUESTION:
            v = self.parse_QUESTION(c)
            _o, children = self._parse_question_token(children, self.lexer.QUESTION)
            return v + ''.join([self.parse_QUESTION(i) for i in _o])
        elif c.symbol.type == self.lexer.STAR:
            v = self.parse_STAR(c)
            _o, children = self._parse_question_token(children, self.lexer.QUESTION)
            return v + ''.join([self.parse_QUESTION(i) for i in _o])
        elif c.symbol.type == self.lexer.PLUS:
            v = self.parse_PLUS(c)
            _o, children = self._parse_question_token(children, self.lexer.QUESTION)
            return v + ''.join([self.parse_QUESTION(i) for i in _o])
        else:
            assert False


    def parser_block(self, obj):
        printIt("parser_block", LogLvl.function_calls, obj)
        '''
        block
           : LPAREN (optionsSpec? ruleAction* COLON)? altList RPAREN
        ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.LPAREN)


        def pred_inside(children_):
            children = copy.copy(children_)
            _o1, children = self._parse_question_object(children, self.parser.OptionsSpecContext)
            assert not _o1
            _o2, children = self._parse_star_object(children, self.parser.RuleActionContext)
            assert not _o2
            _o3, children = self._parse_question_token(children, self.lexer.COLON)
            if not _o3:
                return None, children_
            o = _o3[0]
            return o, children


        res, children = self._parse_question_x(children, pred_inside)
        altlst, children = self._parse_object(children, self.parser.AltListContext)
        _o, children = self._parse_token(children, self.lexer.RPAREN)
        res = self.parser_altList(altlst)
        return res


    def parser_altList(self, obj):
        printIt("parser_altList", LogLvl.function_calls, obj)
        """
        altList
           : alternative (OR alternative)*
           ;
        """
        children = copy.copy(obj.children)
        alt, children = self._parse_object(children, self.parser.AlternativeContext)


        # a single production rule
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.OR)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.AlternativeContext)
            if not _o:
                return None, children
            return _o[0], children


        alts, _ = self._parse_star_x(children, pred_inside)
        altlst = [alt] + alts

        expressions = Expression()
        new_nonterminal_name = "lst"
        for a in altlst:
            parsed_part = self.parser_alt(a)

            if parsed_part is None:
                continue

            ##### if r > 1 then we have NO expansionalternatives. instead we have a concatination
            if len(parsed_part) > 1:
                parsed_part = Expression([parsed_part])

            expressions.append(parsed_part)
            t = parsed_part.get_name()
            new_nonterminal_name += t + "|"

        new_nonterminal_name = new_nonterminal_name[:-1]
        if len(new_nonterminal_name) <= 1:
            new_nonterminal_name = "EMPTY"
        (nt, known) = self.fbg.create_nonterminal(new_nonterminal_name, False)

        if not known:
            for e in expressions:
                nt.add_expression(e)

        return self.fbg.create_nonerminal_wrapper(nt)


    def parse_atom(self, obj) -> Element:
        printIt("parse_atom", LogLvl.function_calls, obj)
        '''
        atom
           : terminal
           | ruleref
           | notSet
           | DOT elementOptions?
           ;
        '''
        # A single token -- can be a terminal or a nonterminal
        children = obj.children
        c = children[0]
        if isinstance(c, self.parser.TerminalContext):
            # note: this may simply be a parser terminal. It does
            # not mean that it is a lexer terminal
            return self.parse_terminal(c)
        elif isinstance(c, self.parser.RulerefContext):
            return self.parse_ruleref(c)
        elif isinstance(c, self.parser.NotSetContext):
            return self.parse_notSet(c)
        elif isinstance(c, tree.Tree.TerminalNodeImpl):
            return self.parse_DOT(c)
        else:
            assert False


    def create_not_nt_out_of_range(self, chars_org, obj):
        chars = chars_org
        is_range = False
        if (chars[0], chars[-1]) == ("[", "]") and len(chars) > 2:
            chars = chars[1:-1]
            is_range = True
            chars = chars.replace('\\]', ']')
        chars = re.escape(chars)
        regex = f"[^{chars}]"
        new_name = f"~[{chars}]"
        lst = self.expand_charset_by_regex(regex, obj)

        if self.__using_gramminator_logic:
            if is_range and len(chars) > 0:
                lst.append(chars[0])

        parsed_element = self.fbg.create_nonterminal_from_char_lst(lst, new_name)

        return self.fbg.create_nonerminal_wrapper(parsed_element)


    def create_not_terminals_out_of_char_list(self, chars, parsed_element, obj):
        total_name = ""
        expressions = []
        for char in chars:
            if char == "\\":
                char = "\\\\"
            name = f"NOT-{char}"
            regex = f"[^{char}]"

            lst = self.expand_charset_by_regex(regex, obj)
            not_nt = self.fbg.create_nonterminal_from_char_lst(lst, name)

            total_name += name
            (nt, _) = self.fbg.create_nonterminal(name, False)
            expressions.append(nt)
            # e2 = Expression([EBNF('?')])
            expressions.append(EBNF('?'))
            if isinstance(parsed_element, Nonterminal):
                nt.not_nt = parsed_element

        (parsed_element, _) = self.fbg.create_nonterminal(total_name, False)

        if len(parsed_element.get_name()) > 2:
            e = Expression(expressions)
            parsed_element.add_expression(e)

        return self.fbg.create_nonerminal_wrapper(parsed_element)


    # lexer and parse
    def parse_notSet(self, obj) -> Nonterminal:
        printIt("parse_notSet", LogLvl.function_calls)

        '''
        notSet
           : NOT setElement
           | NOT blockSet
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.NOT)
        self.parse_NOT(_o)
        c = children.pop(0)
        assert not children
        if isinstance(c, self.parser.SetElementContext):

            parsed_element = self.parse_setElement(copy.copy(c))

            children = copy.copy(c.children)
            c = children.pop(0)

            if c.symbol.type == self.lexer.TOKEN_REF:
                assert isinstance(parsed_element, Nonterminal)
                nt = parsed_element
                (not_nt, _) = self.fbg.create_nonterminal(f"~{nt.get_name()}", False)
                nt.not_nt = not_nt
                not_nt.not_nt = nt
                not_nt.is_not_nt = True
                self.fbg.not_nonterminals.append(not_nt)
                return self.fbg.create_nonerminal_wrapper(not_nt)

            elif c.symbol.type == self.lexer.STRING_LITERAL:
                assert isinstance(parsed_element, Terminal) or isinstance(parsed_element, Nonterminal)
                chars = ""

                if isinstance(parsed_element, Terminal):
                    chars = parsed_element.get_name()
                else:  # Nonterminal
                    # should be range nonterminal
                    chars = parsed_element.get_name()

                return self.create_not_terminals_out_of_char_list(chars, parsed_element, c)


            elif c.symbol.type == self.lexer.LEXER_CHAR_SET:
                name = parsed_element.get_name()
                assert isinstance(parsed_element, Nonterminal)

                chars = ""
                for exp in parsed_element.get_body():
                    char = exp.get_name()
                    assert len(char) == 1
                    char = char.replace("\\", "\\\\")
                    chars += char

                ###################
                total_name = ""
                expressions = []

                name = f"NOT-{chars}"
                regex = f"[^{chars}]"

                lst = self.expand_charset_by_regex(regex, obj)
                not_nt = self.fbg.create_nonterminal_from_char_lst(lst, name)

                return self.fbg.create_nonerminal_wrapper(not_nt)
            #############################

            else:
                assert False


        elif isinstance(c, self.parser.BlockSetContext):
            v = self.parse_NotBlockSet(c)
            return v

        else:
            assert False


    def parse_NotBlockSet(self, obj) -> Expression:
        ####
        # NotBlockSets are bracketed expressions like
        # ~([a-z] | 'B')
        ####
        printIt("parse_NotBlockSet", LogLvl.function_calls)
        '''
        blockSet
            : LPAREN setElement (OR setElement)* RPAREN
            ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.LPAREN)
        _o, children = self._parse_object(children, self.parser.SetElementContext)

        assert _o is not None
        selt_children = [_o]


        # a define with multiple rules
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.OR)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.SetElementContext)
            if not _o:
                return None, children
            return _o[0], children


        cs, children = self._parse_star_x(children, pred_inside)
        selt_children.extend(cs)

        expressions = []
        new_nonterminal_name = "~{"
        all_nonterminals = True
        all_terminals = True
        for c in selt_children:
            parsed_part = self.parse_setElement(c)
            if not isinstance(parsed_part, Nonterminal):
                all_nonterminals = False
            if not isinstance(parsed_part, Terminal):
                if not parsed_part.is_virtual:
                    all_terminals = False
            expressions.append(parsed_part)
            new_nonterminal_name += parsed_part.get_name() + "|"

        new_nonterminal_name = new_nonterminal_name[:-1]
        new_nonterminal_name += "}"

        if all_nonterminals:

            (nt, known) = self.fbg.create_nonterminal(new_nonterminal_name, False)

            if not known:
                nt.is_not_nt = True
                self.fbg.not_nonterminals.append(nt)
                for e in expressions:
                    nt.not_nts_name.append(e.get_name())

            return nt

        elif all_terminals:
            all = ""

            for t in expressions:
                if isinstance(t, Nonterminal):
                    assert t.is_virtual
                    # then this is a parsed range nonterminal,
                    # containing only terminals with each only 1 char
                    # like [a-z]
                    for exp in t.get_body():
                        char = exp.get_name()
                        assert len(char) == 1
                        all += char
                else:
                    c = t.get_name()
                    # decode = c.decode("unicode-escape")
                    all += c

            return self.create_not_nt_out_of_range(all, obj)

        else:
            raise NotImplementedError("BlockSetContext with mixed terminals and nonterminals are not supported.")
            # this is even not valid antlr!


    def parse_terminal(self, obj) -> Element:
        printIt("parse_terminal", LogLvl.function_calls, obj)
        '''
        terminal
           : TOKEN_REF elementOptions?
           | STRING_LITERAL elementOptions?
           ;
        '''
        children = copy.copy(obj.children)
        c = children.pop(0)
        assert isinstance(c, tree.Tree.TerminalNodeImpl)

        if c.symbol.type == self.lexer.TOKEN_REF:
            v = self.parse_RULE_REF(c)
            _o, children = self._parse_question_object(children, self.parser.ElementOptionsContext)
            assert not _o
            (nt, _) = self.fbg.create_nonterminal(v, True)
            return nt

        elif c.symbol.type == self.lexer.STRING_LITERAL:
            v = self.parse_STRING_LITERAL(c)
            _o, children = self._parse_question_object(children, self.parser.ElementOptionsContext)
            return v
        else:
            assert False


    def parse_STRING_LITERAL(self, obj) -> Element:
        printIt("parse_STRING_LITERAL", LogLvl.function_calls, obj)
        v = obj.symbol.text
        assert (v[0], v[-1]) == ("'", "'")
        # we have removed '. So if there was an escape involved (\') then
        # we should unescape it too.
        # we can not use ast.literal_eval here as the ALTLR4 format
        # uses \uXXXX format to specify the unicode characters, which
        # gets converted to the actual unicode chars during literal_eval.
        name = v[1:-1]
        # an espaced backslash (\\) will be double escaped here (\\\\)
        bs = "\\"
        # name = name.replace(bs + bs, bs)

        # so we removing the double escaping here

        name = name.replace("\\'", "'")
        name = name.replace("\\a", "\a")
        name = name.replace("\\b", "\b")
        name = name.replace("\\t", "\t")
        name = name.replace("\\n", "\n")
        name = name.replace("\\v", "\v")
        name = name.replace("\\f", "\f")
        name = name.replace("\\r", "\r")


        # some debug printings here:
        # print(str(name))
        # print(f"Escaped:|{name.encode('unicode_escape').decode('utf-8')}|")
        # print(f'len: {len(name)}')

        try:
            decode = name.encode("unicode-escape")
            decode = decode.decode("unicode-escape", "replace")
        except UnicodeDecodeError as e:
            a = f'Invalid char: "{name}"'
            raise RuntimeError(a) from e

        if len(decode) > 0:
            name = decode

        name = name.replace("\xe2\x80\x98", "‘")
        name = name.replace("â", "’")
        name = name.replace("â", "⊃")
        name = name.replace('â', "⋀")
        name = name.replace('Ã·', "÷")
        name = name.replace('â', "⋁")
        name = name.replace('Â¬', "¬")
        name = name.replace('â ', "≠")
        name = name.replace('Ã', "×")
        name = name.replace('â¤', "≤")
        name = name.replace('⊃', "⊃")
        name = name.replace('â¥', "≥")
        name = name.replace('â', "↑")
        name = name.replace('\xce\xbb', "λ")
        name = name.replace('\xc2\xb5', "µ")
        name = name.replace('\xce\xa9', "Ω")
        name = name.replace('\u02da', "˚")
        name = name.replace('\xc2\xb7', "·")
        name = name.replace('\xe2\x80\x93', "–")

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
            for c in name:
                if c in ["+", "*", "?", "<", ">"]:
                    (nt_c, known) = self.fbg.create_nonterminal(c, False)
                    if not known:
                        nt_c.add_expression(Expression([Terminal(c)]))
                    exp.append(nt_c)
                    nt_name += nt_c.get_name()
                else:
                    nt_name += c
                    exp.append(Terminal(c))

            (nt, known) = self.fbg.create_nonterminal(nt_name, False)
            if not known:
                nt.add_expression(exp)

            return self.fbg.create_nonerminal_wrapper(nt)

        return Terminal(name)


    def parse_ruleref(self, obj):
        printIt("parse_ruleref", LogLvl.function_calls)
        '''
        ruleref
           : RULE_REF argActionBlock? elementOptions?
           ;
        '''
        children = obj.children
        _o, children = self._parse_token(children, self.lexer.RULE_REF)
        v = self.parse_RULE_REF(_o)
        _o, children = self._parse_question_object(children, self.parser.ArgActionBlockContext)
        # _o is here a: b[-1]; see Swift3.g4.
        if not self.__ignore_pre_action_blocks:
            raise NotImplementedError("action block")
        if self.__warn_about_pre_action_blocks and _o:
            printUnimplemented("ArgActionBlockContext", _o, None, "Ignore it.")
        _o, children = self._parse_question_object(children, self.parser.ElementOptionsContext)
        assert not _o
        assert not children
        (nt, _) = self.fbg.create_nonterminal(v, True)
        return nt


    def parse_labeledElement(self, obj):
        printIt("parse_labeledElement", LogLvl.function_calls)

        '''
        labeledElement
           : identifier (ASSIGN | PLUS_ASSIGN) (atom | block)
           ;
        '''
        children = copy.copy(obj.children)
        _o, children = self._parse_object(children, self.parser.IdentifierContext)
        o = self.parse_identifier(_o)
        assign = children.pop(0)
        assert isinstance(assign, tree.Tree.TerminalNodeImpl)
        nxt = children.pop(0)
        res = None
        if isinstance(nxt, self.parser.AtomContext):
            res = self.parse_atom(nxt)
        elif isinstance(nxt, self.parser.BlockContext):
            res = self.parser_block(nxt)
        else:
            assert False
        assert not children
        return res


    def parse_identifier(self, obj):
        printIt("parse_identifier", LogLvl.function_calls)
        '''
        identifier
           : RULE_REF
           | TOKEN_REF
           ;
        '''
        children = obj.children
        if not children:
            return None
        assert len(children) == 1
        c = children[0]
        assert isinstance(c, tree.Tree.TerminalNodeImpl)
        if c.symbol.type == self.lexer.RULE_REF:
            return self.parse_RULE_REF(c)
        elif c.symbol.type == self.lexer.TOKEN_REF:
            return self.parse_TOKEN_REF(c)
        else:
            assert False


    def parse_RULE_REF(self, obj):
        printIt("parse_RULE_REF: " + obj.symbol.text, LogLvl.function_calls)
        return obj.symbol.text


    def parse_TOKEN_REF(self, obj):
        printIt("parse_TOKEN_REF: " + obj.symbol.text, LogLvl.function_calls)
        return obj.symbol.text


    def parse_ruleModifiers_question(self, objs):
        if not objs:
            return []
        assert len(objs) == 1
        return self.parse_ruleModifier(objs[0])


    def parse_ruleModifier(self, obj):
        printIt("parse_ruleModifier", LogLvl.function_calls)
        '''
        ruleModifier
           : PUBLIC
           | PRIVATE
           | PROTECTED
           | FRAGMENT
           ;
        '''
        assert len(obj.children) == 1
        c = obj.children[0]
        if c.symbol.type == self.lexer.FRAGMENT:
            return self.parse_FRAGMENT(c)
        elif c.symbol.type == self.lexer.PRIVATE:
            return self.parse_PRIVATE(c)
        elif c.symbol.type == self.lexer.PUBLIC:
            return self.parse_PUBLIC(c)
        elif c.symbol.type == self.lexer.PROTECTED:
            return self.parse_PROTECTED(c)
        else:
            assert False


    def parse_FRAGMENT(self, obj):
        return obj.symbol.text


    def parse_PUBLIC(self, obj):
        return obj.symbol.text


    def parse_PRIVATE(self, obj):
        return obj.symbol.text


    def parse_PROTECTED(self, obj):
        return obj.symbol.text


    def parse_FRAGMENT_question(self, objs):
        printIt("parse_FRAGMENT_question", LogLvl.function_calls)
        if not objs:
            return []
        assert len(objs) == 1
        return self.parse_FRAGMENT(objs[0])


    ####################################################################################
    ############################### LEXER ##############################################
    ####################################################################################

    def parse_lexerRuleSpec(self, rspec):
        '''
        lexerRuleSpec
           : DOC_COMMENT* FRAGMENT? TOKEN_REF COLON lexerRuleBlock SEMI
           ;
        '''
        children = rspec.children
        _o, children = self._parse_star_token(children, self.lexer.DOC_COMMENT)
        self.parse_DOC_COMMENT_star(_o)

        _o, children = self._parse_question_token(children, self.lexer.FRAGMENT)
        self.parse_FRAGMENT_question(_o)

        _o, children = self._parse_token(children, self.lexer.TOKEN_REF)
        (nt, _) = self.fbg.create_nonterminal(self.parse_TOKEN_REF(_o), True)

        _o, children = self._parse_token(children, self.lexer.COLON)

        _o, children = self._parse_object(children, self.parser.LexerRuleBlockContext)
        ### parserRuleBlock
        printIt("\n>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>")
        printIt("PARSING LEXER RULE: " + nt.get_name(), LogLvl.debug)
        altlst, c = self._parse_object(copy.copy(_o.children), self.parser.LexerAltListContext)
        assert not c
        expression_list = self.lexer_parseRule(altlst)

        if expression_list:
            for e in expression_list:
                nt.add_expression(e)

        else:
            printIt(
                    f"Ignoring nonterminal '{nt.get_name()}' because it has no content. Maybe it contais only non supported features.",
                    LogLvl.warning
                    )

        _o, children = self._parse_token(children, self.lexer.SEMI)


    def lexer_parseRule(self, obj):
        printIt("lexer_parseRule", LogLvl.function_calls, obj)
        '''
        lexerAltList
           : lexerAlt (OR lexerAlt)*
           ;
        '''


        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.OR)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.LexerAltContext)
            if not _o:
                return None, children
            return _o[0], children


        children = copy.copy(obj.children)
        first_part = children.pop(0)
        alt_list = [first_part]

        remaining_part, children = self._parse_star_x(children, pred_inside)
        alt_list.extend(remaining_part)

        parsed_expressions = []
        for c in alt_list:
            parsed_part = self.lexer_alt(c)
            if parsed_part:
                parsed_expressions.append(parsed_part)
        return parsed_expressions


    # returns Nonterminal wrapper or expression
    def lexer_altList(self, obj):
        printIt("lexer_altList", LogLvl.function_calls, obj)
        '''
        lexerAltList
           : lexerAlt (OR lexerAlt)*
           ;
        '''


        # a define with multiple rules
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.OR)
            if not _o:
                return None, children
            _o, children = self._parse_question_object(children, self.parser.LexerAltContext)
            if not _o:
                return None, children
            return _o[0], children


        children = copy.copy(obj.children)
        first_part = children.pop(0)
        alt_list = [first_part]

        remaining_part, children = self._parse_star_x(children, pred_inside)
        alt_list.extend(remaining_part)

        expressions = Expression()
        new_nonterminal_name = "("
        for a in alt_list:
            parsed_part = self.lexer_alt(a)
            if not parsed_part:
                continue
            ##### if r > 1 then we have NO expansionalternatives. instead we have a concatination
            if len(parsed_part) > 1:
                parsed_part = Expression([parsed_part])

            expressions.append(parsed_part)
            new_nonterminal_name += parsed_part.get_name() + "|"

        new_nonterminal_name = new_nonterminal_name[:-1]
        new_nonterminal_name += ")"
        if len(new_nonterminal_name) == 0:
            new_nonterminal_name = f'line{obj.start.line}'
        (nt, known) = self.fbg.create_nonterminal(new_nonterminal_name, False)

        if not known:
            for e in expressions:
                nt.add_expression(e)

        return self.fbg.create_nonerminal_wrapper(nt)


    def lexer_alt(self, obj):
        printIt("lexer_alt", LogLvl.function_calls, obj)
        '''
        lexerAlt
           : lexerElements lexerCommands?
           |
           // explicitly allow empty alts
           ;
        '''
        cs = copy.copy(obj.children)
        if not cs or len(cs) == 1 and not isinstance(cs[0], self.parser.LexerElementsContext):
            # len == 1 because the followig rule also contains an empty word and -> is the one element in cs
            # OTHER: -> mode(DEFAULT_MODE), channel(HIDDEN);
            (nt, known) = self.fbg.create_nonterminal("fblEmptyWord", False)
            if not known:
                nt.add_expression(Expression([Terminal("")]))
            return Expression([nt])

        _o, _ = self._parse_object(cs, self.parser.LexerElementsContext)

        v = self.lexer_elements(_o)

        _o, children = self._parse_question_object(cs, self.parser.LexerCommandsContext)
        if _o:
            cmds = self.parse_lexerCommands(_o[0])

            # make sure here are only actions we know and support:

            for cmd in cmds:
                s = None

                try:
                    s = str(cmd)
                except:
                    pass

                if isinstance(cmd, tuple):
                    s = str(cmd[0])

                if s:

                    if s.lower() in ["channel", "pushmode", "popmode", "mode"]:
                        if self.__ignore_channels:
                            printUnimplemented("Channels", obj, None, "Ignore it.")
                            return v
                        else:
                            raise NotImplementedError("channels")

                    elif s.lower() == "more":
                        if self.__ignore_lexer_more:
                            printUnimplemented("more", obj, None, "Ignore it.")
                            return v
                        else:
                            raise NotImplementedError("Actions, more")

                    elif s.lower() == "type":
                        if self.__ignore_lexer_type:
                            printUnimplemented("type", obj, None, "Ignore it.")
                            return v
                        else:
                            raise NotImplementedError("Actions, type")

                    elif s.lower() == "skip":
                        if self.__enable_skip:
                            name = "SKIPP_ME"
                            (nt, known) = self.fbg.create_nonterminal(name, False, True)
                            nt.add_expression(v)
                            self.fbg.skip = nt
                        return v


                    else:
                        raise NotImplementedError("Actions, unkown", s)


                else:
                    printIt("Unknown type: " + str(type(cmd)), LogLvl.error)
                    assert False

        return v


    def parse_lexerCommands(self, obj):
        printIt("parse_lexerCommands", LogLvl.function_calls)
        '''
        lexerCommands
           : RARROW lexerCommand (COMMA lexerCommand)*
           ;
        '''


        # a single production rule
        def pred_inside(children):
            _o, children = self._parse_question_token(children, self.lexer.COMMA)
            if not _o:
                return None, children
            self.parse_COMMA(_o[0])
            _o, children = self._parse_question_object(children, self.parser.LexerCommandContext)
            if not _o:
                return None, children
            return _o[0], children


        children = copy.copy(obj.children)
        _o, children = self._parse_token(children, self.lexer.RARROW)
        self.parse_RARROW(_o)
        _o, children = self._parse_object(children, self.parser.LexerCommandContext)
        lcommands = [_o]

        res, children = self._parse_star_x(children, pred_inside)
        lcommands.extend(res)

        res = []
        for c in lcommands:
            v = self.parse_lexerCommand(c)
            res.append(v)
        return res


    def parse_lexerCommand(self, obj):
        printIt("parse_lexerCommand", LogLvl.function_calls)
        '''
        lexerCommand
           : lexerCommandName LPAREN lexerCommandExpr RPAREN
           | lexerCommandName
           ;
        '''
        children = copy.copy(obj.children)
        cn, children = self._parse_object(children, self.parser.LexerCommandNameContext)
        cname = self.parse_lexerCommandName(cn)
        if not children:
            return cname

        _o, children = self._parse_token(children, self.lexer.LPAREN)
        self.parse_LPAREN(_o)
        ce, children = self._parse_object(children, self.parser.LexerCommandExprContext)
        _o, children = self._parse_token(children, self.lexer.RPAREN)
        self.parse_RPAREN(_o)
        assert not children

        cname = self.parse_lexerCommandName(cn)
        cexp = self.parse_lexerCommandExpr(ce)
        return (cname, cexp)


    def parse_lexerCommandName(self, obj):
        printIt("parse_lexerCommandName", LogLvl.function_calls)
        '''
        lexerCommandName
           : identifier
           | MODE
           ;
        '''
        children = copy.copy(obj.children)
        c = children[0]
        if isinstance(c, self.parser.IdentifierContext):
            _o, children = self._parse_object(children, self.parser.IdentifierContext)
            assert not children
            return self.parse_identifier(_o)
        elif isinstance(c, tree.Tree.TerminalNodeImpl):
            _o, children = self._parse_token(children, self.lexer.MODE)
            assert not children
            return self.parse_MODE(_o)
        else:
            assert False


    def parse_MODE(self, obj):
        return obj.symbol.text


    def parse_lexerCommandExpr(self, obj):
        printIt("parse_lexerCommandExpr", LogLvl.function_calls)
        '''
        lexerCommandExpr
           : identifier
           | INT
           ;
           // --------------------
           // Rule Alts
        '''
        children = copy.copy(obj.children)
        c = children[0]
        if isinstance(c, self.parser.IdentifierContext):
            _o, children = self._parse_object(copy.copy(obj.children), self.parser.IdentifierContext)
            assert not children
            return self.parse_identifier(_o)
        elif isinstance(c, tree.Tree.TerminalNodeImpl):
            _o, children = self._parse_token(children, self.lexer.MODE)
            assert not children
            return self.parse_INT(_o)
        else:
            assert False


    def lexer_elements(self, obj) -> Expression:
        printIt("lexer_elements", LogLvl.function_calls, obj)
        '''
        lexerElements
           : lexerElement+
           ;
        '''
        line, children = self._parse_star_object(copy.copy(obj.children), self.parser.LexerElementContext)
        assert len(line) > 0  # plus
        parsed_expression_line = ""
        expressions = Expression()

        for val in line:
            o = self.lexer_element(val)

            if o:
                expressions.append(o)

        if len(expressions) >= 1:
            return expressions
        else:
            return None


    def lexer_element(self, obj):
        printIt("lexer_element", LogLvl.function_calls, obj)
        '''
        lexerElement
           : labeledLexerElement ebnfSuffix?
           | lexerAtom ebnfSuffix?
           | lexerBlock ebnfSuffix?
           | actionBlock QUESTION?
           ;
        '''
        children = copy.copy(obj.children)
        c = children.pop(0)

        if isinstance(c, self.parser.LabeledLexerElementContext):
            assert not children
            raise NotImplementedError("parse_labeledLexerElement")
            return self.parse_labeledLexerElement(c)

        elif isinstance(c, self.parser.LexerAtomContext):
            ebnf_suffix, children = self._parse_question_object(children, self.parser.EbnfSuffixContext)
            assert not children
            ebnfs = [self.parse_ebnfSuffix(e) for e in ebnf_suffix]

            res = self.lexer_atom(c)
            e = Expression()
            e.append(res)

            if ebnfs:
                ebnf = ebnfs.pop(0)

                if isinstance(res, Terminal):
                    # we need to create a new nonterminal becaus FBL only supports ebnfs for nontemrinals
                    # but here we have e terminalterminal out of terminal because FBL does not support terminal*
                    (nt, known) = self.fbg.create_nonterminal(res.get_name(), False)
                    if not known:
                        nt.add_expression(e)

                    e = Expression()
                    e.append(self.fbg.create_nonerminal_wrapper(nt))

                e.append(Expression([EBNF(ebnf)]))
                e2 = Expression()
                e2.append(e)
                return e2
            else:
                return e

        elif isinstance(c, self.parser.ActionBlockContext):
            if self.__ignore_lexer_rule_actions:
                printUnimplemented("Lexer Rule Actions", c, None, "Ignoring it")
                return None
            raise NotImplementedError("ActionBlockContext lexer")

        elif isinstance(c, self.parser.LexerBlockContext):
            ebnf_suffix, children = self._parse_question_object(children, self.parser.EbnfSuffixContext)
            assert not children
            res = self.parse_lexerBlock(c)

            assert isinstance(res, Expression) or isinstance(res, Nonterminal)

            ebnfs = [self.parse_ebnfSuffix(e) for e in ebnf_suffix]
            if ebnfs:
                ebnf = ebnfs.pop(0)
                e = Expression()
                b = Brackets(res, EBNF(ebnf))
                e.append(b)
                return e
            else:
                return res
        else:
            assert False


    def parse_lexerBlock(self, obj) -> Nonterminal:
        printIt("parse_lexerBlock", LogLvl.function_calls, obj)
        '''
        lexerBlock
           : LPAREN lexerAltList RPAREN
           ;
        '''
        children = copy.copy(obj.children)
        lparen, children = self._parse_token(children, self.lexer.LPAREN)
        self.parse_LPAREN(lparen)
        lalts, children = self._parse_object(children, self.parser.LexerAltListContext)
        rparen, children = self._parse_token(children, self.lexer.RPAREN)
        self.parse_RPAREN(rparen)
        assert not children

        res = self.lexer_altList(lalts)
        return res


    def lexer_atom(self, obj) -> Element:
        printIt("lexer_atom", LogLvl.function_calls, obj)
        '''
        lexerAtom
           : characterRange
           | terminal
           | notSet
           | LEXER_CHAR_SET
           | DOT elementOptions?
           ;
        '''
        children = copy.copy(obj.children)
        c = children.pop(0)
        assert not children
        if isinstance(c, self.parser.CharacterRangeContext):
            return self.parse_characterRange(c)
        elif isinstance(c, self.parser.TerminalContext):
            return self.parse_terminal(c)
        elif isinstance(c, self.parser.NotSetContext):
            return self.parse_notSet(c)
        elif isinstance(c, tree.Tree.TerminalNodeImpl):
            if c.symbol.type == self.lexer.LEXER_CHAR_SET:
                return self.parse_LEXER_CHAR_SET(c)
            elif c.symbol.type == self.lexer.DOT:
                return self.parse_DOT(c)

        else:
            assert False


####################################################################################
############################### CLASS ENDE #########################################
####################################################################################


def run_antlr(command):
    process = subprocess.Popen(command,
                               universal_newlines = True,
                               shell = False,
                               # stdout = subprocess.PIPE,
                               stderr = subprocess.PIPE
                               )

    output = ""
    return_code = None

    while return_code is None:
        return_code = process.poll()

        output += process.stderr.readline()

    while True:
        s = process.stderr.readline()
        if not s:
            break
        output += s

    return (return_code, output)


def test_with_antlr(input_file):
    tmp_dir = tempfile.mkdtemp()

    file_name = os.path.basename(input_file)
    path = os.path.dirname(input_file)
    input_file_abs = os.path.abspath(input_file)
    tmp_file = f'{tmp_dir}/{file_name}'
    path_to_antlr = os.path.abspath('../bin/antlr-4.9.3-complete.jar')
    os.chdir(path)

    try:
        antlr_process = ['java', '-jar', path_to_antlr, input_file_abs]

        (return_code, output) = run_antlr(antlr_process)

        output = output.splitlines()

        for line in output:
            if line.find("error") != -1:
                print(line)



    finally:
        os.popen(f'rm -r {tmp_dir}')
        pass

    return return_code


########################################################################################
### debug ###
########################################################################################

def print_structure(tre, depth = 0):
    print("  " * (depth + 1), end = "_")
    try:
        print(type(tre), end = ":::")
        print(tre.start.text)
    except:
        try:
            print(tre.symbol.text)
            print(tre.symbol.type)
        except:
            pass
    try:
        for child in tre.children:
            print_structure(child, depth = depth + 1)
    except:
        pass


########################################################################################
### /debug ###
########################################################################################


def main(content, input_file):
    if check_if_is_valid_antlr:
        return_code = test_with_antlr(input_file)
        if return_code != 0:
            raise AttributeError("Invalid ANTLR")

    ag = AntlrG(content, input_file, True)
    ag.start_converting()
    fbl = ag.fbg.print()
    return fbl
    return str(ast.literal_eval(fbl))


if __name__ == '__main__':
    main()
