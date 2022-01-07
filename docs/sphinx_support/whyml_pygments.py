# -*- coding: utf-8 -*-
"""
    pygments.lexers.ml
    ~~~~~~~~~~~~~~~~~~

    This is a lexer for Whyml adapted from the file
    pygments-main/pygments/lexers/ml.py of the pygments repository.
    It takes the information present in why3.el in Why3 repository.

    Note that this file is quickly done wrong (only keywords change from the
    ocaml file) but it helps.

"""

from pygments.lexer import RegexLexer, include, default
from pygments.token import (
    Text,
    Comment,
    Operator,
    Keyword,
    Name,
    String,
    Number,
    Punctuation,
)

__all__ = ["WhymlLexer"]


class WhymlLexer(RegexLexer):
    """
    For the Whyml language.

    """

    name = "Whyml"
    aliases = ["whyml"]
    filenames = ["*.mlw", "*.why"]
    mimetypes = ["text/x-why3"]

    keywords_type = (
        "invariant",
        "variant",
        "diverges",
        "requires",
        "ensures",
        "pure",
        "returns",
        "raises",
        "reads",
        "writes",
        "alias",
        "assert",
        "assume",
        "check",
    )

    keywords_keyword = (
        "use",
        "clone",
        "scope",
        "import",
        "export",
        "coinductive",
        "inductive",
        "external",
        "constant",
        "function",
        "predicate",
        "val",
        "exception",
        "axiom",
        "lemma",
        "goal",
        "type",
        "mutable",
        "abstract",
        "private",
        "any",
        "match",
        "let",
        "rec",
        "in",
        "if",
        "then",
        "else",
        "begin",
        "end",
        "while",
        "for",
        "to",
        "downto",
        "do",
        "done",
        "loop",
        "absurd",
        "ghost",
        "raise",
        "return",
        "break",
        "continue",
        "try",
        "with",
        "theory",
        "uses",
        "module",
        "converter",
        "fun",
        "at",
        "old",
        "true",
        "false",
        "forall",
        "exists",
        "label",
        "by",
        "so",
        "meta",
    )

    keyopts = (
        "!=",
        "#",
        "&",
        "&&",
        r"\(",
        r"\)",
        r"\*",
        r"\+",
        ",",
        "-",
        r"-\.",
        "->",
        r"\.",
        r"\.\.",
        ":",
        "::",
        ":=",
        ":>",
        ";",
        ";;",
        "<",
        "<-",
        "=",
        ">",
        ">]",
        r">\}",
        r"\?",
        r"\?\?",
        r"\[",
        r"\[<",
        r"\[>",
        r"\[\|",
        "]",
        "_",
        "`",
        r"\{",
        r"\{<",
        r"\|",
        r"\|]",
        r"\}",
        "~",
        r"/\\",
        r"\\/",
    )

    operators = r"[!$%&*+\./:<=>?@^|~-]"
    word_operators = ("and", "asr", "land", "lor", "lsl", "lxor", "mod", "or")
    prefix_syms = r"[!?~]"
    infix_syms = r"[=<>@^|&+\*/$%-]"
    primitives = ("unit", "int", "float", "bool", "string", "char", "list", "array")

    tokens = {
        "escape-sequence": [
            (r'\\[\\"\'ntbr]', String.Escape),
            (r"\\[0-9]{3}", String.Escape),
            (r"\\x[0-9a-fA-F]{2}", String.Escape),
        ],
        "root": [
            (r"\s+", Text),
            (r"false|true|\(\)|\[\]", Name.Builtin.Pseudo),
            (r"\b([A-Z][\w\']*)(?=\s*\.)", Name.Namespace, "dotted"),
            (r"\b([A-Z][\w\']*)", Name.Class),
            (r"\(\*(?![)])", Comment, "comment"),
            (r"\b(%s)\b" % "|".join(keywords_keyword), Keyword),
            (r"\b(%s)\b" % "|".join(keywords_type), Keyword.Type),
            (r"(%s)" % "|".join(keyopts[::-1]), Operator),
            (r"(%s|%s)?%s" % (infix_syms, prefix_syms, operators), Operator),
            (r"\b(%s)\b" % "|".join(word_operators), Operator.Word),
            (r"\b(%s)\b" % "|".join(primitives), Keyword.Type),
            (r"[^\W\d][\w']*", Name),
            (r"-?\d[\d_]*(.[\d_]*)?([eE][+\-]?\d[\d_]*)", Number.Float),
            (r"0[xX][\da-fA-F][\da-fA-F_]*", Number.Hex),
            (r"0[oO][0-7][0-7_]*", Number.Oct),
            (r"0[bB][01][01_]*", Number.Bin),
            (r"\d[\d_]*", Number.Integer),
            (r"'(?:(\\[\\\"'ntbr ])|(\\[0-9]{3})|(\\x[0-9a-fA-F]{2}))'", String.Char),
            (r"'.'", String.Char),
            (r"'", Keyword),  # a stray quote is another syntax element
            (r'"', String.Double, "string"),
            (r"[~?][a-z][\w\']*:", Name.Variable),
        ],
        "comment": [
            (r"[^(*)]+", Comment),
            (r"\(\*", Comment, "#push"),
            (r"\*\)", Comment, "#pop"),
            (r"[(*)]", Comment),
        ],
        "string": [
            (r'[^\\"]+', String.Double),
            include("escape-sequence"),
            (r"\\\n", String.Double),
            (r'"', String.Double, "#pop"),
        ],
        "dotted": [
            (r"\s+", Text),
            (r"\.", Punctuation),
            (r"[A-Z][\w\']*(?=\s*\.)", Name.Namespace),
            (r"[A-Z][\w\']*", Name.Class, "#pop"),
            (r"[a-z_][\w\']*", Name, "#pop"),
            default("#pop"),
        ],
    }
