"""Alternate Ada and Project Files parsers for Sphinx/Rest."""

import re
from pygments.lexer import RegexLexer, bygroups
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


def get_lexer_tokens(tag_highlighting=False, project_support=False):
    """Return the tokens needed for RegexLexer.

    :param tag_highlighting: if True we support tag highlighting. See
        AdaLexerWithTags documentation
    :type tag_highlighting: bool
    :param project_support: if True support additional keywords associated
        with project files.
    :type project_support:  bool

    :return: a dictionary following the structure required by RegexLexer
    :rtype: dict
    """
    if project_support:
        project_pattern = r"project\s+|"
        project_pattern2 = (
            r"aggregate|extends|external|external_as_list|library|project|"
        )
    else:
        project_pattern = r""
        project_pattern2 = r""

    result = {
        "root": [
            # Comments
            (r"--.*$", Comment),
            # Character literal
            (r"'.'", String.Char),
            # Strings
            (r'"[^"]*"', String),
            # Numeric
            # Based literal
            (r"[0-9][0-9_]*#[0-9a-f][0-9a-f_]*#(E[\+-]?[0-9][0-9_]*)?", Number.Integer),
            (
                r"[0-9][0-9_]*#[0-9a-f][0-9a-f_]*"
                r"\.[0-9a-f][0-9a-f_]*#(E[\+-]?[0-9][0-9_]*)?",
                Number.Float,
            ),
            # Decimal literal
            (r"[0-9][0-9_]*\.[0-9][0-9_](E[\+-]?[0-9][0-9_]*)?", Number.Float),
            (r"[0-9][0-9_]*(E[\+-]?[0-9][0-9_]*)?", Number.Integer),
            # Match use and with statements
            # The first part of the pattern is be sure we don't match
            # for/use constructs.
            (
                r"(\n\s*|;\s*)(with|use)(\s+[\w\.]+\s*;)",
                bygroups(Punctuation, Keyword.Reserved, Name.Namespace),
            ),
            # Match procedure, package and function declarations
            (r"end\s+(if|loop|record)", Keyword),
            (
                r"(package(?:\s+body)?\s+|"
                + project_pattern
                + r"function\s+|end\s+|procedure\s+)([\w\.]+)",
                bygroups(Keyword, Name.Function),
            ),
            # Ada standard attributes, GNAT specific ones and
            # SPARK ones ('Update, 'Loop_Entry, 'Initialized)
            # (reversed order to avoid having for
            #  example Max before Max_Alignment_For_Allocation).
            (
                r"\'(Write|Word_Size|Width|Wide_Width|Wide_Wide_Width|"
                r"Wide_Wide_Value|Wide_Wide_Image|Wide_Value|Wide_Image|"
                r"Word_Size|Wchar_T_Size|Version|Variable_Indexing|Value_Size|"
                r"Value|Valid_Value|Valid_Scalars|VADS_Size|Valid|Val|"
                r"Update|Unrestricted_Access|Universal_Literal_String|"
                r"Unconstrained_Array|Unchecked_Access|Unbiased_Rounding|"
                r"UET_Address|TypeCode|Truncation|Type_Key|Type_Class|To_Any|"
                r"To_Address|Tick|Terminated|Target_Name|Tag|"
                r"System_Allocator_Alignment|Succ|Super|"
                r"Stub_Type|Stream_Size|Storage_Unit|Storage_Size|Storage_Pool|"
                r"Small_Numerator|Small_Denominator|Small|Size|"
                r"Simple_Storage_Pool|Signed_Zeros|Scaling|Scale|"
                r"Scalar_Storage_Order|Safe_Small|Safe_Last|Safe_Large|"
                r"Safe_First|Safe_Emax|Rounding|Round|Result|Restriction_Set|"
                r"Remainder|Ref|Reduce|Read|Range_Length|Range|"
                r"Put_Image|Priority|Pred|Preelaborable_Initialization|"
                r"Position|Pos|Pool_Address|Passed_By_Reference|Partition_Id|"
                r"Overlaps_Storage|Output|Old|Object_Size|Null_Parameter|Modulus|"
                r"Model_Small|Model_Mantissa|Model_Epsilon|Model_Emin|Model|Mod|"
                r"Min|Mechanism_Code|Maximum_Alignment|"
                r"Max_Size_In_Storage_Elements|Max_Priority|"
                r"Max_Interrupt_Priority|"
                r"Max_Integer_Size|Max_Alignment_For_Allocation|"
                r"Max|Mantissa|Machine_Size|Machine_Rounds|Machine_Rounding|"
                r"Machine_Radix|Machine_Overflows|Machine_Mantissa|Machine_Emin|"
                r"Machine_Emax|Machine|Loop_Entry|Library_Level|Length|"
                r"Leading_Part|Last_Valid|Last_Bit|"
                r"Last|Large|Iterator_Element|Iterable|Invalid_Value|"
                r"Integer_Value|Input|Initialized|Implicit_Dereference|Img|Image|"
                r"Identity|Has_Tagged_Values|Has_Same_Storage|Has_Discriminants|"
                r"Has_Access_Values|From_Any|Fraction|Fore|Floor|Fixed_Value|"
                r"First_Valid|"
                r"First_Bit|First|Finalization_Size|Fast_Math|External_Tag|"
                r"Exponent|Epsilon|Enum_Val|"
                r"Enum_Rep|Enabled|Emax|Elaborated|Elab_Subp_Body|Elab_Spec|"
                r"Elab_Body|Digits|Descriptor_Size|Digits|Deref|Denorm|Delta|"
                r"Definite|Default_Scalar_Storage_Order|Default_Iterator|"
                r"Default_Bit_Order|Count|Copy_Sign|Constrained|"
                r"Constant_Indexing|"
                r"Compose|Component_Size|Compiler_Version|Code_Address|Class|"
                r"Ceiling|Caller|Callable|Body_Version|Bit_Order|Bit_Position|"
                r"Bit|Base|Atomic_Always_Lock_Free|"
                r"Asm_Output|Asm_Input|Alignment|Aft|Adjacent|"
                r"Address_Size|Address|Access|Abort_Signal|AST_Entry)",
                Name.Attribute,
            ),
            # All Ada reserved words
            (
                r"(abort|abstract|abs|accept|access|aliased|all|and|array|at|"
                r"begin|body|case|constant|declare|delay|delta|digits|do|"
                r"else|elsif|end|entry|exception|exit|for|function|generic|goto|"
                r"if|interface|in|is|limited|loop|mod|new|not|null|"
                r"of|or|others|out|overriding|"
                + project_pattern2
                + r"package|pragma|private|procedure|protected|"
                r"raise|range|record|rem|renames|requeue|return|reverse|"
                r"select|separate|some|subtype|synchronized|"
                r"tagged|task|terminate|then|type|until|use|when|while|with|xor"
                r")([\s;,])",
                bygroups(Keyword.Reserved, Punctuation),
            ),
            # Two characters operators
            (r"=>|\.\.|\*\*|:=|/=|>=|<=|<<|>>|<>", Operator),
            # One character operators
            (r"&|\'|\(|\)|\*|\+|-|\.|/|:|<|=|>|\|", Operator),
            (r",|;", Punctuation),
            # Spaces
            (r"\s+", Text),
            # Builtin values
            (r"False|True", Keyword.Constant),
            # Identifiers
            (r"[\w\.]+", Name),
            (r".", Text),
        ]
    }

    # Insert tag highlighting before identifiers
    if tag_highlighting:
        result["root"].insert(-1, (r"\[[\w ]*\]", Name.Tag))

    return result


class AdaLexer(RegexLexer):
    """Alternate Pygments lexer for Ada source code and project files.

    The default pygments lexer always fails causing disabling of syntax
    highlighting in Sphinx. This lexer is simpler but safer.

    In order to use this lexer in your Sphinx project add the following
    code at the end of your conf.py

    .. code-block:: python

        import gnatpython.ada_pygments

        def setup(app):
            app.add_lexer('ada', gnatpython.ada_pygments.AdaLexer())

    """

    name = "Ada"
    aliases = ["ada", "ada83", "ada95", "ada2005", "ada2012", "ada2022"]
    filenames = ["*.adb", "*.ads", "*.ada"]
    mimetypes = ["text/x-ada"]

    flags = re.MULTILINE | re.I  # Ignore case

    tokens = get_lexer_tokens()


class TaggedAdaLexer(AdaLexer):
    """Alternate Pygments lexer for Ada source code with tags.

    A tag is a string of the form::

      [MY STRING]

    Only alphanumerical characters and spaces are considered inside the
    brackets.
    """

    name = "TaggedAda"
    aliases = ["tagged_ada"]
    tokens = get_lexer_tokens(True)


class GNATProjectLexer(RegexLexer):
    """Pygment lexer for project files.

    This is the same as the AdaLexer but with support of ``project``
    keyword.
    """

    name = "GPR"
    aliases = ["gpr"]
    filenames = ["*.gpr"]
    mimetypes = ["text/x-gpr"]

    flags = re.MULTILINE | re.I  # Ignore case

    tokens = get_lexer_tokens(project_support=True)
