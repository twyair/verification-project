import enum
from dataclasses import dataclass
from typing import Any, Dict, List, Optional


@enum.unique
class AstType(enum.Enum):
    paren_left = "("
    paren_right = ")"
    bracket_left = "["
    bracket_right = "]"
    brace_left = "{"
    brace_right = "}"
    plus = "+"
    minus = "-"
    mult = "*"
    div = "/"
    mod = "%"
    comma = ","
    semicolon = ";"
    lt = "<"
    eq = "="
    gt = ">"
    not_ = "!"
    neg = "~"
    EXTERN = "EXTERN"
    CONSTANT = "CONSTANT"  # V
    ELSE = "ELSE"
    IDENTIFIER = "IDENTIFIER"  # V
    IF = "IF"
    SWITCH = "SWITCH"
    WHILE = "WHILE"
    FOR = "FOR"
    DO = "DO"
    CONTINUE = "CONTINUE"
    BREAK = "BREAK"
    GOTO = "GOTO"
    RETURN = "RETURN"
    CASE = "CASE"
    DEFAULT = "DEFAULT"
    INT = "INT"
    FLOAT = "FLOAT"
    BOOL = "BOOL"
    VOID = "VOID"
    NE_OP = "NE_OP"
    GE_OP = "GE_OP"
    RIGHT_OP = "RIGHT_OP"
    LEFT_OP = "LEFT_OP"
    LE_OP = "LE_OP"
    EQ_OP = "EQ_OP"
    OR_OP = "OR_OP"
    AND_OP = "AND_OP"
    MUL_ASSIGN = "MUL_ASSIGN"
    DIV_ASSIGN = "DIV_ASSIGN"
    MOD_ASSIGN = "MOD_ASSIGN"
    ADD_ASSIGN = "ADD_ASSIGN"
    SUB_ASSIGN = "SUB_ASSIGN"
    LEFT_ASSIGN = "LEFT_ASSIGN"
    RIGHT_ASSIGN = "RIGHT_ASSIGN"
    AND_ASSIGN = "AND_ASSIGN"
    XOR_ASSIGN = "XOR_ASSIGN"
    OR_ASSIGN = "OR_ASSIGN"
    unary_expression = "unary_expression"  # V
    shift_expression = "shift_expression"  # V
    additive_expression = "additive_expression"  # V
    multiplicative_expression = "multiplicative_expression"  # V
    and_expression = "and_expression"  # V
    exclusive_or_expression = "exclusive_or_expression"  # V
    inclusive_or_expression = "inclusive_or_expression"  # V
    conditional_expression = "conditional_expression"
    assignment_expression = "assignment_expression"  # V
    block_item_list = "block_item_list"  # V
    compound_statement = "compound_statement"  # V
    iteration_statement = "iteration_statement"
    labeled_statement = "labeled_statement"
    declaration = "declaration"  # V
    direct_declarator = "direct_declarator"  # V
    expression_statement = "expression_statement"  # V
    function_definition = "function_definition"  # V
    init_declarator = "init_declarator"  # V
    jump_statement = "jump_statement"  # V
    logical_and_expression = "logical_and_expression"  # V
    logical_or_expression = "logical_or_expression"  # V
    parameter_declaration = "parameter_declaration"  # X
    parameter_list = "parameter_list"  # X
    postfix_expression = "postfix_expression"  # V
    primary_expression = "primary_expression"  # V
    relational_expression = "relational_expression"  # V
    selection_statement = "selection_statement"  # V
    translation_unit = "translation_unit"  # V
    equality_expression = "equality_expression"  # V
    declaration_specifiers = "declaration_specifiers"
    argument_expression_list = "argument_expression_list"


@dataclass
class AstRange:
    startLineNumber: int
    startColumn: int
    endLineNumber: int
    endColumn: int


@dataclass
class AstNode:
    text: Optional[str]
    type: AstType
    range: AstRange
    children: List["AstNode"]

    def __getitem__(self, index: int) -> "AstNode":
        return self.children[index]


def parse(ast: Dict[str, Any]) -> AstNode:
    return AstNode(
        text=ast.get("text", None),
        type=AstType(ast["type"]),
        range=AstRange(**ast["range"]),
        children=[parse(c) for c in ast["children"]] if ast["children"] else [],
    )
