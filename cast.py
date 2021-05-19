from __future__ import annotations
import enum
from dataclasses import dataclass
from typing import Any, Optional


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
    question_mark = "?"
    colon = ":"
    STRING_LITERAL = "STRING_LITERAL"
    EXTERN = "EXTERN"
    CONSTANT = "CONSTANT"
    ELSE = "ELSE"
    IDENTIFIER = "IDENTIFIER"
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
    INC_OP = "INC_OP"
    DEC_OP = "DEC_OP"
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
    cast_expression = "cast_expression"
    unary_expression = "unary_expression"
    shift_expression = "shift_expression"
    additive_expression = "additive_expression"
    multiplicative_expression = "multiplicative_expression"
    and_expression = "and_expression"
    exclusive_or_expression = "exclusive_or_expression"
    inclusive_or_expression = "inclusive_or_expression"
    conditional_expression = "conditional_expression"
    assignment_expression = "assignment_expression"
    block_item_list = "block_item_list"
    compound_statement = "compound_statement"
    iteration_statement = "iteration_statement"
    labeled_statement = "labeled_statement"
    declaration = "declaration"
    direct_declarator = "direct_declarator"
    expression_statement = "expression_statement"
    function_definition = "function_definition"
    init_declarator = "init_declarator"
    jump_statement = "jump_statement"
    logical_and_expression = "logical_and_expression"
    logical_or_expression = "logical_or_expression"
    parameter_declaration = "parameter_declaration"
    parameter_list = "parameter_list"
    postfix_expression = "postfix_expression"
    primary_expression = "primary_expression"
    relational_expression = "relational_expression"
    selection_statement = "selection_statement"
    translation_unit = "translation_unit"
    equality_expression = "equality_expression"
    declaration_specifiers = "declaration_specifiers"
    argument_expression_list = "argument_expression_list"


LINE_NUM_DIFF = 41


@dataclass(frozen=True, order=True)
class AstRange:
    start_line: int
    start_column: int
    end_line: int
    end_column: int

    @staticmethod
    def from_json(d: dict[str, int]) -> AstRange:
        return AstRange(
            start_line=d["startLineNumber"] - LINE_NUM_DIFF,
            start_column=d["startColumn"],
            end_line=d["endLineNumber"] - LINE_NUM_DIFF,
            end_column=d["endColumn"],
        )


@dataclass(frozen=True)
class AstNode:
    text: Optional[str]
    type: AstType
    range: AstRange
    children: list[AstNode]

    def __getitem__(self, index: int) -> AstNode:
        return self.children[index]


def parse(ast: dict[str, Any]) -> AstNode:
    return AstNode(
        text=ast.get("text", None),
        type=AstType(ast["type"]),
        range=AstRange.from_json(ast["range"]),
        children=[parse(c) for c in ast["children"]] if ast["children"] else [],
    )
