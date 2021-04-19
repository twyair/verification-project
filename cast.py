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
    comma = ","
    semicolon = ";"
    lt = "<"
    eq = "="
    gt = ">"
    AND_OP = "AND_OP"
    CONSTANT = "CONSTANT"  # V
    ELSE = "ELSE"
    IDENTIFIER = "IDENTIFIER"  # V
    IF = "IF"
    INT = "INT"
    LE_OP = "LE_OP"
    RETURN = "RETURN"
    VOID = "VOID"
    EQ_OP = "EQ_OP"
    OR_OP = "OR_OP"
    additive_expression = "additive_expression"  # V
    assignment_expression = "assignment_expression"  # V
    block_item_list = "block_item_list"  # V
    compound_statement = "compound_statement"  # V
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


def parse(ast: Dict[str, Any]) -> AstNode:
    return AstNode(
        text=ast.get("text", None),
        type=AstType(ast["type"]),
        range=AstRange(**ast["range"]),
        children=[parse(c) for c in ast["children"]] if ast["children"] else [],
    )
