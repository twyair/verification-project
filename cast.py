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
    CONSTANT = "CONSTANT"
    ELSE = "ELSE"
    IDENTIFIER = "IDENTIFIER"
    IF = "IF"
    INT = "INT"
    LE_OP = "LE_OP"
    RETURN = "RETURN"
    VOID = "VOID"
    additive_expression = "additive_expression"
    assignment_expression = "assignment_expression"
    block_item_list = "block_item_list"
    compound_statement = "compound_statement"
    declaration = "declaration"
    direct_declarator = "direct_declarator"
    expression_statement = "expression_statement"
    function_definition = "function_definition"
    init_declarator = "init_declarator"
    jump_statement = "jump_statement"  # return
    logical_and_expression = "logical_and_expression"
    logical_or_expression = "logical_or_expression"
    parameter_declaration = "parameter_declaration"
    parameter_list = "parameter_list"
    postfix_expression = "postfix_expression"
    primary_expression = "primary_expression"
    relational_expression = "relational_expression"
    selection_statement = "selection_statement"  # if
    translation_unit = "translation_unit"


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
