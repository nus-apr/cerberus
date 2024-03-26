import abc
import copy
import hashlib
import json
import os
import re
from typing import Any
from typing import Dict
from typing import List
from typing import Optional
from typing import Sequence
from typing import Tuple

from app.drivers.tools.AbstractTool import AbstractTool


class AbstractLLMTool(AbstractTool):

    ACCEPTED_NODE_TYPES = [
        "MethodDeclaration",
        "ConstructorDeclaration",
        "ClassDeclaration",
        "EnumDeclaration",
        "InterfaceDeclaration",
    ]

    """
    References from https://github.com/ASSERT-KTH/repairllama/blob/aprcomp2024/main.py
    """

    def find_code(self, file_path: str, line_numbers: List[int]) -> str:
        """
        Finds the code corresponding to the given line numbers in the given file.
        """
        code = ""
        file_content = self.read_file(file_path, encoding="ISO-8859-1")
        for idx, line in enumerate(file_content):
            if idx + 1 in line_numbers:
                code += line
        return code

    def filter_ast_nodes_by_types(
        self, ast_tree: List[Any], node_types: List[str]
    ) -> List[Any]:
        filtered_nodes = []
        for node in ast_tree:
            if isinstance(node, tuple):
                for t in node:
                    if not isinstance(t, tuple):
                        if t.__class__.__name__ in node_types:
                            filtered_nodes.append(t)
            else:
                if node.__class__.__name__ in node_types:
                    filtered_nodes.append(node)

        return filtered_nodes

    def load_ast_nodes(self, file_path: str, prog_language: str) -> List[Any]:
        ast_nodes = []
        tree = self.load_ast(file_path, encoding="ISO-8859-1", language=prog_language)
        file_lines = self.read_file(file_path, encoding="ISO-8859-1")

        filtered_nodes = self.filter_ast_nodes_by_types(tree, self.ACCEPTED_NODE_TYPES)
        for filtered_node in filtered_nodes:
            ast_node = JavaAstNode(
                filtered_node.name,
                filtered_node.__class__.__name__,
                filtered_node.position.line,
            )
            ast_node.load_code_snippet(file_lines)
            ast_node.load_node_data(filtered_node)
            ast_nodes.append(ast_node)

        return ast_nodes

    def load_origin_code_node(
        self,
        file_path: str,
        line_number: int,
        prog_language: str,
        allowed_types: List[str] = ["MethodDeclaration", "ConstructorDeclaration"],
    ) -> Tuple[Any, int]:
        origin_ast_nodes = self.load_ast_nodes(file_path, prog_language)
        ast_nodes = copy.deepcopy(origin_ast_nodes)

        for m in ast_nodes:
            if m.type in allowed_types and m.start_pos <= line_number <= m.end_pos:
                m.add_highlight_line_number(line_number)

        ast_nodes = list(filter(lambda n: len(n.highlight_line_numbers) > 0, ast_nodes))

        ast_nodes.sort(key=lambda n: n.code_size())

        most_related_method = JavaAstNode()
        for m in ast_nodes:
            if len(m.highlight_line_numbers) > 0:
                if most_related_method.is_empty() or len(
                    m.highlight_line_numbers
                ) > len(most_related_method.highlight_line_numbers):
                    most_related_method = m

        position = 0
        for i in range(len(origin_ast_nodes)):
            if origin_ast_nodes[i].hash == most_related_method.hash:
                position = i

        return most_related_method, position

    def create_prompts(
        self, src_locations: List[Tuple[str, int]], bug_info: Dict[str, Any]
    ) -> List[str]:
        prompt_list: List[str] = []
        return prompt_list

    def generate_prompt(
        self, source_file_path: str, line_number: int, bug_type: str, prog_lang: str
    ) -> str:

        prompt = ""
        return prompt


class CodeLine:
    def __init__(self, number: Optional[int], content: str) -> None:
        self.number = number
        self.content = content

    def is_comment_line(self) -> bool:
        return bool(re.match(r"^(//|/\*|\*|\*/)", self.content.strip()))

    def __str__(self) -> str:
        return f"{self.number}: {self.content}"


class JavaAstNode:
    def __init__(
        self,
        name: str = "",
        type: str = "",
        start_pos: int = 0,
        end_pos: int = 0,
        highlight_line_numbers: List[int] = [],
    ) -> None:
        self.name = name
        self.type = type
        self.start_pos = start_pos
        self.end_pos = end_pos
        self.code_snippet: List[Any] = []
        if highlight_line_numbers:
            self.highlight_line_numbers = highlight_line_numbers
        else:
            self.highlight_line_numbers = []
        self.hash = ""
        self.documentation = ""

    def load_node_data(self, ast_node: Any) -> None:
        self.documentation = ast_node.documentation

        hash_str = ""
        hash_str += ast_node.name
        hash_str += ast_node.__class__.__name__
        hash_str += str(ast_node.modifiers)
        hash_str += str(ast_node.annotations)

        if self.type in ["MethodDeclaration", "ConstructorDeclaration"]:
            hash_str += str(ast_node.type_parameters)
            hash_str += str(ast_node.parameters)
            hash_str += str(ast_node.throws)
        elif self.type in ["ClassDeclaration", "InterfaceDeclaration"]:
            hash_str += str(ast_node.type_parameters)

        self.hash = hashlib.sha256(hash_str.encode("utf-8")).hexdigest()

    def is_empty(self) -> bool:
        return self.name == "" and self.start_pos == 0 and self.end_pos == 0

    def load_code_snippet(self, file_lines: List[str]) -> None:
        self.end_pos = self.__cal_node_end_pos(file_lines)
        for num, line in enumerate(file_lines[self.start_pos - 1 : self.end_pos]):
            self.code_snippet.append(CodeLine(self.start_pos + num, line))

    def add_highlight_line_number(self, line_number: int) -> None:
        self.highlight_line_numbers.append(line_number)

    def code_lines(self, include_comment_line: bool = True) -> List[str]:
        if include_comment_line:
            return [line.content for line in self.code_snippet]
        else:
            return [
                line.content for line in self.code_snippet if not line.is_comment_line()
            ]

    def code_lines_str(self, include_comment_line: bool = True) -> str:
        return "".join(self.code_lines(include_comment_line))

    def code_size(self) -> int:
        return self.end_pos - self.start_pos + 1

    def __cal_node_end_pos(self, file_lines: List[str]) -> int:
        try:
            current_pos = self.start_pos
            stack = []

            while current_pos < len(file_lines):
                line = file_lines[current_pos - 1]
                line = re.sub(r'".*"', "", line)
                line = re.sub(r"'.*'", "", line)
                if CodeLine(None, line).is_comment_line():
                    current_pos += 1
                    continue
                for c in line:
                    if c == "{":
                        stack.append(c)
                    elif c == "}":
                        stack.pop()
                        if len(stack) == 0:
                            return current_pos
                    elif c == ";":
                        if len(stack) == 0:
                            return current_pos
                current_pos += 1

            return current_pos
        except Exception as e:
            print(
                "Error in __cal_node_end_pos: {} {} {}\n{}".format(
                    self.name, self.type, self.start_pos, e
                )
            )
            raise e

    def __str__(self) -> str:
        return "JavaAstNode(name={}, type={}, start_pos={}, end_pos={}, hash={}, highlight_line_numbers=\n{})".format(
            self.name,
            self.type,
            self.start_pos,
            self.end_pos,
            self.hash,
            self.highlight_line_numbers,
        )

    def __repr__(self) -> str:
        return self.__str__()

    def __eq__(self, __o: object) -> bool:
        if not isinstance(__o, JavaAstNode):
            return False
        return (
            self.name == __o.name
            and self.type == __o.type
            and self.start_pos == __o.start_pos
            and self.end_pos == __o.end_pos
            and self.hash == __o.hash
        )
