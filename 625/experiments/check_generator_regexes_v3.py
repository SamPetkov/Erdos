#!/usr/bin/env python3
"""Statically validate literal regular expressions in the manuscript generator.

`py_compile` does not compile regex patterns or parse replacement templates.
This checker walks the generator AST, compiles every literal `re.sub` pattern,
and asks the regex engine to parse each literal replacement template. Callable
replacements are deliberately accepted because their return values are literal
text rather than replacement-language programs.
"""

from __future__ import annotations

import ast
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
GENERATOR = ROOT / "scripts" / "build_self_contained_ams_v3.py"


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def is_re_sub(node: ast.Call) -> bool:
    return (
        isinstance(node.func, ast.Attribute)
        and isinstance(node.func.value, ast.Name)
        and node.func.value.id == "re"
        and node.func.attr == "sub"
    )


def main() -> None:
    require(GENERATOR.is_file(), f"missing generator: {GENERATOR}")
    source = GENERATOR.read_text(encoding="utf-8")
    tree = ast.parse(source, filename=str(GENERATOR))

    calls = 0
    literal_patterns = 0
    literal_replacements = 0
    callable_replacements = 0

    for node in ast.walk(tree):
        if not isinstance(node, ast.Call) or not is_re_sub(node):
            continue
        calls += 1
        require(len(node.args) >= 2, f"line {node.lineno}: re.sub lacks arguments")

        try:
            pattern = ast.literal_eval(node.args[0])
        except (ValueError, TypeError, SyntaxError) as exc:
            raise RuntimeError(
                f"line {node.lineno}: re.sub pattern is not a static literal"
            ) from exc
        require(isinstance(pattern, str), f"line {node.lineno}: non-string pattern")
        try:
            compiled = re.compile(pattern)
        except re.error as exc:
            raise RuntimeError(
                f"line {node.lineno}: malformed regex pattern: {exc}"
            ) from exc
        literal_patterns += 1

        replacement_node = node.args[1]
        try:
            replacement = ast.literal_eval(replacement_node)
        except (ValueError, TypeError, SyntaxError):
            require(
                isinstance(replacement_node, (ast.Lambda, ast.Name)),
                f"line {node.lineno}: replacement must be literal or callable",
            )
            callable_replacements += 1
            continue

        require(
            isinstance(replacement, str),
            f"line {node.lineno}: literal replacement is not a string",
        )
        try:
            # The engine parses the replacement template even when the subject
            # does not match, so this catches invalid escapes such as `\lambda`.
            compiled.sub(replacement, "")
        except re.error as exc:
            raise RuntimeError(
                f"line {node.lineno}: malformed replacement template: {exc}"
            ) from exc
        literal_replacements += 1

    require(calls >= 15, f"unexpectedly few re.sub calls: {calls}")
    require(calls == literal_patterns, "not every re.sub pattern was checked")
    print("ERDOS 625 GENERATOR REGEX CHECK: PASS")
    print(f"  re.sub calls: {calls}")
    print(f"  literal replacement templates: {literal_replacements}")
    print(f"  callable replacements: {callable_replacements}")


if __name__ == "__main__":
    main()
