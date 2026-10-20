"""Check static Manim slide LaTeX before launching expensive scene renders.

The slide helpers use Tex, MathTex, and Tex-wrapped minipages.  Extract their
literal arguments from the Python AST and compile them with the same LaTeX
preamble/engine as the Manim template.  This does not substitute for rendering
scenes with dynamic text, but catches many source errors in under a second.
"""
from __future__ import annotations

import ast
from dataclasses import dataclass
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


SOURCE_DIR = Path(__file__).resolve().parent


@dataclass(frozen=True)
class TexFragment:
    kind: str
    body: str
    path: Path
    line: int


def _literal(node: ast.AST) -> str | None:
    if isinstance(node, ast.Constant) and isinstance(node.value, str):
        return node.value
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        left, right = _literal(node.left), _literal(node.right)
        if left is not None and right is not None:
            return left + right
    if isinstance(node, ast.JoinedStr) and all(isinstance(n, ast.Constant) for n in node.values):
        return "".join(n.value for n in node.values)
    return None


def collect_fragments(paths: list[Path] | None = None, *, scenes: set[str] | None = None) -> list[TexFragment]:
    """Gather compile-time strings that reach Tex/MathTex/para study helpers."""
    if paths is None:
        paths = sorted(SOURCE_DIR.glob("slides_*.py"))
    fragments: list[TexFragment] = []
    for path in paths:
        tree = ast.parse(path.read_text(), filename=str(path))

        def add(kind: str, expr: ast.AST | None) -> None:
            value = _literal(expr) if expr is not None else None
            if value:
                fragments.append(TexFragment(kind, value, path, expr.lineno))

        scene_nodes = (
            child
            for cls in tree.body
            if isinstance(cls, ast.ClassDef) and (scenes is None or cls.name in scenes)
            for child in ast.walk(cls)
        )
        for node in scene_nodes:
            if isinstance(node, (ast.Assign, ast.AnnAssign)):
                targets = node.targets if isinstance(node, ast.Assign) else [node.target]
                if any(isinstance(t, ast.Name) and t.id in {"title", "kicker"} for t in targets):
                    add("tex", node.value)
            if not isinstance(node, ast.Call) or not isinstance(node.func, ast.Name):
                continue
            name, args = node.func.id, node.args
            keywords = {kw.arg: kw.value for kw in node.keywords}
            if name in {"tex", "Tex", "para", "math", "MathTex", "operation_box"} and args:
                if name in {"math", "MathTex"}:
                    # A MathTex call's substrings are independent math fragments.
                    if all(_literal(arg) is not None for arg in args):
                        for arg in args:
                            add("math", arg)
                else:
                    add("para" if name == "para" else "tex", args[0])
                if name == "operation_box":
                    add("tex", keywords.get("subtitle"))
            if name in {"definition_box", "reminder_box"}:
                if args:
                    add("tex", args[0])
                if len(args) > 1:
                    add("para", args[1])
                add("math", keywords.get("symbol"))
            if name == "remember_box" and args:
                add("para", args[0])
            if name in {"glossary_grid", "derivation_steps"} and args:
                if isinstance(args[0], (ast.List, ast.Tuple)):
                    for entry in args[0].elts:
                        if isinstance(entry, ast.Tuple) and len(entry.elts) >= 2:
                            add("tex", entry.elts[0])
                            add("para", entry.elts[1])
            if name == "colored_math":
                for entry in args:
                    if isinstance(entry, ast.Tuple) and entry.elts:
                        add("math", entry.elts[0])
    return fragments


# Keep these packages/definitions aligned with shuffleviz.style.TEMPLATE.
_TEX_HEADER = r"""\documentclass[preview]{standalone}
\usepackage{lmodern}
\renewcommand{\familydefault}{\sfdefault}
\usepackage{amsmath,amssymb}
\usepackage{xcolor}
\newcommand{\TV}{d_{\mathrm{TV}}}
\newcommand{\Unif}{\mathrm{Unif}}
\newcommand{\cost}{\mathrm{cost}}
\newbox\preflightbox
\begin{document}
"""


def _tex_source(fragments: list[TexFragment]) -> str:
    pieces = [_TEX_HEADER]
    for index, fragment in enumerate(fragments):
        pieces.append(f"\\typeout{{TEX-PREFLIGHT-ENTRY {index}}}\n")
        if fragment.kind == "math":
            contents = r"\begin{align*}" + fragment.body + r"\end{align*}"
        else:
            contents = r"\begin{minipage}{10cm}\raggedright " + fragment.body + r"\end{minipage}"
        # A box typesets and expands the contents without accumulating pages.
        pieces.append(r"\setbox\preflightbox=\vbox{" + contents + "}\n")
    pieces.append(r"\end{document}" + "\n")
    return "".join(pieces)


def preflight_tex(paths: list[Path] | None = None, *, scenes: set[str] | None = None) -> int:
    """Compile all available static snippets; report the offending source line."""
    compiler = shutil.which("latex")
    if not compiler:
        raise RuntimeError("LaTeX preflight requires the 'latex' command used by Manim")
    fragments = collect_fragments(paths, scenes=scenes)
    if not fragments:
        return 0
    with tempfile.TemporaryDirectory(prefix="shuffleviz-tex-") as tmp:
        texfile = Path(tmp) / "preflight.tex"
        texfile.write_text(_tex_source(fragments))
        result = subprocess.run(
            [compiler, "-no-shell-escape", "-interaction=nonstopmode", "-halt-on-error", texfile.name],
            cwd=tmp,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            errors="replace",
            check=False,
        )
        if result.returncode != 0:
            output = result.stdout
            indices = re.findall(r"TEX-PREFLIGHT-ENTRY (\d+)", output)
            index = int(indices[-1]) if indices else None
            label = "unknown fragment"
            if index is not None and index < len(fragments):
                item = fragments[index]
                label = f"{item.path.name}:{item.line} ({item.kind}): {item.body[:180]}"
            error = re.search(r"^! .*?(?=\n(?:No pages of output|Transcript written|\Z))", output, re.M | re.S)
            diagnostic = (error.group(0) if error else "\n".join(output.splitlines()[-15:])).strip()
            raise RuntimeError(f"LaTeX preflight failed at {label}\n{diagnostic}")
    return len(fragments)


if __name__ == "__main__":
    print(f"LaTeX preflight: {preflight_tex()} static fragments compiled")
