"""Static checks for common Python/raw-string -> LaTeX escaping mistakes."""
import ast
import re
from pathlib import Path


def test_no_double_escaped_latex_ampersands():
    source_dir = Path(__file__).parents[1] / "shuffleviz"
    offenders = []
    needle = r"\\&"
    for path in sorted(source_dir.glob("*.py")):
        for lineno, line in enumerate(path.read_text().splitlines(), 1):
            if needle in line:
                offenders.append(f"{path.name}:{lineno}: {line.strip()}")
    assert not offenders, (
        "Use r'\\&' in raw Python strings for a literal LaTeX ampersand; "
        "r'\\\\&' becomes a LaTeX linebreak followed by an illegal alignment '&'.\n"
        + "\n".join(offenders)
    )


def test_riffle_code_does_not_introspect_mobject_angle():
    source = (Path(__file__).parents[1] / "shuffleviz" / "slides_classical.py").read_text()
    assert ".get_angle()" not in source, (
        "Manim VGroup has no readable angle property. Track riffle card orientation "
        "explicitly with riffle_angle instead."
    )


def test_slide_headings_put_mathematics_in_math_mode():
    """Title/kicker strings are passed to ``Tex``, not ``MathTex``.

    TeX math-only macros and unescaped subscripts/superscripts must be inside
    ``$...$`` or ``make final`` fails only after reaching the affected scene.
    """
    source_dir = Path(__file__).parents[1] / "shuffleviz"
    math_only = re.compile(
        r"(?<!\\)[_^]"
        r"|\\(?:langle|rangle|mathbf|mathbb|mathcal|mathrm|frac|dfrac|tfrac|"
        r"binom|sum|prod|sup|otimes|cdots|cdot|le|ge|pi|lambda|Delta|delta|"
        r"mu|sigma|alpha|beta|Omega|Theta|infty|in|ldots|subseteq)\b"
    )
    offenders = []
    for path in sorted(source_dir.glob("slides_*.py")):
        for node in ast.walk(ast.parse(path.read_text())):
            if not isinstance(node, (ast.Assign, ast.AnnAssign)):
                continue
            targets = node.targets if isinstance(node, ast.Assign) else [node.target]
            if not any(isinstance(t, ast.Name) and t.id in {"title", "kicker"} for t in targets):
                continue
            if not isinstance(node.value, ast.Constant) or not isinstance(node.value.value, str):
                continue
            source = node.value.value
            chunks = re.split(r"(?<!\\)\$", source)
            if len(chunks) % 2 == 0 or any(math_only.search(chunk) for chunk in chunks[::2]):
                offenders.append(f"{path.name}:{node.lineno}: {source}")

    assert not offenders, "Slide title/kicker TeX must keep math inside $...$:\n" + "\n".join(offenders)


def test_slide_strings_have_no_python_escape_control_characters():
    r"""Non-raw ``\varepsilon`` / ``\to`` silently decode to control characters."""
    bad_control = re.compile(r"[\x00-\x09\x0b-\x1f]")
    source_dir = Path(__file__).parents[1] / "shuffleviz"
    offenders = []
    for path in sorted(source_dir.glob("slides_*.py")):
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Constant) and isinstance(node.value, str):
                match = bad_control.search(node.value)
                if match:
                    offenders.append(
                        f"{path.name}:{node.lineno}: {match.group()!r} in {node.value[:90]!r}"
                    )
    assert not offenders, "Possible TeX escapes decoded by Python:\n" + "\n".join(offenders)
