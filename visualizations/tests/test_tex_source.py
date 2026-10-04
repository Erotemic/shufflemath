"""Static checks for common Python/raw-string -> LaTeX escaping mistakes."""
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
