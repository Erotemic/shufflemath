"""Compile real slide source literals with LaTeX before costly Manim rendering."""
from pathlib import Path
import shutil

import pytest

from shuffleviz.tex_preflight import collect_fragments, preflight_tex


def test_static_tex_source_coverage():
    fragments = collect_fragments()
    assert fragments
    assert {f.kind for f in fragments} == {"tex", "math", "para"}
    assert any(f.kind == "para" and "Search layer" in f.body for f in fragments)
    assert any(f.kind == "para" and "Simplex" in f.body for f in fragments)


@pytest.mark.skipif(shutil.which("latex") is None, reason="LaTeX not installed")
def test_static_tex_compiles():
    assert preflight_tex() == len(collect_fragments())


@pytest.mark.skipif(shutil.which("latex") is None, reason="LaTeX not installed")
def test_static_tex_errors_identify_the_source(tmp_path: Path):
    source = tmp_path / "slides_bad.py"
    source.write_text(
        'class BadSlide:\n'
        '    title = r"$\\alpha$"\n'
        '    def body(self):\n'
        r'        para(r"\textbf{Bad}\nEnumerate", 4, 20)' + "\n"
    )
    with pytest.raises(RuntimeError, match=r"(?s)slides_bad\.py:4.*Undefined control sequence"):
        preflight_tex([source])
