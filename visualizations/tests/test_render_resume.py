"""Ensure resume mode cannot silently mix incomplete or stale scene outputs."""
import json
import os
from pathlib import Path

from shuffleviz import build_slides


def test_resume_reuses_matching_render_only(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(build_slides, "ROOT", tmp_path)
    source = tmp_path / "shuffleviz" / "slides_control_study.py"
    source.parent.mkdir()
    source.write_text("class OD15SearchVsCertificate: pass\n")
    video = tmp_path / "media" / "videos" / "slides_control_study" / "1080p30" / "OD15SearchVsCertificate.mp4"
    video.parent.mkdir(parents=True)
    video.write_bytes(b"mp4 placeholder")
    metadata = tmp_path / "slides-part4-control" / "OD15SearchVsCertificate.json"
    metadata.parent.mkdir()
    metadata.write_text(json.dumps({"slides": [{"file": str(video.relative_to(tmp_path))}]}))
    module = "shuffleviz.slides_control_study"
    check = lambda quality="h", fps=30: build_slides._cached_scene_ready(
        "part4-control", module, "OD15SearchVsCertificate", quality, fps
    )
    assert check()
    assert not check(fps=60)
    assert not check(quality="m")

    # The source was subsequently edited, so even intact video is stale.
    updated = metadata.stat().st_mtime + 1
    os.utime(source, (updated, updated))
    assert not check()
    os.utime(source, (metadata.stat().st_mtime - 1, metadata.stat().st_mtime - 1))
    assert check()

    video.unlink()
    assert not check()


def test_resume_rejects_bad_metadata(tmp_path: Path, monkeypatch):
    monkeypatch.setattr(build_slides, "ROOT", tmp_path)
    source = tmp_path / "shuffleviz" / "slides_control_study.py"
    source.parent.mkdir()
    source.write_text("# source\n")
    metadata = tmp_path / "slides-part4-control" / "OD15SearchVsCertificate.json"
    metadata.parent.mkdir()
    metadata.write_text("not JSON")
    assert not build_slides._cached_scene_ready(
        "part4-control", "shuffleviz.slides_control_study", "OD15SearchVsCertificate", "h", 30
    )
