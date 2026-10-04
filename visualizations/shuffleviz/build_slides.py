"""Render and assemble shufflemath Manim-slide decks.

Examples
--------
python -m shuffleviz.build_slides shufflemath-short --quality l --pdf --handout
python -m shuffleviz.build_slides shufflemath-study --quality l
python -m shuffleviz.build_slides shufflemath-advanced-math --quality l
python -m shuffleviz.build_slides shufflemath-full --quality h --fps 30 --pdf --handout
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import importlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

from shuffleviz.palette import OUTPUT_SUFFIX

ROOT = Path(__file__).resolve().parents[1]

FOUNDATIONS = "shuffleviz.slides_foundations"
CLASSICAL = "shuffleviz.slides_classical"
CLASSICAL_STUDY = "shuffleviz.slides_classical_study"
LARGE = "shuffleviz.slides_large_decks"
LARGE_STUDY = "shuffleviz.slides_large_decks_study"
REALISM = "shuffleviz.slides_realism"
REALISM_STUDY = "shuffleviz.slides_realism_study"
CONTROL = "shuffleviz.slides_control"
CONTROL_STUDY = "shuffleviz.slides_control_study"
ROADMAP = "shuffleviz.slides_roadmap"
ROADMAP_STUDY = "shuffleviz.slides_roadmap_study"
MODULES = [
    FOUNDATIONS,
    CLASSICAL, CLASSICAL_STUDY,
    LARGE, LARGE_STUDY,
    REALISM, REALISM_STUDY,
    CONTROL, CONTROL_STUDY,
    ROADMAP, ROADMAP_STUDY,
]

HERO = "riffle-hero"
SHORT = "shufflemath-short"
STUDY = "shufflemath-study"
FULL = "shufflemath-full"
GLOSSARY = "shufflemath-glossary"
ADVANCED = "shufflemath-advanced-math"
PARTS = {
    "part0-foundations": [
        "F00StudyCourse", "F01StateSpace", "F02Distribution", "F03PermutationConvention",
        "F04RandomVariableAndLaw", "F04BProjectionAndLumping", "F05MarkovKernel", "F06MatrixUpdate", "F07KernelComposition",
        "F08Stationary", "F09Reversible", "F10TVDefinition", "F11TVEventForm",
        "F12TVContraction", "F13MarkovEigenfunction", "F14MixingTime", "F15Cutoff",
        "F16FoundationsGlossary",
    ],
    "part1-classical": [
        "C00TitleRiffleHero",
        "CS00ClassicalNotation",
        "C00SevenShuffles",
        "C01RandomIsADistribution",
        "CS01TVReminder",
        "C01EntropyLowerBound",
        "C02RiffleMechanicsLab",
        "C02GSRForwardMechanics",
        "C03WhyInvert",
        "C04InverseRiffleLab",
        "C04InverseBinaryLabels",
        "CS05DescentDefinition",
        "C05RisingSequenceLab",
        "C05RisingSequences",
        "C06OneRiffleAlreadyPredictsTheFormula",
        "C07CompositionLab",
        "C07RepeatedRifflesBecomeOneAShuffle",
        "C08TargetPermutationBecomesInequalities",
        "CS09StarsAndBarsPrimer",
        "C09CountCompatibleLabels",
        "C10BayerDiaconisProbabilityFormula",
        "C11SanityCheckOnFiveCards",
        "CS12EulerianDefinition",
        "C12EulerianNumbers",
        "C12EulerianInsertionRecurrence",
        "CS13TVClassCollapsePrimer",
        "C13FiftyTwoFactorialCollapsesTo52Terms",
        "C14UniformMomentsFromIndicators",
        "C14WhatUniformLooksLikeInRisingSequences",
        "C15WatchTheRiffleDistributionApproachUniform",
        "CS16LikelihoodRatioPrimer",
        "C16LikelihoodRatioIsMonotone",
        "C16TotalVariationBecomesAGuessingGame",
        "C17TheExact52CardTable",
        "CS18CutoffReminder",
        "C18DiscoverTheThreeHalvesScale",
        "C19WhatSevenActuallyMeans",
        "C20ClassicalRoadmap",
        "CS21ClassicalGlossary",
    ],
    "part2-large-decks": [
        "LD00PartPrimer",
        "L01WorkingSet",
        "LD01NestoridiWhiteProcedure",
        "LD02PerfectLocalOracle",
        "LD03MembershipMicrostates",
        "LD04DefineStateX",
        "LD05HypergeometricPrimer",
        "LD06StationaryCounting",
        "LD07ExchangeVariables",
        "LD08TransitionDerivation",
        "LD09ToyExample",
        "LD10RowStochastic",
        "LD11DetailedBalanceDefinition",
        "LD12DetailedBalanceToy",
        "LD13ReversibilityStationarity",
        "LD14ConditionalExpectation",
        "LD15FirstEigenfunction",
        "LD16LambdaInterpretation",
        "LD17CommanderParameters",
        "L05K25",
        "L06CommanderTV",
        "LD18ProjectionFullDeckCaveat",
        "LD19MixingTheorems",
        "LD19ACoupling",
        "LD19BPathCoupling",
        "LD19CSpectralDecomposition",
        "LD19D4SelfAdjointProof",
        "LD19D2SymmetryReduction",
        "LD19D3GelfandPairPrimer",
        "LD19DDualHahn",
        "LD19ESecondMomentLowerBound",
        "L07UnequalUrns",
        "LD21SKBlockDynamicsDeep",
        "L08BlockDynamics",
        "LD20LargeDeckGlossary",
    ],
    "part3-realism": [
        "RD00PartPrimer",
        "RD01BiasedTwoShuffle",
        "RD02InverseBiasedLabels",
        "RD03GeneralPShuffle",
        "RD04CompositionTensor",
        "RD05CollisionProbability",
        "RD06SSTDefinition",
        "RD06StrongUniformTime",
        "RD06AExactFulmanBound",
        "RD07DistanceMetrics",
        "RD08BiasedCutLiterature",
        "RD08A0QuasisymmetricPrimer",
        "RD08AQuasisymmetricBridge",
        "RD08CDescentPositionMatters",
        "RD08BExtremalPermutations",
        "RD09CutBiasVsClumping",
        "RD10CorrelatedSource",
        "RD11RunLength",
        "RD12Nonexchangeability",
        "RD13JonassonMorrisTheorem",
        "RD14GeneralCutLaw",
        "RD15ModelInterfaces",
        "RD16RealismGlossary",
    ],
    "part4-control": [
        "OD00PartPrimer",
        "OD01ProtocolComposition",
        "OD02OracleProtocol",
        "OD03KernelDistance",
        "OD04KernelDistanceProof",
        "OD05CommonSuffixContraction",
        "OD06ThreeStepTelescope",
        "OD07GeneralTelescope",
        "OD08DobrushinDefinition",
        "OD09DobrushinContraction",
        "OD10WeightedTelescope",
        "OD10AWeightedTelescopeProof",
        "OD11TotalErrorBudget",
        "OD12CostModel",
        "OD13OptimizationProblem",
        "OD14ParetoDominance",
        "OD15SearchVsCertificate",
        "OD16RobustOptimization",
        "OD17OperationalTheorem",
        "OD18ControlGlossary",
    ],
    "part5-roadmap": [
        "MD00RoadmapPrimer",
        "M01LiteratureMap",
        "MD01DependencyDAG",
        "MD02MathLeanDictionary",
        "M02Status",
        "MD03BLFormalTargets",
        "M03BLTheorems",
        "MD04GSRFormalTargets",
        "M04GSRTheorems",
        "MD05CompositionFormalTargets",
        "M05Composition",
        "M06ProtocolCertificates",
        "MD06RealismFormalTargets",
        "M07RealismRoadmap",
        "MD07WhatNotToFormalizeFirst",
        "MD08ProofVsComputation",
        "M08EndToEnd",
        "MD09StudyChecklist",
        "MD10MasterGlossary",
        "M09Closing",
    ],
}
PART_TITLES = {
    "part0-foundations": "Part 0 · mathematical foundations",
    "part1-classical": "Part 1 · classical riffle foundations",
    "part2-large-decks": "Part 2 · large decks and Bernoulli--Laplace",
    "part3-realism": "Part 3 · more realistic local shuffles",
    "part4-control": "Part 4 · the costed working-set control problem",
    "part5-roadmap": "Part 5 · formalization roadmap",
}
ALL_PARTS = list(PARTS)
GLOSSARY_SCENES = [
    "F16FoundationsGlossary",
    "CS21ClassicalGlossary",
    "LD20LargeDeckGlossary",
    "RD16RealismGlossary",
    "OD18ControlGlossary",
    "MD10MasterGlossary",
]
ADVANCED_SCENES = [
    "LD19ACoupling", "LD19BPathCoupling", "LD19CSpectralDecomposition", "LD19D4SelfAdjointProof",
    "LD19D2SymmetryReduction", "LD19D3GelfandPairPrimer", "LD19DDualHahn", "LD19ESecondMomentLowerBound",
    "RD06SSTDefinition", "RD06AExactFulmanBound", "RD08A0QuasisymmetricPrimer", "RD08AQuasisymmetricBridge",
    "RD08CDescentPositionMatters", "RD08BExtremalPermutations", "OD08DobrushinDefinition", "OD09DobrushinContraction",
    "OD10WeightedTelescope", "OD10AWeightedTelescopeProof",
]
DECK_SCENES = {
    HERO: ["C00TitleRiffleHero"],
    SHORT: list(PARTS["part1-classical"]),
    GLOSSARY: GLOSSARY_SCENES,
    ADVANCED: ADVANCED_SCENES,
    **PARTS,
    STUDY: [scene for scenes in PARTS.values() for scene in scenes],
    FULL: [scene for scenes in PARTS.values() for scene in scenes],
}
COMPOSITES = {
    STUDY: ALL_PARTS,
    FULL: ALL_PARTS,
}
DECKS = list(DECK_SCENES)


def output_name(deck: str) -> str:
    return deck + OUTPUT_SUFFIX


def _module_of() -> dict[str, str]:
    owner: dict[str, str] = {}
    for module in MODULES:
        mod = importlib.import_module(module)
        for name, obj in vars(mod).items():
            if isinstance(obj, type) and getattr(obj, "__module__", None) == module and hasattr(obj, "construct"):
                owner[name] = module
    return owner


def deck(name: str) -> list[tuple[str, list[str]]]:
    owner = _module_of()
    grouped: dict[str, list[str]] = {}
    for scene in DECK_SCENES[name]:
        if scene not in owner:
            raise KeyError(f"deck {name!r} names unknown scene {scene!r}")
        grouped.setdefault(owner[scene], []).append(scene)
    return list(grouped.items())


def _run(*args: str) -> None:
    cmd = [sys.executable, "-m", "manim_slides", *args]
    print("+", " ".join(cmd), flush=True)
    subprocess.run(cmd, cwd=ROOT, check=True, env=dict(os.environ))


def _render_scene(deck_name: str, module: str, scene: str, quality: str, fps: float | None) -> float:
    source = Path(importlib.import_module(module).__file__).relative_to(ROOT)
    cmd = [sys.executable, "-m", "manim_slides", "render", f"--quality={quality}"]
    if fps:
        cmd.append(f"--fps={fps:g}")
    cmd += [str(source), scene]
    log = ROOT / "renders" / "logs" / f"{output_name(deck_name)}--{scene}.log"
    log.parent.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "SHUFFLEVIZ_DECK": deck_name}
    start = time.monotonic()
    with open(log, "w") as out:
        result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    if result.returncode:
        tail = "\n".join(log.read_text(errors="replace").splitlines()[-30:])
        raise RuntimeError(f"{deck_name}/{scene} failed (log: {log}):\n{tail}")
    return time.monotonic() - start


def render(deck_names: list[str], quality: str, fps: float | None = None, only: list[str] | None = None, jobs: int | None = None) -> None:
    tasks = [
        (name, module, scene)
        for name in deck_names
        for module, scenes in deck(name)
        for scene in scenes
        if not only or scene in only
    ]
    jobs = jobs or os.cpu_count() or 1
    print(f"rendering {len(tasks)} scenes, {jobs} at a time", flush=True)
    with ThreadPoolExecutor(jobs) as pool:
        futures = {pool.submit(_render_scene, *task, quality, fps): task for task in tasks}
        try:
            for done, future in enumerate(as_completed(futures), 1):
                name, _, scene = futures[future]
                print(f"[{done}/{len(tasks)}] {name}/{scene} ({future.result():.0f} s)", flush=True)
        except BaseException:
            pool.shutdown(cancel_futures=True)
            raise


def assemble(deck_name: str) -> None:
    folder = ROOT / f"slides-{output_name(deck_name)}"
    folder.mkdir(exist_ok=True)
    for stale in folder.glob("*.json"):
        stale.unlink()
    for part in COMPOSITES[deck_name]:
        for scene in DECK_SCENES[part]:
            src = ROOT / f"slides-{output_name(part)}" / f"{scene}.json"
            if not src.exists():
                raise FileNotFoundError(f"{src} is missing; render {part} first")
            (folder / src.name).write_text(src.read_text())


def write_handout(deck_name: str, out: Path) -> None:
    """Write static summary pages, omitting animation-only scenes.

    A scene can opt out with ``handout = False`` when its explanatory content is
    carried by motion rather than its final frame. This lets the live deck use
    genuinely dynamic mechanics while neighboring summary scenes remain useful
    on paper.
    """
    from PIL import Image

    folder = ROOT / f"slides-{output_name(deck_name)}"
    owner = _module_of()
    pages = []
    with tempfile.TemporaryDirectory() as tmp:
        for k, scene in enumerate(DECK_SCENES[deck_name]):
            scene_cls = getattr(importlib.import_module(owner[scene]), scene)
            if not getattr(scene_cls, "handout", True):
                continue
            slides = json.loads((folder / f"{scene}.json").read_text())["slides"]
            drawn = [s for s in slides if not s.get("src")]
            frame = Path(tmp) / f"{k:03d}.png"
            subprocess.run(
                ["ffmpeg", "-loglevel", "error", "-sseof", "-0.5", "-i", str(ROOT / drawn[-1]["file"]), "-update", "1", "-y", str(frame)],
                check=True,
            )
            pages.append(Image.open(frame).convert("RGB"))
    if not pages:
        raise RuntimeError(f"deck {deck_name!r} has no handout-enabled scenes")
    first, *rest = pages
    first.save(out, save_all=True, append_images=rest, resolution=first.width / 13.333)
    print(f"wrote {out} ({len(pages)} summary pages)")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("deck", choices=DECKS)
    parser.add_argument("-q", "--quality", default="h", choices=list("lmhpk"))
    parser.add_argument("--fps", type=float)
    parser.add_argument("-j", "--jobs", type=int)
    parser.add_argument("--scenes", nargs="+")
    parser.add_argument("--list", action="store_true")
    parser.add_argument("--no-render", action="store_true")
    parser.add_argument("--render-only", action="store_true", help="render selected scenes and stop before conversion")
    parser.add_argument("--html", type=Path)
    parser.add_argument("--one-file", action="store_true")
    parser.add_argument("--pdf", action="store_true")
    parser.add_argument("--pptx", action="store_true")
    parser.add_argument("--handout", action="store_true")
    args = parser.parse_args()

    names = DECK_SCENES[args.deck]
    if args.list:
        print(" ".join(names))
        return

    if not args.no_render:
        render(COMPOSITES.get(args.deck, [args.deck]), args.quality, fps=args.fps, only=args.scenes, jobs=args.jobs)
    if args.render_only:
        return
    if args.deck in COMPOSITES:
        assemble(args.deck)

    renders = ROOT / "renders"
    renders.mkdir(exist_ok=True)
    out = output_name(args.deck)
    html = args.html or renders / f"{out}.html"
    folder = ["--folder", f"slides-{out}"]
    convert = ["convert", *folder, "--to", "html", *names, str(html), "-cslide_number=true", "-ccontrols=true"]
    if args.one_file:
        convert.insert(1, "--one-file")
    _run(*convert)
    if args.pdf:
        _run("convert", *folder, "--to", "pdf", *names, str(renders / f"{out}.pdf"))
    if args.pptx:
        _run("convert", *folder, "--to", "pptx", *names, str(renders / f"{out}.pptx"))
    if args.handout:
        write_handout(args.deck, renders / f"{out}.handout.pdf")

    print(f"\nPresent live:  manim-slides present --folder slides-{out} {' '.join(names)}")
    print(f"Or open:       {html}")


if __name__ == "__main__":
    main()
