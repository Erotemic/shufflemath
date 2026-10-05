# shufflemath visualizations

A Manim / `manim-slides` presentation that explains the mathematical roadmap
behind `shufflemath`, independent of the Lean proof build.

The layout deliberately follows the Davis--Kahan visualization project:

- semantic colors are stable across every scene;
- explanatory scenes may use motion as part of the mathematics rather than pretending every frame is a static slide;
- animation-first mechanics labs are paired with neighboring static summary scenes;
- builds can be presented interactively, exported to HTML/PDF/PPTX, or collected
  into a static summary handout that omits scenes marked animation-only;
- full talks are assembled from independently renderable parts;
- scene rendering is parallel but the Manim LaTeX/SVG cache is cross-process locked;
- exact numerical graphics are driven by small checked Python models rather than
  hard-coded plotting coordinates.

## Story

The full deck has five parts:

1. **Classical riffles** — GSR inverse labels, repeated `a`-shuffles, exact TV,
   Bayer--Diaconis.
2. **Large decks** — Nestoridi--White, Bernoulli--Laplace, the 50-state
   Commander projection, unequal urns, and `S_k` block dynamics.
3. **Human realism** — biased cuts, Fulman, Assaf--Diaconis--Soundararajan,
   Jonasson--Morris clumpy/dealer shuffles, and broad cut-size laws.
4. **Our combined control problem** — finite local shuffle error, cross-pile
   mixing, telescoping TV bounds, heterogeneous physical costs, robust
   parameters, and bounded protocol optimization.
5. **Formalization roadmap** — what is implemented, what should be symbolic,
   which literature results need finite formal interfaces, and where search
   ends and Lean certification begins.

The **short deck is now intentionally deep rather than broad**: it is the full
classical seven-riffle derivation.  It starts from the 52-card puzzle and an
entropy lower bound that only predicts five, then walks through the physical
GSR move, inversion, independent labels, rising sequences, stars-and-bars,
Eulerian numbers (including the insertion recurrence), the exact TV collapse,
the uniform run-count mean/variance, the monotone likelihood-ratio witness,
the 52-card table, and the $\tfrac32\log_2 n$ cutoff heuristic.

The mechanics are now deliberately animated rather than diagrammed. The deck now opens with a title-scene hero riffle that visibly splits a packet into two hands and interleaves them back together. Dedicated
lab scenes then show an eight-card cut and card-by-card interleave; the inverse
construction as independent bits followed by a stable sort; a scan that discovers
rising sequences from the stable-sort output; and two inverse riffles composing
into one stable sort by two-bit addresses. The exact run-count distribution also
morphs from five to eight riffles rather than accumulating static curves. Only
the full deck proceeds to large decks and our extensions.

## Semantic colors

| color role | meaning |
|---|---|
| blue | finite local shuffle / mash |
| amber | cross-working-set exchange |
| green | uniform target / certified success |
| pink | residual nonuniformity / TV error |
| violet | physical cost / optimization |
| cyan | perfect-local oracle used in prior idealized models |
| vermilion | empirical / human-behavior parameter |

Set `SHUFFLEVIZ_THEME=light` (or `make ... THEME=light`) for a printable light
variant. Theme outputs get a `-light` suffix and do not overwrite the dark deck.

## Setup

```bash
cd visualizations
uv sync --extra slides --extra test
```

Manim also needs the usual Cairo/Pango/FFmpeg/LaTeX host packages.

## Build

```bash
make short QUALITY=l        # fast draft of the complete seven-riffle derivation
make mechanics QUALITY=l    # fast render of the title riffle + animation-heavy mechanics labs
make short                  # 1080p30 + PDF + static-summary handout
make part2                  # large-deck / BL section only
make full                   # all five parts + assembled full deck
make full SCENES="L05K25 L06CommanderTV"
make handout                # regenerate static handouts without rerendering
make standalone             # self-contained HTML
make final                  # 1080p60
make full THEME=light
```

Present a built deck:

```bash
make present-short
make present-full
```

Exact-model checks:

```bash
make test
make lint
```

## Static handouts

`make short` and `make full` write both the normal exported PDF and a
`*.handout.pdf`. Live/HTML presentation is the primary medium for mechanics.
Scenes with `handout = False` are intentionally animation-first and are omitted
from the handout; the neighboring summary scenes carry the corresponding static
mathematics. This lets us use motion when motion is explanatory without making
the printable document incoherent.

## Numerical status

`shuffleviz/model.py` independently recomputes the small exact numbers used by
the deck (GSR TV values and the 50-state Commander Bernoulli--Laplace chain).
The tests pin these against the exact values already reproduced by the main
repository. These graphics support intuition; they do not replace Lean proofs.
