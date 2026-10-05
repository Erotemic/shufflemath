shufflemath riffle-title overlay

This overlay improves the classical seven-riffle Manim deck so the opening and
mechanics scenes visibly resemble a riffle shuffle.

Included changes
- add a new animation-first opening scene: `C00TitleRiffleHero`
- make the title slide show an actual split-into-two-hands and interleave-back-together riffle
- make `C02RiffleMechanicsLab` cut into visibly slanted packets before interleaving
- include the new hero scene in the classical deck order
- include the hero scene in `make mechanics`
- update the visualization README to document the new opening

Apply from the repository root, e.g. `~/code/shufflemath`:

    tar -xzf ~/Downloads/shufflemath-riffle-title-overlay.tar.gz -C .

Then validate:

    cd visualizations
    make test
    make lint
    make mechanics QUALITY=l JOBS=1

The first scene to inspect is `C00TitleRiffleHero`.
