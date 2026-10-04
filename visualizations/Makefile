# Build the shufflemath Manim presentation. Run from visualizations/.
#
#   make                 # list targets
#   make all             # classical + full six-part study course, 1080p30
#   make final           # full 1080p60 build
#   make short           # deep derivation of the classical seven-riffle result
#   make part2           # one literature/model section (part0 ... part5)
#   make study           # complete foundations-to-formalization study course
#   make glossary        # glossary/checkpoint scenes only
#   make advanced        # complex proof-tool / advanced-math scenes only
#   make full            # render parts in parallel, assemble the full deck
#   make short QUALITY=l # fast draft
#   make full SCENES="L05K25 L06CommanderTV"  # re-render selected scenes
#   make full THEME=light # printable light deck
#   make standalone      # single-file HTML for every deck
#   make handout         # one-static-page-per-scene PDFs
#
# Outputs live under renders/; rendered scene metadata lives under slides-<deck>/.

UV      ?= uv
RUN     := $(UV) run --extra slides --extra test
QUALITY ?= h
FPS     ?= $(if $(filter l m,$(QUALITY)),,30)
JOBS    ?=
PDF     ?= 1
SCENES  ?=
THEME   ?= dark
export SHUFFLEVIZ_THEME := $(THEME)
SUFFIX  := $(if $(filter dark,$(THEME)),,-$(THEME))

BUILD_FLAGS := --quality $(QUALITY) $(if $(FPS),--fps $(FPS)) $(if $(JOBS),--jobs $(JOBS)) \
               $(if $(filter 1,$(PDF)),--pdf --handout) $(if $(SCENES),--scenes $(SCENES))

DECK_hero  := riffle-hero
DECK_short := shufflemath-short
DECK_study := shufflemath-study
DECK_full  := shufflemath-full
DECK_glossary := shufflemath-glossary
DECK_advanced := shufflemath-advanced-math
DECK_part0 := part0-foundations
DECK_part1 := part1-classical
DECK_part2 := part2-large-decks
DECK_part3 := part3-realism
DECK_part4 := part4-control
DECK_part5 := part5-roadmap
PARTS      := part0 part1 part2 part3 part4 part5
DECKS      := hero short study full glossary advanced $(PARTS)

.DEFAULT_GOAL := help
.PHONY: help setup all final draft rebuild mechanics $(DECKS) parts standalone handout test lint clean distclean \
        $(addprefix standalone-,$(DECKS)) $(addprefix handout-,$(DECKS)) $(addprefix present-,$(DECKS)) $(addprefix clean-,$(DECKS))

help:
	@awk '/^#/ { sub(/^# ?/, ""); print; next } { exit }' $(firstword $(MAKEFILE_LIST))
	@echo; echo 'Targets:'
	@echo '  setup              uv sync with slides + test extras'
	@echo '  all                classical + complete detailed study course'
	@echo '  final              all at 1080p60'
	@echo '  hero               render/export only the physical riffle title animation'
	@echo '  short              deep classical seven-riffle derivation'
	@echo '  study              complete detailed six-part study course'
	@echo '  glossary           six glossary/checkpoint scenes only'
	@echo '  advanced           complex coupling/spectral/quasisymmetric/Dobrushin scenes'
	@echo '  mechanics          render only the animation-first shuffle mechanics labs'
	@echo '  part0 ... part5    foundations / classical / large decks / realism / control / roadmap'
	@echo '  full               every part, then assembled full deck'
	@echo '  standalone         self-contained HTML for every deck'
	@echo '  handout            static one-page-per-scene PDFs'
	@echo '  present-<deck>     present a built deck live'
	@echo '  test               exact-model tests'
	@echo '  lint               syntax-check all Python sources'
	@echo 'Variables: QUALITY=l|m|h|p|k  FPS=30|60  JOBS=n  PDF=0|1  SCENES="..."  THEME=dark|light'

setup:
	$(UV) sync --extra slides --extra test

all: short study

final:
	$(MAKE) all FPS=60

draft:
	$(MAKE) all QUALITY=l PDF=0

mechanics:
	$(RUN) python -m shuffleviz.build_slides $(DECK_part1) --quality $(QUALITY) \
	    $(if $(FPS),--fps $(FPS)) $(if $(JOBS),--jobs $(JOBS)) --render-only \
	    --scenes C00TitleRiffleHero C02RiffleMechanicsLab C04InverseRiffleLab C05RisingSequenceLab C07CompositionLab C15WatchTheRiffleDistributionApproachUniform

rebuild:
	$(MAKE) clean
	$(MAKE) all

hero short glossary advanced $(PARTS):
	$(RUN) python -m shuffleviz.build_slides $(DECK_$@) $(BUILD_FLAGS)

parts: $(PARTS)

study:
	$(RUN) python -m shuffleviz.build_slides $(DECK_study) $(BUILD_FLAGS)

full:
	$(RUN) python -m shuffleviz.build_slides $(DECK_full) $(BUILD_FLAGS)
	for part in $(foreach p,$(PARTS),$(DECK_$(p))); do \
	    $(RUN) python -m shuffleviz.build_slides $$part --no-render $(if $(filter 1,$(PDF)),--pdf --handout) || exit 1; \
	done

standalone: $(addprefix standalone-,$(DECKS))

$(addprefix standalone-,$(DECKS)):
	$(RUN) python -m shuffleviz.build_slides $(DECK_$(@:standalone-%=%)) --no-render --one-file \
	    --html renders/$(DECK_$(@:standalone-%=%))$(SUFFIX).standalone.html

handout: $(addprefix handout-,$(DECKS))

$(addprefix handout-,$(DECKS)):
	$(RUN) python -m shuffleviz.build_slides $(DECK_$(@:handout-%=%)) --no-render --handout

$(addprefix present-,$(DECKS)):
	$(RUN) manim-slides present --folder slides-$(DECK_$(@:present-%=%))$(SUFFIX) \
	    $$($(RUN) python -m shuffleviz.build_slides $(DECK_$(@:present-%=%)) --list)

$(addprefix clean-,$(DECKS)):
	rm -rf slides-$(DECK_$(@:clean-%=%))$(SUFFIX) renders/$(DECK_$(@:clean-%=%))$(SUFFIX).* renders/$(DECK_$(@:clean-%=%))$(SUFFIX)_assets

test:
	$(RUN) pytest -q tests

lint:
	python -m py_compile shuffleviz/*.py tests/*.py

clean:
	rm -rf renders slides slides-* media/videos media/images media/texts

distclean: clean
	rm -rf media .pytest_cache .ruff_cache .venv
