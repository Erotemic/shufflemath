#!/usr/bin/env bash
# Targeted verification of the next-phase source overlay.
# The finite 2,401-pair native certificate is optional; pass --pair to check it.
set -euo pipefail

cd "$(dirname "$0")/.."
lake exe cache get
lake build \
  Shufflemath.FiberLifting \
  Shufflemath.BernoulliLaplaceSemantic \
  Shufflemath.GSR \
  Shufflemath.ProtocolCertificate \
  Shufflemath.OracleRefinement \
  Shufflemath.PhysicalRefinement \
  Shufflemath.CommanderPermutation \
  Shufflemath.CommanderFiberWitness \
  Shufflemath.CommanderFiberCount \
  Shufflemath.CommanderFiberMembership \
  Shufflemath.CommanderMembershipKernels \
  Shufflemath.CommanderPhysicalExchange \
  Shufflemath.FiberDisintegration \
  Shufflemath.PhysicalExchangeReduction \
  Shufflemath.CommanderFullDeckDisintegration \
  Shufflemath.ExchangeOverlap \
  Shufflemath.FinsetCombinatorics \
  Shufflemath.CommanderMembershipOrbits \
  Shufflemath.CommanderMembershipExchange \
  Shufflemath.CommanderA3Count \
  Shufflemath.CommanderA3Kernel \
  Shufflemath.CommanderA3UniformPushforward \
  Shufflemath.CommanderA3ExchangePushforward \
  Shufflemath.CommanderA3Mass \
  Shufflemath.CommanderA3KernelLaw \
  Shufflemath.CommanderA3ExchangeCard \
  Shufflemath.CommanderCostedCertificate \
  Shufflemath.TelescopeF5 \
  Shufflemath.CommanderMarkedRightCount \
  Shufflemath.CommanderLocalGSR \
  Shufflemath.CommanderDeckGSR \
  Shufflemath.Gate6BadLabels \
  Shufflemath.Gate6F \
  Shufflemath.Gate6Crux \
  Shufflemath.GSRDeckRound \
  Shufflemath.GSRGate6Telescope \
  Shufflemath.GSRSegMembership \
  Shufflemath.GSRSegFiber \
  Shufflemath.GSRSegHeadline \
  Shufflemath.FiniteDeck.Gate6TieRank \
  Shufflemath.FiniteDeck.RelabelInvariance \
  Shufflemath.FiniteDeck.A3KernelLaw \
  Shufflemath.FiniteDeck.BLDisintegration \
  Shufflemath.FiniteDeck.PositionAction \
  Shufflemath.FiniteDeck.ActionConvolution \
  Shufflemath.FiniteDeck.Piles \
  Shufflemath.FiniteDeck.Histograms \
  Shufflemath.FiniteDeck.HistogramFiber \
  Shufflemath.FiniteDeck.HistogramKernel \
  Shufflemath.FiniteDeck.PileEquiv \
  Shufflemath.FiniteDeck.MultiPileOrbit \
  Shufflemath.FiniteDeck.MultiPileExchange \
  Shufflemath.FiniteDeck.A1Witness \
  Shufflemath.K1Wall \
  Shufflemath.Gate6K1Capstone \
  Shufflemath.Gate6K1Bridges \
  Shufflemath.FiniteDeck.Partition \
  Shufflemath.FiniteDeck.Gate6ThreeRound \
  Shufflemath.FiniteDeck.Gate6Deterministic \
  Shufflemath.FiniteDeck.Gate6Row \
  Shufflemath.FiniteDeck.Gate6Corrected \
  Shufflemath.FiniteDeck.ChangingPiles

if [[ "${1:-}" == "--pair" ]]; then
  lake build Shufflemath.BernoulliLaplace
  lake env lean dev/BernoulliLaplacePairOptimality.lean
elif [[ "${1:-}" != "" ]]; then
  echo "Usage: $0 [--pair]" >&2
  exit 2
fi

python3 -m unittest discover -s tests -v
