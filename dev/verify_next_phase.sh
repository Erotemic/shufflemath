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
  Shufflemath.CommanderPermutation

if [[ "${1:-}" == "--pair" ]]; then
  lake build Shufflemath.BernoulliLaplace
  lake env lean dev/BernoulliLaplacePairOptimality.lean
elif [[ "${1:-}" != "" ]]; then
  echo "Usage: $0 [--pair]" >&2
  exit 2
fi

python3 -m unittest discover -s tests -v
