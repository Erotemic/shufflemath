#!/usr/bin/env bash
set -euo pipefail

lake update
lake build
python -m unittest discover -s tests -v
