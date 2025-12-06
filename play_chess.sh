#!/bin/bash
# Simple script to play chess
# Option 1: Use pre-built executable (faster startup)
# lake build && .lake/build/bin/chess
#
# Option 2: Run directly with Lean (no build needed)
echo "Starting Chess Game..."
lean --run Chess.lean
