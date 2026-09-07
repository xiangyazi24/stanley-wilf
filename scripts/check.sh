#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/check_sources.py
python3 -m unittest discover -s tests -p test_harness.py
python3 tests/test_small_cases.py --max-n 7
python3 tests/test_occurrence_split.py --max-n 6
if ! command -v lake >/dev/null 2>&1; then
  echo 'ERROR: lake is unavailable; Lean compilation and kernel audit NOT performed.' >&2
  exit 127
fi
mkdir -p build-logs
lake build 2>&1 | tee build-logs/lake-build.log
lake env lean tests/Smoke.lean 2>&1 | tee build-logs/smoke.log
lake env lean Audit.lean 2>&1 | tee build-logs/axioms.log
python3 scripts/check_axioms.py build-logs/axioms.log
