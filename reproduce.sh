#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")" && pwd)"
BUILD="$ROOT/_repro"
rm -rf "$BUILD"
mkdir -p "$BUILD/python" "$BUILD/gmp"

python3 "$ROOT/verification/verify_c3a_two_temperature_121418.py" \
  --emit "$BUILD/python"

python3 "$ROOT/verification/test_universal_quotient_small.py"

CXX="${CXX:-c++}"
GMP_CPPFLAGS=()
GMP_LDFLAGS=(-lgmpxx -lgmp)

if ! printf '#include <gmpxx.h>\n' | \
    "$CXX" -x c++ -std=c++20 -E - >/dev/null 2>&1; then
  if command -v brew >/dev/null 2>&1; then
    GMP_PREFIX="$(brew --prefix gmp 2>/dev/null || true)"
  else
    GMP_PREFIX=""
  fi

  if [[ -n "$GMP_PREFIX" && -f "$GMP_PREFIX/include/gmpxx.h" ]]; then
    GMP_CPPFLAGS+=("-I$GMP_PREFIX/include")
    GMP_LDFLAGS=("-L$GMP_PREFIX/lib" -lgmpxx -lgmp)
  else
    printf '%s\n' \
      'GMP headers were not found. Install libgmp-dev (Debian/Ubuntu) or brew install gmp (macOS).' >&2
    exit 1
  fi
fi

"$CXX" -O2 -Wall -Wextra -pedantic -std=c++20 \
  "${GMP_CPPFLAGS[@]}" \
  "$ROOT/verification/verify_c3a_two_temperature_121418_gmp.cpp" \
  "${GMP_LDFLAGS[@]}" -o "$BUILD/verify_gmp"

"$BUILD/verify_gmp" --emit "$BUILD/gmp"

for name in mask.txt sum_support.txt difference_costs.tsv N.txt L.txt; do
  cmp "$ROOT/certificate/$name" "$BUILD/python/$name"
  cmp "$ROOT/certificate/$name" "$BUILD/gmp/$name"
done

printf '%s\n' 'BYTE-FOR-BYTE CERTIFICATE COMPARISON: PASS'
printf '%s\n' 'COMPLETE REPRODUCTION: PASS'
