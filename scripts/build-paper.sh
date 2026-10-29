#!/usr/bin/env bash
# Rebuild the paper from its Markdown source. Requires Pandoc and Tectonic.
set -euo pipefail
cd "$(dirname "$0")/.."
# The Markdown title/author/date are supplied by the metadata below.
awk '/^## / { body = 1 } body' c3a_two_temperature_proof.md | \
"${PANDOC:-pandoc}" \
  --from=markdown+tex_math_single_backslash --to=latex --standalone \
  --metadata='title:Two-temperature cyclic compression for the Gyarmati-Hennecart-Ruzsa constant' \
  --metadata='author:Carson Olafson' \
  --metadata='date:August 19, 2026; finite-proof revision October 29, 2026' \
  --variable=fontsize:10pt --variable=geometry:margin=1in \
  --variable=colorlinks:true \
  --output=c3a_two_temperature_proof.tex
"${TECTONIC:-tectonic}" --keep-logs c3a_two_temperature_proof.tex
