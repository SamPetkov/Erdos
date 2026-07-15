#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"

# 11 July 2026, 12:00:00 UTC.  LuaTeX reads SOURCE_DATE_EPOCH when
# FORCE_SOURCE_DATE is set, making the embedded PDF creation/modification
# dates reproducible.
export SOURCE_DATE_EPOCH=1783771200
export FORCE_SOURCE_DATE=1

# Keep the LuaTeX font cache local to a writable temporary directory.
export TEXMFVAR="${TEXMFVAR:-${TMPDIR:-/tmp}/erdos593-texmf-cache}"
export TEXMFCACHE="${TEXMFCACHE:-$TEXMFVAR}"
mkdir -p "$TEXMFVAR"

python3 generate_tex.py
rm -f erdos593_obligatory_triple_systems.{aux,bbl,bcf,blg,fdb_latexmk,fls,log,out,run.xml,toc}
lualatex -interaction=nonstopmode -halt-on-error erdos593_obligatory_triple_systems.tex
biber erdos593_obligatory_triple_systems
lualatex -interaction=nonstopmode -halt-on-error erdos593_obligatory_triple_systems.tex
lualatex -interaction=nonstopmode -halt-on-error erdos593_obligatory_triple_systems.tex
