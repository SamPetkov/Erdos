#!/usr/bin/env bash
# Release replay driver. Runs each audited command, preserving stdout, stderr,
# and exit code separately. Never edits any source file.
set -u
cd "$(dirname "$0")/../.." || exit 2
R=replay/release-replay-824e4b6
L=$R/logs
mkdir -p "$L"

run() {
  local tag="$1"; shift
  echo "[$(date -u +%FT%TZ)] BEGIN $tag: $*" | tee -a "$R/timeline.txt"
  local start=$SECONDS
  "$@" > "$L/$tag.stdout.log" 2> "$L/$tag.stderr.log"
  local rc=$?
  local dur=$((SECONDS - start))
  echo "$rc" > "$L/$tag.exit-code.txt"
  printf '%s\t%s\t%s\t%ss\n' "$tag" "$*" "exit=$rc" "$dur" >> "$R/summary.tsv"
  echo "[$(date -u +%FT%TZ)] END   $tag exit=$rc duration=${dur}s" | tee -a "$R/timeline.txt"
  return 0
}

: > "$R/summary.tsv"
run 00_cache_get lake exe cache get
run 01_lake_build_wfail lake build --wfail
run 02_Section12ConcreteSignedFirstMoment lake env lean -DwarningAsError=true Erdos625/Section12ConcreteSignedFirstMoment.lean
run 03_Section12PartialDiagonalAssembly lake env lean -DwarningAsError=true Erdos625/Section12PartialDiagonalAssembly.lean
run 04_Section15FinalInstantiation lake env lean -DwarningAsError=true Erdos625/Section15FinalInstantiation.lean
run 05_Erdos625 lake env lean -DwarningAsError=true Erdos625.lean
run 06_AxiomAudit lake env lean -DwarningAsError=true Erdos625/AxiomAudit.lean
run 07_Erdos625SelfContained lake env lean -DwarningAsError=true Erdos625SelfContained.lean
echo "[$(date -u +%FT%TZ)] ALL DONE" | tee -a "$R/timeline.txt"
