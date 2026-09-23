#!/usr/bin/env bash
# Session setup for Lean Kernel Challenge work in a Claude Code cloud environment.
#
# Installs the Lean toolchain the challenge pins (via elan), makes it the default,
# clones the official challenge repository, and optionally pre-fetches Mathlib and
# the local evaluator. Safe to run repeatedly: every step is skipped when already done,
# and optional steps never fail the session.
#
# Optional environment variables:
#   LKC_WORK=<dir>            where to put the challenge checkout (default: $HOME/lkc)
#   LKC_PREFETCH_MATHLIB=1    also download Mathlib for fib, mertens, primecount (~2 GB each)
#   LKC_PREP_EVALUATOR=<id>   also prepare the local evaluator for one problem (e.g. partition)
#   SAIR_API_KEY              read by the solution scripts; set it as an environment secret,
#                             never in this file

set -uo pipefail

LEAN_TOOLCHAIN="leanprover/lean4:v4.33.1"
WORK="${LKC_WORK:-$HOME/lkc}"
log() { echo "[lkc-setup] $*"; }

# 1. elan and the pinned Lean toolchain
export PATH="$HOME/.elan/bin:$PATH"
if ! command -v elan >/dev/null 2>&1; then
  log "installing elan"
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -o /tmp/elan-init.sh \
    && sh /tmp/elan-init.sh -y --default-toolchain none >/dev/null \
    || { log "elan install failed"; exit 1; }
fi
if ! elan toolchain list 2>/dev/null | grep -q "v4.33.1"; then
  log "installing $LEAN_TOOLCHAIN"
  elan toolchain install "$LEAN_TOOLCHAIN" || { log "toolchain install failed"; exit 1; }
fi
elan default "$LEAN_TOOLCHAIN" >/dev/null 2>&1
grep -qs '.elan/bin' "$HOME/.bashrc" || echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$HOME/.bashrc"
log "lean: $(lean --version 2>/dev/null | head -1)"

# 2. helper tools used by the scripts (jq for API bodies, valgrind for instruction counts)
missing=""
for t in jq valgrind; do command -v "$t" >/dev/null 2>&1 || missing="$missing $t"; done
if [ -n "$missing" ]; then
  log "installing:$missing"
  (sudo -n true 2>/dev/null && SUDO=sudo || SUDO=""; $SUDO apt-get install -y -qq $missing >/dev/null 2>&1) \
    || log "could not install$missing (non-fatal)"
fi

# 3. the official challenge repository
mkdir -p "$WORK"
if [ ! -d "$WORK/lean-kernel-challenge/.git" ]; then
  log "cloning SAIRcompetition/lean-kernel-challenge into $WORK"
  git clone -q --depth 1 https://github.com/SAIRcompetition/lean-kernel-challenge "$WORK/lean-kernel-challenge" \
    || log "clone failed (non-fatal)"
fi

# 4. optional: Mathlib for the three Mathlib-based problems
if [ "${LKC_PREFETCH_MATHLIB:-0}" = "1" ] && [ -d "$WORK/lean-kernel-challenge" ]; then
  for p in fib mertens primecount; do
    d="$WORK/lean-kernel-challenge/problems/$p"
    if [ ! -d "$d/.lake/packages/mathlib" ]; then
      log "fetching Mathlib for $p"
      (cd "$d" && timeout 1800 python3 setup.py >/dev/null 2>&1 && timeout 1800 lake build Spec >/dev/null 2>&1) \
        || log "Mathlib fetch for $p failed (non-fatal)"
    fi
  done
fi

# 5. optional: local evaluator for one problem
if [ -n "${LKC_PREP_EVALUATOR:-}" ] && [ -d "$WORK/lean-kernel-challenge" ]; then
  log "preparing local evaluator for $LKC_PREP_EVALUATOR"
  (cd "$WORK/lean-kernel-challenge" && timeout 1800 bash evaluation/setup.sh --problem "$LKC_PREP_EVALUATOR" >/dev/null 2>&1) \
    || log "evaluator setup failed (non-fatal)"
fi

log "done"
exit 0
