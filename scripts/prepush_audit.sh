#!/usr/bin/env bash
# Copyright 2026 - Present Light Transport Entertainment Inc.
# SPDX-License-Identifier: MIT
#
# Prepush audit: secret-token scan of the commits that would be pushed.
# Runs gitleaks (rule/entropy based) and trufflehog (verified + unverified
# detections) over the same range, plus a narrow regex heuristic as a fallback
# when a scanner is unavailable. Any finding blocks the push.
#
# Usage:
#   bash scripts/prepush_audit.sh                 # commits in BASE..HEAD
#   bash scripts/prepush_audit.sh --full-history  # whole repository history
#
# Override the comparison base with PREPUSH_BASE=<rev> (useful when no upstream
# is configured). Tool discovery: gitleaks on PATH; trufflehog on PATH then
# ~/go/bin/trufflehog.
#
# Exit codes: 0 clean, 1 findings, 2 cannot determine the range,
# 77 neither scanner installed (regex fallback still ran clean).

set -uo pipefail
cd "$(dirname "$0")/.."

ran=0
fail=0
full=0
[ "${1:-}" = "--full-history" ] && full=1

BRANCH="$(git rev-parse --abbrev-ref HEAD)"
BASE="${PREPUSH_BASE:-}"

if [ -z "$BASE" ]; then
    if git rev-parse --verify --quiet "origin/$BRANCH" >/dev/null 2>&1; then
        BASE="$(git merge-base HEAD "origin/$BRANCH")"
    elif git rev-parse --verify --quiet origin/main >/dev/null 2>&1; then
        BASE="$(git merge-base HEAD origin/main)"
    else
        echo "prepush-audit: cannot determine push base; set PREPUSH_BASE=<rev>" >&2
        exit 2
    fi
fi

if [ "$full" -eq 1 ]; then
    RANGE="all history"
    DIFF_RANGE="$(git rev-list --max-parents=0 HEAD | head -1)..HEAD"
    GITLEAKS_RANGE_ARGS=()
    SINCE_ARGS=()
    REV_LIST="$(git rev-list HEAD)"
else
    RANGE="$BASE..HEAD"
    DIFF_RANGE="$RANGE"
    GITLEAKS_RANGE_ARGS=(--log-opts="$RANGE")
    SINCE_ARGS=(--since-commit="$BASE" --branch="$BRANCH")
    REV_LIST="$(git rev-list "$RANGE")"
fi
echo "prepush-audit: scanning $RANGE ($(printf '%s\n' "$REV_LIST" | grep -c .) commits)"

# --- narrow regex heuristic (also the fallback when scanners are missing) ---
# Patterns are deliberately specific to avoid flagging documentation/example
# text; scanners below are the authoritative check.
if [ -n "$REV_LIST" ]; then
    if git diff "$DIFF_RANGE" -U0 2>/dev/null | grep -nE \
        'ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9]{20,}|AKIA[0-9A-Z]{16}|-----BEGIN (RSA |OPENSSH |EC |DSA )?PRIVATE KEY-----' \
        >/dev/null; then
        echo "prepush-audit: regex heuristic found a token-like string" >&2
        fail=1
    fi
fi

# --- gitleaks ---
if command -v gitleaks >/dev/null 2>&1; then
    echo "prepush-audit: gitleaks over $RANGE"
    if ! gitleaks detect --source . --redact --no-banner "${GITLEAKS_RANGE_ARGS[@]}"; then
        echo "prepush-audit: gitleaks reported findings" >&2
        fail=1
    fi
    ran=1
else
    echo "note: gitleaks not installed; skipping (https://github.com/gitleaks/gitleaks)" >&2
fi

# --- trufflehog ---
# Its go-git backend cannot follow a worktree's .git file, so point it at the
# main worktree when running from a linked worktree.
TH="$(command -v trufflehog || true)"
if [ -z "$TH" ] && [ -x "$HOME/go/bin/trufflehog" ]; then
    TH="$HOME/go/bin/trufflehog"
fi
if [ -n "$TH" ]; then
    REPO="$PWD"
    GITDIR="$(git rev-parse --absolute-git-dir)"
    case "$GITDIR" in
        */.git/worktrees/*)
            REPO="$(git worktree list --porcelain | awk '/^worktree /{print $2; exit}')"
            ;;
    esac
    echo "prepush-audit: trufflehog over $RANGE"
    # --fail makes unverified detections fatal too: a token that fails live
    # verification is still a leak.
    if ! "$TH" git "file://$REPO" --no-update --fail "${SINCE_ARGS[@]}"; then
        echo "prepush-audit: trufflehog reported findings" >&2
        fail=1
    fi
    ran=1
else
    echo "note: trufflehog not installed (PATH, ~/go/bin); skipping" >&2
fi

if [ "$ran" -eq 0 ]; then
    echo "prepush-audit: SKIP (no scanner installed; regex fallback only)"
    [ "$fail" -eq 0 ] && exit 77 || exit 1
fi
if [ "$fail" -ne 0 ]; then
    echo "prepush-audit: FINDINGS - do not push" >&2
    exit 1
fi
echo "prepush-audit: clean"
exit 0
