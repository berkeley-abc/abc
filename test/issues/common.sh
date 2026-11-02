#!/usr/bin/env bash
# Shared setup for command-level regressions. Run from the repository root.
set -eu
ABC=${ABC:-./abc}
case "$ABC" in /*) ;; *) ABC="$PWD/$ABC" ;; esac
issue_tmp=$(mktemp -d)
trap 'rm -rf "$issue_tmp"' EXIT
cd "$issue_tmp"

run_abc() {
    "$ABC" -s -c "$1" > abc.log 2>&1 || { cat abc.log; exit 1; }
}

expect_log() {
    grep -Eq "$1" abc.log || { cat abc.log; echo "Missing: $1" >&2; exit 1; }
}
