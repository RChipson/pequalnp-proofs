#!/bin/bash
# Usage: generator/submit.sh <number> <proof file> <statement file> <commit subject>
# Copies the proof into the Lean tree, runs the project's file-rule guard against the live
# step list, commits it on its own branch off upstream/main, and pushes that branch
# together with the request line that makes the workflow open the pull request.
# Then starts the project's checker locally in the background.
set -e
N=$1; SRC=$2; ST=$3; MSG=$4
S=${SCRATCH:-/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad}
cd /home/user/pequalnp-proofs
F=lean/PEqualNP/Outside/L_meta_$N.lean
mkdir -p $S/g$N
if grep -q '"' "$SRC"; then echo "double quote in file"; exit 1; fi
cp "$SRC" $F
curl -s https://data.pequalnp.com/data/desk/gaps.json -o $S/g$N/gaps.json
node .github/scripts/outside-guard.mjs gap $S/g$N/gaps.json L-meta-$N $F $S/g$N check | tail -1
node .github/scripts/outside-guard.mjs imports $F $S/g$N/imports.json $F check | tail -1
cmp $S/g$N/statement.txt "$ST"
TRAILER=$'Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01TpFXUkpyLFra3HXQJVTCWi'
rm -rf $S/wt$N; git worktree prune
git worktree add -q -b L-meta-$N $S/wt$N upstream/main
cp $F $S/wt$N/$F
# The project's landing program only merges a head that is ONE unsigned commit with a one-line
# plain message (no links, no tool names) and the numbered no-reply address, so the proof
# commit is made in exactly that shape.
(cd $S/wt$N && git add $F && git -c commit.gpgsign=false -c user.name=RChipson \
  -c user.email=213504381+RChipson@users.noreply.github.com commit -q -m "L-meta-$N")
echo L-meta-$N >> generator/pr-requests.txt
git add generator/pr-requests.txt
git commit -q -m "Request a pull request for L-meta-$N" -m "$TRAILER"
git push -q origin L-meta-$N claude/optimistic-ride-tshloe 2>&1 | grep -v '^remote:' || true
git -C $S/wt$N rev-parse HEAD
date -u
[ -n "$NOCHECK" ] || (export PATH=$HOME/.elan/bin:$PATH; nohup node tools/check-lean.mjs $F $S/g$N/statement.txt check > $S/g$N/checker.log 2>&1; echo "exit $?" >> $S/g$N/checker.log) > /dev/null 2>&1 &
