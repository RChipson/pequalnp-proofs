#!/bin/bash
# Usage: generator/submit.sh <step id, e.g. L-meta-5006 or R-meta-5006-1> <proof file>
# Sends one proof (or reduction) exactly as https://pequalnp.com/join.txt asks:
#   - only for a step we hold a live lease on (.pnp/<step>.json, written by generator/desk.py);
#   - the lease is renewed once first, and nothing is sent if the desk answers 410;
#   - the project's own file-rule guard is run against the live step list;
#   - one branch named after the step, ONE unsigned commit whose message is the step id,
#     one file, made off upstream/main with the numbered no-reply address;
#   - the request line (the step id, the lease id for the pull request's Lease line, and the word types when the file declares its own data types or
#     instances) makes the fork's workflow open the pull request;
#   - once the desk shows the pull request, the lease is released with reason submitted
#     (reason reduced for a reduction).
# Set NOCHECK=1 to skip the local run of the project's checker afterwards.
set -e
ID=$1; SRC=$2
# one submission at a time: the request file is committed in the shared working tree
exec 9>/tmp/submit_sh.lock; flock 9
S=${SCRATCH:-/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad}
cd /home/user/pequalnp-proofs
case "$ID" in
  L-*) STEP=$ID;;
  R-*) STEP=L-$(echo "$ID" | cut -d- -f2-3);;
  *) echo "not a step id: $ID"; exit 1;;
esac
[ -f .pnp/$STEP.json ] || { echo "no live lease on $STEP: nothing is sent"; exit 1; }
F=lean/PEqualNP/Outside/$(echo "$ID" | tr '-' '_').lean
# a value step's file is named after the value claimed (set by: generator/desk.py value <step> <k>)
if [ "${ID#L-}" != "$ID" ]; then
  LF=$(python3 -c "import json;print(json.load(open('.pnp/$STEP.json'))['gap'].get('file') or '')")
  echo "$LF" | grep -Eq '^lean/PEqualNP/Outside/[A-Za-z0-9_]+\.lean$' && F=$LF
fi
W=$S/send-$ID; mkdir -p $W
if grep -q '"' "$SRC"; then echo "double quote in file"; exit 1; fi
[ "$(wc -c < "$SRC")" -le 524288 ] || { echo "file larger than 512 KiB"; exit 1; }

# renew once before sending; a 410 means the step is settled or withdrawn
LEASE=$(python3 -c "import json;print(json.load(open('.pnp/$STEP.json'))['lease']['id'])")
CODE=$(curl -sS -m 30 -o $W/beat.json -w '%{http_code}' -X POST "https://pequalnp.com/desk/beat?lease=$LEASE")
[ "$CODE" = 200 ] || { echo "the desk answered $CODE to the renewal: not sending"; exit 1; }

git fetch -q upstream main
# the project's stop notice, and its rule that a recorded proof is final
if git cat-file -e upstream/main:STOP 2>/dev/null; then echo "STOPPED by a notice on the proofs repository: nothing is sent"; exit 120; fi
if git cat-file -e upstream/main:$F 2>/dev/null; then echo "$ID was just proved by someone else (its file is on main): nothing is sent"; exit 1; fi
# the file is read from a copy in the scratch folder; nothing is written into the repository's working tree
COPY=$W/proof.lean; cp "$SRC" $COPY
curl -s https://data.pequalnp.com/data/desk/gaps.json -o $W/gaps.json
if [ "${ID#L-}" != "$ID" ]; then
  # the project's current guard, read from its main branch
  git show upstream/main:.github/scripts/outside-guard.mjs > $W/outside-guard.mjs
  node $W/outside-guard.mjs gap $W/gaps.json $ID $F $W check | tail -1
  node $W/outside-guard.mjs imports $COPY $W/imports.json $F check | tail -1
  python3 -c "import json;open('$W/lease-statement.txt','w').write(json.load(open('.pnp/$STEP.json'))['gap']['statement'])"
  cmp $W/statement.txt $W/lease-statement.txt
fi
NOTE=""
if grep -Eq '^[[:space:]]*(private |protected )?(inductive|structure|instance|class)[[:space:]]' "$SRC"; then NOTE=" types"; fi

TRAILER=$'Co-Authored-By: Claude Fable 5.2 <noreply@anthropic.com>\nClaude-Session: https://claude.ai/code/session_01TpFXUkpyLFra3HXQJVTCWi'
rm -rf $W/wt; git worktree prune; git branch -D $ID 2>/dev/null || true
# ONE unsigned commit with the one file on top of the project's main branch, made without a checkout
# (the project tree is large; a checkout cost many seconds)
WHO=RChipson; MAIL=213504381+RChipson@users.noreply.github.com
BLOB=$(git hash-object -w $COPY)
rm -f $W/index
GIT_INDEX_FILE=$W/index git read-tree upstream/main
GIT_INDEX_FILE=$W/index git update-index --add --cacheinfo 100644,$BLOB,$F
TREE=$(GIT_INDEX_FILE=$W/index git write-tree)
COMMIT=$(GIT_AUTHOR_NAME=$WHO GIT_AUTHOR_EMAIL=$MAIL GIT_COMMITTER_NAME=$WHO GIT_COMMITTER_EMAIL=$MAIL git commit-tree $TREE -p upstream/main -m "$ID")
[ "$(git diff --name-only upstream/main $COMMIT)" = "$F" ] || { echo "the commit does not hold exactly the one file"; exit 1; }
git branch -f $ID $COMMIT
echo "$ID $LEASE$NOTE" >> generator/pr-requests.txt
git add generator/pr-requests.txt
git commit -q -m "Request a pull request for $ID" -m "$TRAILER"
# both branches in one push: the proof branch, and the request that makes the fork's workflow open the pull request
PUSHED=""
for i in 1 2 3 4; do git push -q origin $ID claude/optimistic-ride-tshloe && { PUSHED=1; break; }; sleep $((2**i)); done
[ -n "$PUSHED" ] || { echo "the push was refused four times: NOT sent (is there already a branch $ID on the fork?)"; exit 1; }
echo "pushed $ID at $(git rev-parse --short $COMMIT)$NOTE, $(date -u)"

# wait until the desk shows the pull request, then report it.  The lock is given up first; with BG_RELEASE=1
# the wait runs in the background (the lease stays on its renewal job until the release), so that the caller
# can go on to its next step.
flock -u 9; exec 9>&-
REASON=submitted; [ "${ID#R-}" != "$ID" ] && REASON=reduced
wait_and_release() {
  for i in $(seq 1 90); do
    sleep 10
    # our own pull request, not somebody else's on the same step
    if [ "$(gh api -X GET search/issues -f q="repo:open-goat/pequalnp-proofs is:pr author:RChipson in:title $ID" --jq '[.items[] | select(.title == "'$ID'")] | length' 2>/dev/null)" = 1 ]; then
      python3 generator/desk.py release $STEP $REASON; break
    fi
    [ $i = 90 ] && echo "no pull request seen after 15 minutes: lease NOT released, look at the workflow run"
  done
}
if [ -n "$BG_RELEASE" ]; then
  ( wait_and_release > /tmp/release_$ID.log 2>&1 & )
  echo "release of $STEP follows in the background once the pull request shows"
  exit 0
fi
wait_and_release
if [ -z "$NOCHECK" ] && [ "${ID#L-}" != "$ID" ]; then
  cp "$SRC" $F
  (export PATH=$HOME/.elan/bin:$PATH; flock /tmp/lean.lock node tools/check-lean.mjs $F $W/statement.txt check > $W/checker.log 2>&1; echo "exit $?" >> $W/checker.log; rm -f $F) > /dev/null 2>&1 &
  rm -f $F
fi
