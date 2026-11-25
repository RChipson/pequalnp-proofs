#!/bin/bash
# Usage: generator/sixinput/refute_held.sh <held false step> <its twin's id>
# For a held "False: ... six-input ..." step whose twin somebody has already sent: prove the twin
# here (never sent), and if the proof compiles hand the held step back as statement_seems_false.
HELD=$1; TWIN=$2
S=/tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad
cd /home/user/pequalnp-proofs
[ -f .pnp/$HELD.json ] || { echo "$HELD is not held"; exit 0; }
OUT=$S/desk/six/auto/$(echo $TWIN | tr '-' '_').lean
python3 generator/sixinput/gen6.py $TWIN $S/desk/six/auto/stmt_$TWIN.txt $OUT || { echo "$TWIN: generator gave no proof"; exit 1; }
export PATH=$HOME/.elan/bin:$PATH
if (cd $S/up/lean && flock /tmp/lean.lock timeout 1500 lake env lean $OUT 2>&1 | grep -q error); then echo "$TWIN: does not compile"; exit 1; fi
[ -f .pnp/$HELD.json ] && python3 generator/desk.py release $HELD statement_seems_false
