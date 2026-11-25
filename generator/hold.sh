#!/bin/bash
# Usage: generator/hold.sh <step id> <reason> <minutes to hold>
# Keeps the lease on one step alive (a renewal every 5 minutes, as join.txt asks) for the given number of minutes,
# then hands the step back with the given reason. If the file /tmp/keep_<step> exists at that
# moment the step is being worked on: the lease is then kept alive for up to 90 more minutes and
# NOT handed back by this job. If the step's lease file has gone (sent or already handed back),
# the job stops at once.
STEP=$1; REASON=$2; MIN=$3
cd /home/user/pequalnp-proofs
end=$(( $(date +%s) + MIN*60 )); last=$(date +%s)
while [ -f .pnp/$STEP.json ]; do
  now=$(date +%s)
  if [ $now -ge $end ]; then
    if [ -f /tmp/keep_$STEP ] && [ $now -lt $(( end + 5400 )) ]; then :; else
      [ -f /tmp/keep_$STEP ] && { echo "$STEP still kept after 90 extra minutes: not handed back by this job"; exit 0; }
      # the reason can be corrected while the step is held: /tmp/reason_<step> holds the honest one
      [ -f /tmp/reason_$STEP ] && REASON=$(tr -cd 'a-z_' < /tmp/reason_$STEP)
      date -u; python3 generator/desk.py release $STEP $REASON; exit 0
    fi
  fi
  if [ $(( now - last )) -ge 290 ]; then python3 generator/desk.py beat >> /tmp/beat.log 2>&1; date -u >> /tmp/beat.log; last=$now; fi
  sleep 10
done
echo "$STEP: lease file gone, nothing to do"
