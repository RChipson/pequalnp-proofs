#!/bin/bash
# Compile a proof file with the command of the brief, under a memory watch.
# usage: compile_watch.sh <file.lean> [anon limit in KB, default 6000000] [timeout s, default 1500]
export PATH=$HOME/.elan/bin:$PATH
F=$(readlink -f "$1"); LIM=${2:-6000000}; TO=${3:-1500}
log="${F%.lean}.compile.log"
rm -f "$log"
cd /tmp/claude-0/-home-user-pequalnp-proofs/740307a3-5578-556b-b545-0397351cd4f4/scratchpad/up/lean
( s=$(date +%s); flock /tmp/lean.lock timeout $TO lake env lean "$F" > "$log" 2>&1; echo "EXIT $? TIME $(( $(date +%s) - s ))s" >> "$log" ) &
peak=0; pf=0
until grep -q "^EXIT" "$log" 2>/dev/null; do
  for p in $(pgrep -f "lean $F"); do
    m=$(grep RssAnon /proc/$p/status 2>/dev/null | awk '{print $2}')
    f=$(grep RssFile /proc/$p/status 2>/dev/null | awk '{print $2}')
    [ -n "$f" ] && [ "$f" -gt "$pf" ] && pf=$f
    if [ -n "$m" ]; then
      [ "$m" -gt "$peak" ] && peak=$m
      if [ "$m" -gt "$LIM" ]; then kill -9 $p; echo "KILLED by the memory watch at $m KB" >> "$log"; fi
    fi
  done
  sleep 1
done
echo "peak anonymous memory: $((peak/1024)) MB (mapped library files: $((pf/1024)) MB)" >> "$log"
grep -v "linter\|Note: This" "$log" | cut -c1-500 | tail -${4:-12}
