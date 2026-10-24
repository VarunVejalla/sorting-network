#!/bin/bash
# Run the jobs in jobs.txt (one shell command per line, run from rd731/) with at most MAXP of MY python
# processes at once (counts python processes visible to this msys session, i.e. the ones started here).
cd "$(dirname "$0")"
MAXP=${MAXP:-6}
while IFS= read -r line; do
  [ -z "$line" ] && continue
  case "$line" in \#*) continue;; esac
  while [ "$(ps -ef | grep -i 'python' | grep -v grep | wc -l)" -ge "$MAXP" ]; do sleep 20; done
  echo "$(date '+%F %T') start: $line" >> queue.log
  nohup bash -c "$line" > /dev/null 2>&1 &
  sleep 5
done < "${1:-jobs.txt}"
echo "$(date '+%F %T') queue drained" >> queue.log
