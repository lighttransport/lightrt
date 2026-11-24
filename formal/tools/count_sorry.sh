#!/bin/sh
# Exact count of `sorry` placeholders in the library (comments excluded).
# Usage: tools/count_sorry.sh [--max N]   (fails if the count exceeds N)
cd "$(dirname "$0")/.." || exit 2
n=$(grep -rn --include='*.lean' -E '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' LightRT CDiff.lean \
      | grep -vE '^[^:]+:[0-9]+:\s*--' | grep -v 'uses `sorry`' | wc -l)
echo "sorry count: $n"
grep -rn --include='*.lean' -E '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)' LightRT \
  | grep -vE '^[^:]+:[0-9]+:\s*--' | awk -F: '{print "  " $1}' | sort | uniq -c
if [ "$1" = "--max" ] && [ "$n" -gt "$2" ]; then
  echo "error: sorry count $n exceeds budget $2" >&2; exit 1
fi
