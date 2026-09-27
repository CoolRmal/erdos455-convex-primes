#!/usr/bin/env bash
# Time every checker bundled with the toolchain on an export of the given declarations.
# Usage: scripts/bench_checkers.sh <Module> <decl>...   (run inside a built Lake project)
set -euo pipefail
mod=$1; shift
BIN=$(dirname "$(elan which lean)")
tmp=$(mktemp -d)
EXTRA="Quot Quot.mk Quot.lift Quot.ind propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"
# The same extra declarations `lake comparator` exports alongside the checked ones.
lake env "$BIN/leanexport" "$mod" -- "$@" $EXTRA > "$tmp/export.ndjson"
ls -la "$tmp/export.ndjson" | awk '{print "export size:", $5}'
cat > "$tmp/nanoda.json" <<JSON
{"use_stdin": false, "export_file_path": "$tmp/export.ndjson", "permitted_axioms": ["propext","Quot.sound","Classical.choice"],
 "unpermitted_axiom_hard_error": false, "num_threads": 4, "nat_extension": true, "string_extension": true}
JSON
t() { local name=$1; shift; local s=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())');
  /usr/bin/time -l "$@" > "$tmp/$name.log" 2>&1 && st=ok || st=FAIL
  local e=$(python3 -c 'import time;print(time.time())')
  rss=$(grep "maximum resident" "$tmp/$name.log" | awk '{printf "%.0fMB", $1/1048576}')
  printf "%-16s %-5s %8.1fs  %s\n" "$name" "$st" "$(python3 -c "print($e-$s)")" "$rss"; }
t leanchecker "$BIN/leanchecker" --silent --from-export "$tmp/export.ndjson"
t nanoda "$BIN/nanoda_bin" "$tmp/nanoda.json"
t con-ron "$BIN/con-ron" "$tmp/export.ndjson"
if [[ "${ALL:-0}" == 1 ]]; then
  t paranoid "$BIN/leanchecker-paranoid" --silent --from-export "$tmp/export.ndjson"
  t lean4lean "$BIN/lean4lean" --import "$tmp/export.ndjson"
  t con-leche "$BIN/con-leche" "$tmp/export.ndjson"
fi
rm -rf "$tmp"
