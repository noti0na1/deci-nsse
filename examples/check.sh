#!/bin/sh
# Run the Lean solver on every example, compare with the known answer, and
# recheck its certificate with nsse-check. Run from the repository root after
# `lake build`.
status=0
tmp=$(mktemp)
for entry in arrow:true deep-context:true infinite-tree:false mixed-ternary:true \
    modular:false nullary:true periodic:true reverse:false transitivity:true; do
  name=${entry%%:*}
  want=${entry##*:}
  out=$(.lake/build/bin/nsse "examples/$name.json" --no-countermodel 2>/dev/null)
  printf '%s\n' "$out" > "$tmp"
  case $out in
    *"\"answer\":$want"*'"used_fallback":false'*)
      if .lake/build/bin/nsse-check "examples/$name.json" "$tmp" > /dev/null; then
        echo "ok      $name"
      else
        echo "FAILED  $name: certificate rejected"; status=1
      fi ;;
    *) echo "FAILED  $name: $(printf '%s' "$out" | cut -c1-120)"; status=1 ;;
  esac
done
rm -f "$tmp"
exit $status
