#!/bin/bash
# Build the programs, rewrite outputs/ and rerun the checks.  Run from anywhere; needs gcc, g++, Python 3.10 or later
# with sympy, and the folder ../reading-family/scripts of this repository (for export_local_data.py and check_c.py).
set -euo pipefail
cd "$(dirname "$0")/.."
make -s -C c
make -s -C cpp mockup
mkdir -p outputs
for d in D211 D109 D2 D3 D18 D15 D2357; do
    c/classical data/$d.txt > outputs/classical_$d.txt
    c/iut data/$d.txt > outputs/iut_$d.txt
    (cd cpp && ./mockup ../data/$d.txt > ../outputs/mockup_$d.txt && ./mockup --selftest ../data/$d.txt > ../outputs/selftest_$d.txt)
done
for d in D211 D109 D2 D3 D18 D15; do
    (cd cpp && ./mockup --scan ../data/$d.txt 40 > ../outputs/scan40_$d.txt)
done
(cd cpp && ./mockup --scan ../data/D211.txt 20 > ../outputs/scan_D211.txt)
tmp=$(mktemp -d)
python3 scripts/export_local_data.py ../reading-family/scripts "$tmp" > outputs/export_local_data.txt
diff -r data "$tmp"
echo "data/ is reproduced exactly by export_local_data.py" >> outputs/export_local_data.txt
rm -r "$tmp"
python3 scripts/check_c.py ../reading-family/scripts c data > outputs/check_c.txt
python3 scripts/check_cpp.py > /dev/null
echo "run_all.sh: all checks passed"
