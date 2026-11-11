#!/bin/bash
cd /home/al/dev/MOSP
check() { id=$1; d=reports/scratch/obstruction_search/13_pass1/certificates/$id; nice -n 19 python3 paper1/obstruction_check.py check-minor $d/instance.txt $d/minor.json --c-cap 120 --no-rulefree --json > reports/scratch/pass1_floors/check_$id.json 2>&1; echo "$id $(python3 -c "import json;d=json.load(open('reports/scratch/pass1_floors/check_$id.json'));print(d['verdict'],d['c_ok'])" 2>/dev/null || echo error)"; }
export -f check
xargs -a reports/scratch/pass1_floors/ids.txt -P 8 -I{} bash -c 'check {}' > reports/scratch/pass1_floors/verify.out 2>&1
echo VERIFY-DONE >> reports/scratch/pass1_floors/verify.out
