#!/bin/bash
# n = 10 in eight residue classes of geng, each at nice 19
cd /home/al/dev/MOSP/reports/scratch/layout_second_moment
for k in 0 1 2 3 4 5 6 7; do
  ( nice -n 19 nauty-geng -q 10 $k/8 > bin/g10_$k.g6 && nice -n 19 nauty-countg -V --a -2 -q bin/g10_$k.g6 | awk '{print $4}' > bin/a10_$k.txt && nice -n 19 bin/layout_moment_enum 10 bin/g10_$k.g6 bin/a10_$k.txt > enum_n10_part$k.csv 2> bin/enum10_$k.log ) &
done
wait
echo done > bin/run10.done
