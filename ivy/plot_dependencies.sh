#!/bin/bash

FILE=$1
NAME=${FILE%.*}
cd /home/user/shared
# analyze file using 2 threads:
python /home/user/poison-ivy/poisonivy.py $FILE 2
# make png file:
dot -Tpng -o $NAME-invariants.png $NAME.dot
echo "finished"
