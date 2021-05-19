#!/bin/bash

sed -E 's/^(#(ifdef|endif))/\n\1/g' benchmarks/$1.c > /tmp/$1.c
cp benchmarks/common.h /tmp/
cpp -DANNOTATIONS -traditional-cpp -C -P /tmp/$1.c -o /tmp/$1.ii


node ../Teaching.Verification.Project/ext/sindarin.js parse /tmp/$1.ii -o benchmarks/$1.json > /dev/null

rm /tmp/$1.c /tmp/$1.ii
