#!/bin/bash

sed -E 's/^(#(ifdef|endif))/\n\1/g' tmp/$1.c > tmp/$1.c1
cp benchmarks/common.h tmp/
cpp -DANNOTATIONS -traditional-cpp -C -P tmp/$1.c1 -o tmp/$1.ii

node ../Teaching.Verification.Project/ext/sindarin.js parse tmp/$1.ii -o tmp/$1.json > /dev/null
