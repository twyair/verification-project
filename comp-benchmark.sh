#!/bin/bash

cpp -DANNOTATIONS -P "benchmarks/$1.c" -o /tmp/"$1".ii

node ../Teaching.Verification.Project/ext/sindarin.js parse /tmp/"$1".ii -o benchmarks/"$1".json > /dev/null