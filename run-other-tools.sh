#!/bin/bash

timeout="300s"
timestamp=$(date '+%Y-%m-%d_%H%m')
log_dir="logs/"

mkdir -p ${log_dir}

# Print header row
printf "Running tests with timeout ${timeout} (logs in ${log_dir})...\n\n"

printf "%-30s %12s %12s\n" "Name" "Forester" "Predator"

for fname in `ls tests/forester/`
do
    printf "%-30s " $fname
    for tool_name in forester predator
    do
	log_dirname="${log_dir}/${tool_name}/"
	mkdir -p ${log_dirname}
	log_fname="${log_dirname}/${fname}.out"

	case $tool_name in
	    forester)
		cmd="/home/siddharth/forester/fa_build/fagcc";;
	    predator)
		cmd="/home/siddharth/predator/sl_build/slgcc";;
	    *)
		echo "Unknown tool ${tool_name}"
		exit 1;;
	esac

	timeout ${timeout} ${cmd} tests/forester/${fname} &> ${log_fname}

	RET_CODE=$?
	last_line=$(tail -n 1 ${log_fname})
	if [[ (${RET_CODE} -ne 0) || ($last_line =~ "FAIL") ]] ; then
            printf "%12s" "FAIL"
	else
	    printf "%12s" "OK"
	fi
    done
    printf "\n"
done
