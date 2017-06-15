#!/bin/bash

timeout="300s"
runmode=$1
if [[ -z $runmode ]] ; then runmode="cricket"; fi
no_cricket="sls_double_all.spl sls_pairwise_sum.spl sls_strand_sort.spl list_of_lists_split_traverse.spl list_of_lists_traverse.spl list_of_trees_traverse.spl tree_of_lists_traverse.spl"

timestamp=$(date '+%Y-%m-%d_%H%M')
log_dir="logs/${runmode}-${timestamp}/"

mkdir -p ${log_dir}

# Also redirect all output to $log_dir/summary.txt
exec &> >(tee "${log_dir}/summary.txt")

# Print header row
printf "Running ${runmode} tests with timeout ${timeout} (logs in ${log_dir})...\n\n"
printf "%-32s %12s %12s %12s %12s %12s\n" "Name" "Platypus" "Loc-GHP" "Beetle" "Btl-GHP" "Total"

for fname in `ls tests/spl/cricket/`
do
    printf "%-32s " $fname
    log_fname="${log_dir}/${fname}.out"

    if [[ $no_cricket =~ $fname ]] && [[ $runmode = "cricket" ]] ; then
        mode_flag="-locust"
    else
        mode_flag="-${runmode}"
    fi
   
    timeout ${timeout} ./grasshopper.native ${mode_flag} \
             -cricket-log-level 3 \
             tests/spl/cricket/${fname} \
             > ${log_fname} 2>&1

    RET_CODE=$?
    if [[ ${RET_CODE} -eq 0 ]] ; then
        stat_line=$(grep 'Program succesfully verified' ${log_fname})
        total_time=$(echo ${stat_line} | sed -n 's/.*\[\([0-9][0-9]*\.[0-9]*\)s total.*/\1/p')
        platy_time=$(echo ${stat_line} | sed -n 's/.*, \([0-9][0-9]*\.[0-9]*\)s platypus.*/\1/p')
        loc_ghp_time=$(echo ${stat_line} | sed -n 's/.*, \([0-9][0-9]*\.[0-9]*\)s locust-grasshopper.*/\1/p')
        btl_time=$(echo ${stat_line} | sed -n 's/.*, \([0-9][0-9]*\.[0-9]*\)s beetle,.*/\1/p')
        btl_ghp_time=$(echo ${stat_line} | sed -n 's/.*, \([0-9][0-9]*\.[0-9]*\)s beetle-grasshopper.*/\1/p')
        if [[ -z $platy_time ]] ; then
            platy_time="N/A"
        fi
        if [[ -z $loc_ghp_time ]] ; then
            loc_ghp_time="N/A"
        fi
        if [[ -z $btl_time ]] ; then
            btl_time="N/A"
        fi
        if [[ -z $btl_ghp_time ]] ; then
            btl_ghp_time="N/A"
        fi

        printf "%12s %12s %12s %12s \e[32m%12s\e[0m\n" \
            $platy_time $loc_ghp_time $btl_time $btl_ghp_time $total_time
    elif [[ ${RET_CODE} -eq 124 ]] ; then
        printf "\e[31mTO\e[0m\n"
    else
        printf "\e[31mFAIL\e[0m "
        tail -n 1 ${log_fname}
    fi
done
