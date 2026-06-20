#!/usr/bin/env bash

echo "file,expected_status,expected_result,pgeon_result,pgeon_time,pgeon_ok,twb_result,twb_time,twb_ok,same"

expected_status_from_file() {
    awk -F'expected: ' '/\/\* expected:/ { sub(/[[:space:]]*\*\/.*/, "", $2); print $2; exit }' "$1"
}

expected_result_for_status() {
    case "$1" in
        Theorem|Unsatisfiable) printf 'Close' ;;
        NonTheorem|Satisfiable) printf 'Open' ;;
        *) printf 'Unknown' ;;
    esac
}

for pgeon_file in problems/pgeon/*.pgeon; do
    [ -e "$pgeon_file" ] || continue

    file=$(basename "$pgeon_file" .pgeon)
    twb_file="problems/twb/$file.twb"
    expected_status=$(expected_status_from_file "$pgeon_file")
    expected_result=$(expected_result_for_status "$expected_status")

    if [ ! -f "$twb_file" ]; then
        echo "$file,$expected_status,$expected_result,Error,,no,Missing,,no,no"
        continue
    fi

    pgeon_output=$(pgeon/_build/install/default/bin/pgeon --focused --log-level error "${PGEON_LOGIC:-pgeon/gore_3.txt}" "$pgeon_file" 2>&1)
    pgeon_status=$?
    pgeon_result=$(printf '%s\n' "$pgeon_output" | grep --only-matching -e "Open" -e "Close" | tail -n 1)
    pgeon_time=$(printf '%s\n' "$pgeon_output" | grep --only-matching -e "Time:[0-9.]*" | tail -n 1 | cut -d: -f2)
    if [ "$pgeon_status" -ne 0 ] || [ -z "$pgeon_result" ]; then
        pgeon_result="Error"
    fi
    if [ "$expected_result" != "Unknown" ] && [ "$pgeon_result" = "$expected_result" ]; then
        pgeon_ok="yes"
    else
        pgeon_ok="no"
    fi

    twb_output=$(tableau-workbench/library/s4.twb --noneg "$twb_file" 2>&1)
    twb_status=$?
    twb_result=$(printf '%s\n' "$twb_output" | grep --only-matching -e "Open" -e "Close" | tail -n 1)
    twb_time=$(printf '%s\n' "$twb_output" | grep --only-matching -e "Time:[0-9.]*" | tail -n 1 | cut -d: -f2)
    if [ "$twb_status" -ne 0 ] || [ -z "$twb_result" ]; then
        twb_result="Error"
    fi
    if [ "$expected_result" != "Unknown" ] && [ "$twb_result" = "$expected_result" ]; then
        twb_ok="yes"
    else
        twb_ok="no"
    fi

    if [ "$pgeon_result" = "$twb_result" ]; then
        same="yes"
    else
        same="no"
    fi

    echo "$file,$expected_status,$expected_result,$pgeon_result,$pgeon_time,$pgeon_ok,$twb_result,$twb_time,$twb_ok,$same"
done
