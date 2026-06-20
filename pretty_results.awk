BEGIN {
    FS = ","
    color = (ENVIRON["COLOR"] == "yes")
    green = color ? sprintf("%c[32m", 27) : ""
    red = color ? sprintf("%c[31m", 27) : ""
    reset = color ? sprintf("%c[0m", 27) : ""

    printf "%-12s %-12s %-18s %-18s %-8s\n", "problem", "expected", "pgeon", "twb", "same"
}

NR == 1 {
    next
}

{
    file = $1
    expected = $3
    pgeon_result = $4
    pgeon_time = $5
    pgeon_ok = $6
    twb_result = $7
    twb_time = $8
    twb_ok = $9
    same = $10

    printf "%-12s %-12s %-18s %-18s %-8s\n", \
        file, \
        expected, \
        formatted_result(pgeon_result, pgeon_time, pgeon_ok), \
        formatted_result(twb_result, twb_time, twb_ok), \
        same

    total += 1
    if (pgeon_ok == "yes") {
        pgeon_pass += 1
    }
    if (twb_ok == "yes") {
        twb_pass += 1
    }
    if (same == "yes") {
        same_pass += 1
    }
}

END {
    if (total == 0) {
        print "No benchmark results found."
        exit 1
    }

    printf "\n"
    printf "pgeon: %d/%d match expected\n", pgeon_pass, total
    printf "twb:   %d/%d match expected\n", twb_pass, total
    printf "same:  %d/%d pgeon/twb agree\n", same_pass, total
}

function formatted_result(result, time, ok, label) {
    label = result
    if (time != "") {
        label = label " (" time "s)"
    }

    if (ok == "yes") {
        return green label reset
    }
    return red label reset
}
