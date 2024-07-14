#!/bin/bash
set -o pipefail -o noclobber -o nounset

# Defaults
SATISFIABLE=10
UNSATISFIABLE=20
DIFFICULTY=easy
TIMEOUT=30s
PARAMS_ARG=
LABEL_ARG=

# Process any overrides from command-line flags.
while getopts ":d:l:p:t:" opt; do
    case $opt in
        d)
            DIFFICULTY="${OPTARG}"
            ;;
        l)
            LABEL_ARG="${OPTARG}"
            ;;
        p)
            PARAMS_ARG="-p${OPTARG}"
            ;;
        t)
            TIMEOUT="${OPTARG}"
            ;;
        \?)
            echo "Invalid option: -$OPTARG" >&2
            exit 1
            ;;
        :)
            echo "Option -$OPTARG requires an argument." >&2
            exit 1
            ;;
    esac
done

BINARY="./millisat.py"
echo "Testing binary ${BINARY}"

LABEL="label:${DIFFICULTY}"
NSUCCESS=0
NFAILURE=0
NTIMEOUT=0

start=`date +%s`

if [[ satisfiable == "${LABEL_ARG}"* ]]; then
    echo "Testing label:satisfiable, ${LABEL}:"
    for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:satisfiable'); do
        printf "${filename} "
        output="$(timeout ${TIMEOUT} ${BINARY} ${PARAMS_ARG} ${filename} 1>/dev/null 2>&1)"
        result="$?"
        if [ "$result" -eq "124" ]; then
            printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
            ((NTIMEOUT++))
        elif [ "$result" -eq "$SATISFIABLE" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        else
            printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
            ((NFAILURE++))
        fi
    done
    echo ""
fi

if [[ unsatisfiable == "${LABEL_ARG}"* ]]; then
    echo "Testing label:unsatisfiable, ${LABEL}:"
    for filename in $(grep -l "${LABEL}" test/*.cnf | xargs grep -l 'label:unsatisfiable'); do
        printf "${filename} "
        output="$(timeout ${TIMEOUT} ${BINARY} ${PARAMS_ARG} ${filename} 1>/dev/null 2>&1)"
        result="$?"
        if [ "$result" -eq "124" ]; then
            printf $'\u001b[33m\u23f1\u001b[0m\n' # Yellow stopwatch
            ((NTIMEOUT++))
        elif [ "$result" -eq "$UNSATISFIABLE" ]; then
            printf $'\u001b[32m\u2714\u001b[0m\n' # Green check
            ((NSUCCESS++))
        else
            printf $'\u001b[31m\u274c\u001b[0m\n' # Red X
            ((NFAILURE++))
        fi
    done
    echo ""
fi

end=`date +%s`
runtime=$((end-start))

echo "${NSUCCESS} succeeded, ${NFAILURE} failed, ${NTIMEOUT} timed out in ${runtime} seconds."
