#!/bin/bash
#
# This script tests the application with the original data files that has to
# be provided by the user.
#

usage()
{
    cat <<__EOF__
$0: [OPTIONS...] <data_dir>

Integration tests for woxar with original games data. These files must be
available in the <data_dir> directory.

Options:
    -h, --help  Show this help text and exit.
    -s, --stats Display stats for each test run.
__EOF__
}

cleanup()
{
    rm -fr "${scratch_dir}"
}

#############################################################################

set -euo pipefail

stats=false

temp=$(getopt -o hs --long help,stats -n integration-tests.bash -- "$@")
if [ $? -ne 0 ]; then
    exit 1
fi

eval set -- "${temp}"

while true; do
    case "$1" in
        -s | --stats)
            stats=true
            shift
            ;;
        -h | --help)
            usage
            exit 0
            ;;
        --)
            shift
            break
            ;;
        *)
            break
            ;;
    esac
done

if [ $# -eq 1 ]; then
    orig_data_dir="$1"
else
    echo 1>&2 "$0: ERROR: Must be called with the directory where World of Xeen is installed as the only argument"
    exit 1
fi

scratch_dir=

trap cleanup SIGHUP SIGINT SIGTERM
scratch_dir=$(mktemp -d)

readonly sha1_intro="3818b2b1b2326b86bd3cd9962d094910b85891c4"
readonly sha1_xeen="8b2cff57083c1d7c0a6e663637fe76cdae5e6cf8"
readonly sha1_dark="29665d274acedc80a7acb7fad3939fd78fd74846"

declare -a save_chunks_xeen="OUT0.SPL OUT1.SPL OUT2.SPL OUT3.SPL OUT4.SPL"
declare -a save_chunks_dark="OUT0.SPL OUT1.SPL OUT2.SPL OUT3.SPL OUT4.SPL OUT5.SPL"

if ${stats}; then
    start_tests="set -x"
    end_tests="set +x"
    tool="time"
else
    start_tests=
    end_tests=
    tool=
fi

# Run unit tests and build a release binary that we will use below
export RUST_BACKTRACE=1

cargo clippy --all-targets
cargo test
cargo build --release

for cc_base in "intro" "xeen" "dark"; do
    cc_file="${orig_data_dir}/${cc_base^^}.CC"
    dict_file="data/${cc_base}.fl"
    extracted_dir="${scratch_dir}/extracted"
    exe="target/release/woxar"
    rebuilt="${scratch_dir}/rebuilt.cc"
    rebuilt_stdout="${scratch_dir}/rebuilt-stdout.cc"

    rm -f "${rebuilt}" "${rebuilt_stdout}"
    rm -fr "${extracted_dir}"
    mkdir -p "${extracted_dir}"

    computed=$(sha1=; rest=; read sha1 rest < <(sha1sum "${cc_file}"); echo "${sha1}")
    expected_var="sha1_${cc_base}"
    expected="${!expected_var}"

    if [ "${computed}" != "${expected}" ]; then
        echo 1>&2 "$0: WARNING: Archive '${cc_file}' has a different hash than expected, this is not an original data file!"
    fi

    ${start_tests}

    # The provided archive can be a file or stdin ("-").
    # XXX: Write a test that make sure that the result are the same if you extract from a file or stdin.
    ${tool} ${exe} extract --archive "-" --root "${extracted_dir}" --dictionary "${dict_file}" < "${cc_file}"

    # The provided archive can be a file or stdout ("-").
    ${tool} ${exe} create --archive "${rebuilt}" --root "${extracted_dir}"
    ${tool} ${exe} create --archive "-" --root "${extracted_dir}" > "${rebuilt_stdout}"

    ${tool} ${exe} compare "${cc_file}" "${rebuilt}" "${rebuilt_stdout}"

    # Extract the default save from the archive. Since the save file is larger than 64K, it's
    # in multiple parts. Not all CC files have save files in them.
    var="save_chunks_${cc_base}"
    if ! [ -z ${!var+x} ]; then
        ext=
        for file in ${!var}; do
            ext+=" --file ${file}"
        done

        extracted_save="${scratch_dir}/${cc_base}_save.cc"
        ${tool} ${exe} extract --archive "${cc_file}" ${ext} > "${extracted_save}"

        # Build the same save file with files from a complete extraction earlier
        rebuilt_save="${scratch_dir}/${cc_base}_rebuilt_save.cc"
        for file in ${!var}; do
            cat "${extracted_dir}/${file}"
        done > "${rebuilt_save}"
        cmp "${extracted_save}" "${rebuilt_save}"

        # Extract the save file: these subarchive are not encrypted
        extracted_save_dir="${scratch_dir}/${cc_base}_save"
        mkdir -p "${extracted_save_dir}"
        ${tool} ${exe} extract --archive "${extracted_save}" --root "${extracted_save_dir}" --dictionary "data/save.fl" --disable-contents-crypt
    fi

    ${end_tests}
done
