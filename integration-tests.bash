#!/bin/bash
#
# This script tests the application with the original data files that has to
# be provided by the user.
#

cleanup()
{
    rm -fr "${scratch_dir}"
}

#############################################################################

set -euo pipefail

export RUST_BACKTRACE=1

cargo test
cargo build --release

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

for cc_base in "intro" "xeen" "dark"; do
    cc_file="${orig_data_dir}/${cc_base^^}.CC"
    fl_file="data/${cc_base}.fl"
    extracted_dir="${scratch_dir}/extracted"
    exe="target/release/woxar"
    rebuilt="${scratch_dir}/rebuilt.cc"

    rm -f "${rebuilt}"
    rm -fr "${extracted_dir}"
    mkdir -p "${extracted_dir}"

    computed=$(sha1=; rest=; read sha1 rest < <(sha1sum "${cc_file}"); echo "${sha1}")
    expected_var="sha1_${cc_base}"
    expected="${!expected_var}"

    if [ "${computed}" != "${expected}" ]; then
        echo 1>&2 "$0: WARNING: Archive '${cc_file}' has a different hash than expected, this is not an original data file!"
    fi

    ${exe} extract --archive "${cc_file}" --root "${extracted_dir}" --fl "${fl_file}"
    ${exe} create --archive "${rebuilt}" --root "${extracted_dir}"
    ${exe} compare "${cc_file}" "${rebuilt}"
done
