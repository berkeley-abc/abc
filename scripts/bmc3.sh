#!/bin/sh

abc_root()
{
    cwd="$(pwd)"
    cd $(dirname "$1")
    echo $(dirname "$(pwd)")
    cd "${cwd}"
}

abc_dir=$(abc_root "$0")
bin_dir="${abc_dir}"/bin
aig_file="$1"

exec "${bin_dir}"/abc -c "/rf ${aig_file} ; /pushredirect ; /pushdtemp ; bmc3 ; /popdtemp ; /popredirect ; /print_aiger_result"
