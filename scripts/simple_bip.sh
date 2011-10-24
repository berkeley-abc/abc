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

exec ${bin_dir}/abc -c "/simple_bip_aiger $*"
