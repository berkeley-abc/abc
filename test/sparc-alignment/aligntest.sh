#!/bin/sh

# Run test lifted from yosys demonstrating bus error on sparc64.

PATH=`pwd`/../..:$PATH
export PATH

cd $(dirname $0)

abc -s -f abc.script
