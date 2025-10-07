#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI test job script
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This is the main script executed in the 'script' phase by all jobs. We use a
# single script to keep the CI setting simple. We pass job parameters via
# environment variables using 'env' keys.
################################################################################

set -e
set -x

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

if [[ "$CI_RUNS_ON" == ubuntu-* ]]; then
  NPROC=$(nproc)
elif [[ "$CI_RUNS_ON" = macos-* ]]; then
  NPROC=$(sysctl -n hw.logicalcpu)
else
  fatal "Unknown os: '$CI_RUNS_ON'"
fi
NPROC=$(expr $NPROC '+' 1)

##############################################################################
# Run tests

export VERILATOR_TEST_NO_CONTRIBUTORS=1  # Separate workflow check
export VERILATOR_TEST_NO_LINT_PY=1  # Separate workflow check

if [[ "$CI_RUNS_ON" == macos-* ]]; then
  export VERILATOR_TEST_NO_GDB=1  # Pain to get GDB to work on macOS
fi

# Run sanitize on Ubuntu 24.04 only
sanitize=""
if [[ "$CI_RUNS_ON" == "ubuntu-24.04" ]]; then
  sanitize="--sanitize"
fi

# If testing that the installation is relocatable
TEST_REGRESS=test_regress
if [ "$CI_RELOC" == 1 ]; then
   make install
   mkdir -p "$RELOC_DIR"
   mv "$INSTALL_DIR" "$RELOC_DIR/relocated-install"
   export VERILATOR_ROOT="$RELOC_DIR/relocated-install/share/verilator"
   TEST_REGRESS="$RELOC_DIR/test_regress"
   mv test_regress "$TEST_REGRESS"
   NODIST="$RELOC_DIR/nodist"
   mv nodist "$NODIST"
   # Feeling brave?
   find . -delete
   ls -la .
fi

# Run the specified test
ccache -z
case $TESTS in
  dist-vlt-0)
    make -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean $sanitize" DRIVER_HASHSET=--hashset=0/4
    ;;
  dist-vlt-1)
    make -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean $sanitize" DRIVER_HASHSET=--hashset=1/4
    ;;
  dist-vlt-2)
    make -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean $sanitize" DRIVER_HASHSET=--hashset=2/4
    ;;
  dist-vlt-3)
    make -C "$TEST_REGRESS" SCENARIOS="--dist --vlt --driver-clean $sanitize" DRIVER_HASHSET=--hashset=3/4
    ;;
  vltmt-0)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=0/3
    ;;
  vltmt-1)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=1/3
    ;;
  vltmt-2)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt --driver-clean" DRIVER_HASHSET=--hashset=2/3
    ;;
  coverage-dist)
    make -C "$TEST_REGRESS" SCENARIOS="--dist"
    ;;
  coverage-vlt-0)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vlt-1)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vlt-2)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vlt-3)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vlt-4)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vlt-5)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vlt-6)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vlt-7)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vlt-8)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vlt-9)
    make -C "$TEST_REGRESS" SCENARIOS="--vlt" DRIVER_HASHSET=--hashset=9/10
    ;;
  coverage-vltmt-0)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=0/10
    ;;
  coverage-vltmt-1)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=1/10
    ;;
  coverage-vltmt-2)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=2/10
    ;;
  coverage-vltmt-3)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=3/10
    ;;
  coverage-vltmt-4)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=4/10
    ;;
  coverage-vltmt-5)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=5/10
    ;;
  coverage-vltmt-6)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=6/10
    ;;
  coverage-vltmt-7)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=7/10
    ;;
  coverage-vltmt-8)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=8/10
    ;;
  coverage-vltmt-9)
    make -C "$TEST_REGRESS" SCENARIOS="--vltmt" DRIVER_HASHSET=--hashset=9/10
    ;;
  *)
    fatal "Unknown test: $TESTS"
    ;;
esac

# To see load average (1 minute, 5 minute, 15 minute)
uptime
# ccache statistics
ccache -s
