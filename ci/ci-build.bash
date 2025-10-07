#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI build job script
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
# Build verilator

CONFIGURE_ARGS="--enable-longtests --enable-ccwarn"
if [[ "$CI_DEV_ASAN" == 1 ]]; then
  CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-asan"
  CXX="$CXX -DVL_LEAK_CHECKS"
fi
if [[ "$CI_DEV_GCOV" == 1 ]]; then
  CONFIGURE_ARGS="$CONFIGURE_ARGS --enable-dev-gcov"
fi

autoconf
./configure $CONFIGURE_ARGS --prefix="$INSTALL_DIR"
ccache -z
make -j "$NPROC" -k
ccache -s
