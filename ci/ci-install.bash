#!/usr/bin/env bash
# DESCRIPTION: Verilator: CI dependency install script
#
# Copyright 2020 by Geza Lore. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
#
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

################################################################################
# This script runs in the 'install' phase of all jobs, in all stages. We try to
# minimize the time spent in this by selectively installing only the components
# required by the particular build stage.
################################################################################

set -e
set -x

cd $(dirname "$0")/..

readonly CI_STAGE=$1

# Avoid occasional cpan failures "Issued certificate has expired."
export PERL_LWP_SSL_VERIFY_HOSTNAME=0
echo "check_certificate = off" >> ~/.wgetrc

fatal() {
  echo "ERROR: $(basename "$0"): $1" >&2; exit 1;
}

MAKE=make

if [[ "$CI_RUNS_ON" == ubuntu-* ]]; then
  # Avoid slow "processing triggers for man db"
  echo 'set man-db/auto-update false' | sudo debconf-communicate >/dev/null
  sudo dpkg-reconfigure man-db
fi

if [[ "$CI_STAGE" == "build" ]]; then
  ##############################################################################
  # Dependencies of jobs in the 'build' stage, i.e.: packages required to
  # build Verilator

  if [[ "$CI_RUNS_ON" == ubuntu-* ]]; then
    APT_PACKAGES="ccache libfl-dev libsystemc libsystemc-dev mold bear help2man"
    # Some conflict of libunwind version on 22.04, can live without
    if [[ ! "$CI_RUNS_ON" =~ "ubuntu-22.04" ]]; then
      APT_PACKAGES="${APT_PACKAGES} libgoogle-perftools-dev"
    fi
    # Try twice, as sometimes the hosted runners fail to connect
    sudo apt update                  || sleep 30 && sudo apt update
    sudo apt install ${APT_PACKAGES} || sleep 30 && sudo apt install ${APT_PACKAGES}
  elif [[ "$CI_RUNS_ON" == macos-* ]]; then
    brew update
    brew install ccache perl gperftools autoconf bison flex help2man
  else
    fatal "Unknown os: '$CI_RUNS_ON'"
  fi
elif [[ "$CI_STAGE" == "test" ]]; then
  ##############################################################################
  # Dependencies of jobs in the 'test' stage, i.e.: packages required to
  # run the tests

  if [[ "$CI_RUNS_ON" = ubuntu-* ]]; then
    # python3-clang and moRequired for test_regress/t/t_dist_attributes.py
    APT_PACKAGES="ccache libfl-dev libsystemc libsystemc-dev mold bear gdb gtkwave lcov jq z3 python3-clang"
    # Try twice, as sometimes the hosted runners fail to connect
    sudo apt update                  || sleep 30 && sudo apt update
    sudo apt install ${APT_PACKAGES} || sleep 30 && sudo apt install ${APT_PACKAGES}
  elif [[ "$CI_RUNS_ON" = macos-* ]]; then
    brew update
    # brew cask install gtkwave # fst2vcd hangs at launch, so don't bother
    brew install ccache perl jq z3
  else
    fatal "Unknown os: '$CI_RUNS_ON'"
  fi
  # Install vcddiff
  TMP_DIR="$(mktemp -d)"
  git clone https://github.com/veripool/vcddiff "$TMP_DIR"
  git -C "${TMP_DIR}" checkout dca845020668887fd13498c772939814d9264fd5
  "$MAKE" -C "${TMP_DIR}"
  sudo cp "${TMP_DIR}/vcddiff" /usr/local/bin
  # Workaround -fsanitize=address crash
  sudo sysctl -w vm.mmap_rnd_bits=28
else
  ##############################################################################
  # Unknown stage
  fatal "Unknown stage: '$CI_STAGE'"
fi
