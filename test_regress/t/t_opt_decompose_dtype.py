#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt_all')

test.compile(timing_loop=True, verilator_flags2=['--stats', '-fno-var-split', '-fno-dfg', '--timing'])

test.execute()

test.file_grep(test.stats, r'Optimizations, Decompose, unpacked variables split\s+(\d+)', 2)

test.passes()
