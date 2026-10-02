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

test.compile(verilator_flags2=['--stats', '-fno-var-split'])

test.execute()

# Each variable expected to be split is marked in the source
nSplit = test.file_contents(test.top_filename).count('// Split')
test.file_grep(test.stats, r'Optimizations, SplitComponents, packed variables split\s+(\d+)',
               nSplit)
# The elements of 'pas'
test.file_grep(test.stats, r'Optimizations, SplitComponents, packed components split\s+(\d+)', 2)

test.passes()
