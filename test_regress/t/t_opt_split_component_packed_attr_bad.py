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

test.compile(verilator_flags2=['--stats', '-fno-var-split', '-Wno-fatal', '--no-skip-identical'],
             expect_filename=test.golden_filename)

test.execute()

# 'ok', and the copy of the primary input 'in' in module 't', which is not a primary input
test.file_grep(test.stats, r'Optimizations, SplitComponents, packed variables split\s+(\d+)', 2)

test.passes()
