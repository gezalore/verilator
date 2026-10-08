#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('simulator')
test.top_filename = 't/t_opt_slice.v'

test.compile(verilator_flags2=['--stats', '-fno-slice'])

test.execute()

test.file_grep(test.stats, r'Optimizations, Slice, array assignments\s+(\d+)', 0)
test.file_grep(test.stats, r'Optimizations, Slice, temporaries added for self assignments\s+(\d+)',
               1)
test.file_grep(test.stats, r'Optimizations, Slice, struct assignments\s+(\d+)', 0)

test.passes()
