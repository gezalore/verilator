#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# Copyright 2025 by Wilson Snyder. This program is free software; you
# can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License
# Version 2.0.
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

import vltest_bootstrap

test.scenarios('vlt')

test.lint(verilator_flags2=["--stats", "-Wno-fatal", "--no-skip-identical"],
          expect_filename=test.golden_filename)

test.file_grep(test.stats, r'DFG pre inline BreakCycles, true cycle\s+(\d+)', 1)
test.file_grep(test.stats, r'DFG post inline BreakCycles, true cycle\s+(\d+)', 1)
test.file_grep(test.stats, r'DFG scoped BreakCycles, true cycle\s+(\d+)', 1)

test.passes()
