#!/usr/bin/env python3
# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0
import vltest_bootstrap

test.scenarios('vlt')

# The library omits its top module from %m, the instances of 'sub' are still combined
test.vm_prefix = "Vlib_lib"
test.compile(make_main=False,
             threads=1,
             verilator_make_gmake=False,
             verilator_flags2=["--stats", "--lib-create", "lib", "--top-module", "lib"])
test.run(logfile=test.obj_dir + "/Vlib_lib_make.log",
         cmd=[os.environ["MAKE"], "-C", test.obj_dir, "-f", "Vlib_lib.mk", "liblib.a"])
test.file_grep(test.obj_dir + "/Vlib_lib__stats.txt", r'Optimizations, Combined CFuncs\s+(\d+)', 4)

test.vm_prefix = "Vt_display_m_combine_lib"
test.main_filename = test.obj_dir + "/" + test.vm_prefix + "__main.cpp"
test.compile(verilator_flags2=["--top-module", "t", "+define+USE_LIB", test.obj_dir + "/lib.sv", "liblib.a"])

test.execute(expect_filename=test.golden_filename)

test.passes()
