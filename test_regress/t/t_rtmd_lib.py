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

# A --lib-create library used by a traced model. TODO: Check the trace output
secret_dir = test.obj_dir + "/secret"
secret_prefix = "Vt_rtmd_lib_secret"
test.mkdir_ok(secret_dir)

test.run(logfile=secret_dir + "/vlt_compile.log",
         cmd=[
             os.environ["VERILATOR_ROOT"] + "/bin/verilator", "--cc", "--no-timing",
             "--trace-vcd", "--prefix", secret_prefix, "-Mdir",
             secret_dir, "--lib-create", "secret", "t/t_lib_prot_secret.v"
         ],
         verilator_run=True)

test.top_filename = secret_dir + "/secret.sv"

test.compile(verilator_flags2=["--no-timing", "--trace-vcd"],
             verilator_make_gmake=False,
             make_top_shell=False,
             make_main=False)

test.passes()
