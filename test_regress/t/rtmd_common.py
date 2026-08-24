# DESCRIPTION: Verilator: Verilog Test driver/expect definition
#
# This program is free software; you can redistribute it and/or modify it
# under the terms of either the GNU Lesser General Public License Version 3
# or the Perl Artistic License Version 2.0.
# SPDX-FileCopyrightText: 2026 Wilson Snyder
# SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0


def run(test):
    # Same design with different inlining. TODO: Check the trace output
    variant, = test.parse_name(r"t_rtmd_?([a-z]*)")

    test.top_filename = "t/t_rtmd.v"

    # For coverage of dump(), dumpJson() and V3EmitV
    flags = [
        "--trace-vcd", "--dumpi-tree 9", "--dumpi-tree-json 9", "--no-json-ids", "--debug-emitv"
    ]
    match variant:
        case "":
            pass
        case "noinl":
            flags.append("-fno-inline")
        case "flatten":
            flags.append("--flatten")
        case _:
            test.error(f"Unhandled test variant '{variant}'")

    test.compile(verilator_flags2=flags)

    test.passes()
