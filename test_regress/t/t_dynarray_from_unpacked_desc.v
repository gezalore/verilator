// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Assignment of an unpacked array with descending range to a dynamic array
// or queue assigns elements left to right (IEEE 1800-2023 7.6)
module t;
  int b[3:0];
  int d[];
  int q[$];

  initial begin
    b[3] = 1;
    b[2] = 2;
    b[1] = 3;
    b[0] = 4;
    d = b;
    `checkd(d[0], 1);
    `checkd(d[3], 4);
    q = b;
    `checkd(q[0], 1);
    `checkd(q[3], 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
