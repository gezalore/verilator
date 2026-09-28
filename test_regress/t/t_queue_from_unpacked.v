// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Assignment of a fixed-size unpacked array to a queue (IEEE 1800-2023 7.6)
module t;
  int a[4];
  int q[$];

  initial begin
    a = '{1, 2, 3, 4};
    q = a;
    `checkd(q.size(), 4);
    `checkd(q[0], 1);
    `checkd(q[3], 4);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
