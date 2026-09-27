// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Unpacked array concatenation of arrays, above the --fslice-element-limit
module t;
  int b[150];
  int a[301];

  initial begin
    foreach (b[i]) b[i] = i + 1;
    a = {b, 7, b};
    `checkd(a[0], 1);
    `checkd(a[149], 150);
    `checkd(a[150], 7);
    `checkd(a[151], 1);
    `checkd(a[300], 150);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
