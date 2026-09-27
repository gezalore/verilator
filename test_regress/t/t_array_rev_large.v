// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Assignment between arrays with opposite range directions assigns elements
// left to right (IEEE 1800-2023 7.6), also for arrays above the
// --fslice-element-limit
module t;
  // verilator lint_off ASCRANGE
  int a[0:299];
  int m[0:1][0:299];
  // verilator lint_on ASCRANGE
  int b[299:0];
  int n[1:0][299:0];

  initial begin
    foreach (a[i]) a[i] = i;
    b = a;
    `checkd(b[299], 0);
    `checkd(b[0], 299);
    `checkd(b[100], 199);
    foreach (m[i, j]) m[i][j] = i * 1000 + j;
    n = m;
    `checkd(n[1][299], 0);
    `checkd(n[0][0], 1299);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
