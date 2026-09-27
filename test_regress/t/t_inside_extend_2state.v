// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// 'inside' with a two state variable member that is extended to a wider
// type, which is not four state
// verilator lint_off WIDTHEXPAND
module t;
  bit [7:0] e;
  bit [64:0] d;
  int a;
  int n;

  initial begin
    d = 65'h5;
    e = 8'hff;
    n = 0;
    a = 5;
    if ((e & a) inside {72'hff_ffff_ffff_ffff_fffe, [7:8], d}) n += 1;
    a = 8;
    if ((e & a) inside {72'hff_ffff_ffff_ffff_fffe, [7:8], d}) n += 2;
    a = 9;
    if ((e & a) inside {72'hff_ffff_ffff_ffff_fffe, [7:8], d}) n += 4;
    `checkd(n, 3);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
