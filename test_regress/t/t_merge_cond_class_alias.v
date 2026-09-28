// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Class members written via one handle and read via another handle to the
// same object, or by a shallow copy, must not be reordered, nor conditions on
// them merged
class C;
  int x;
  bit flag;
endclass

module t;
  C h0, h2, h3;
  int a, b, c1, i1;

  initial begin
    h0 = new;
    h2 = $test$plusargs("never") ? null : h0;
    h0.x = 1;
    h0.flag = 1;
    a = 0;
    b = 0;
    c1 = (h2 != null) ? 3 : 4;
    if (h0 != null) h0.x = 5;
    i1 = (h2 != null) ? h2.x : 0;
    `checkd(c1, 3);
    `checkd(i1, 5);
    if (h0.flag) a = 1;
    h2.flag = 0;
    if (h0.flag) b = 1;
    `checkd(a, 1);
    `checkd(b, 0);
    a = 0;
    if (h2 != null) h2.x = 7;
    if (h0 != null) h3 = new h0;
    if (h2 != null) a = 3;
    `checkd(a, 3);
    `checkd(h3.x, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
