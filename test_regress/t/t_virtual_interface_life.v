// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Interface variable written via a virtual interface between a direct write
// and a direct read
interface I;
  int s;
endinterface

module t;
  I u ();
  virtual I v;
  int a, b;

  initial begin
    v = u;
    u.s = 1;
    a = 0;
    b = 0;
    if (u.s == 1) a = 1;
    v.s = 5;
    if (u.s == 1) b = 1;
    `checkd(a, 1);
    `checkd(b, 0);
    u.s = 2;
    v.s = u.s + 10;
    `checkd(u.s, 12);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
