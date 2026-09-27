// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Cast of an integral value to string (IEEE 1800-2023 6.16)
module t;
  typedef string str_t;
  string s;
  int i;
  logic [39:0] w;
  logic [79:0] ww;

  initial begin
    i = 32'h41424344;
    s = type(s)'(i);
    `checks(s, "ABCD");
    `checkd(s.len(), 4);
    i = 32'h00004142;
    s = str_t'(i);
    `checks(s, "AB");
    `checkd(s.len(), 2);
    w = 40'h48656c6c6f;
    s = string'(w);
    `checks(s, "Hello");
    ww = 80'h48656c6c6f2c20576f72;
    s = type(s)'(ww);
    `checks(s, "Hello, Wor");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
