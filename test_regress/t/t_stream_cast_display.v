// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Cast streaming concatenations used as display arguments
module t;
  typedef logic [7:0] byte_t;
  logic [7:0] a8;
  logic [15:0] a16;
  string s;

  initial begin
    a8 = 8'b1100_1010;
    a16 = 16'h1234;
    s = $sformatf("%h", 8'({<<{a8}}));
    `checks(s, "53");
    s = $sformatf("%h", 16'({<<4{a16}}));
    `checks(s, "4321");
    s = $sformatf("%h %h", a8, 8'({<<4{a8}}));
    `checks(s, "ca ac");
    s = $sformatf("%h", 16'({<<{a8}}));
    `checks(s, "0053");
    s = $sformatf("%h", byte_t'({<<{a8}}));
    `checks(s, "53");
    $display("%h", 8'({<<{a8}}));
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
