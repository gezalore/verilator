// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// An event control with a false 'iff' condition is not triggered at time zero
module t;
  logic [3:0] v = 0;
  logic en = 0;
  int cnt = 0;

  always @(v iff en) cnt++;

  initial begin
    #1 v = 1;
    #1 en = 1;
    #1 v = 2;
    #1 v = 3;
    #1;
    `checkd(cnt, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
