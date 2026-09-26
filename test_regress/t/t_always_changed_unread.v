// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// An always block with a sensitivity list is triggered by changes of the listed
// signals, even if it does not read them
module t;
  logic clk = 0;
  logic [7:0] a = 0;
  logic [7:0] b = 0;
  logic flag = 0;
  logic flag2 = 0;
  int seen = 0;
  int seen2 = 0;

  always @(a) flag = 1;
  always @(a or b) flag2 = 1;

  always @(posedge clk) begin
    if (flag) seen++;
    if (flag2) seen2++;
    flag = 0;
    flag2 = 0;
  end

  initial begin
    repeat (4) begin
      #1 a = a + 1;
      #1 clk = 1;
      #1 clk = 0;
    end
    repeat (3) begin
      #1 b = b + 1;
      #1 clk = 1;
      #1 clk = 0;
    end
    `checkd(seen, 4);
    `checkd(seen2, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
