// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A cycle delay waits for the clocking block event, which is triggered after
// the clocking block inputs are sampled (IEEE 1800-2023 14.13)
module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;

  clocking cb @(posedge clk);
    input cnt;
  endclocking
  default clocking cb;

  initial begin
    @(cb);
    `checkd($time, 5);
    `checkd(cb.cnt, 0);
    ##1;
    `checkd($time, 15);
    `checkd(cb.cnt, 1);
    ##1;
    `checkd($time, 25);
    `checkd(cb.cnt, 2);
    ##2;
    `checkd($time, 45);
    `checkd(cb.cnt, 4);
    @(cb);
    `checkd($time, 55);
    `checkd(cb.cnt, 5);
    ##1;
    @(cb);
    `checkd($time, 75);
    `checkd(cb.cnt, 7);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
