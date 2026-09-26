// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// $monitor displays once at the end of a time step with changes, and
// $monitoron displays even without a change (IEEE 1800-2023 21.2.3)
module t;
  int a = 0;
  logic clk = 0;
  always @(posedge clk) a <= a + 10;

  initial begin
    $monitor("[%0t] a=%0d", $time, a);
    #1 a = 1;
    #0 a = 2;
    #1 clk = 1;
    a = 5;
    #1 $monitoroff;
    a = 6;
    #1 $monitoron;
    #1 $monitoron;
    #1 $monitoroff;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
