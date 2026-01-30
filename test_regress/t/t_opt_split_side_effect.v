// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top;

  logic clk = 1'b0;
  logic nclk;

  always #5 clk = ~clk;

  always_comb begin
    $display("SIDE EFFECT"); // Must print on every clk change, and at time 0
    nclk = ~clk;
  end

  int cyc = 0;
  always @(negedge nclk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
